package oxide

import Substitution._
import Syntax._

object TypeChecker {
  def check(expr: Expression): (Type, Effects) = TypeChecker(Map(), Map(), Map(), Map()).check(expr)
  def checkPost(expr: Expression): (Type, RegionContext) = {
    val (typ, eff) = TypeChecker.check(expr)
    (typ, Effects.applyToRegionCtx(eff, Map().asInstanceOf[RegionContext]))
  }
}

case class TypeChecker(
  sigma: GlobalContext, delta: TyVarContext, rho: RegionContext, gamma: VarContext
) {
  private def mutaToFrac(mu: MutabilityQuantifier): Fraction = mu match {
    case QImm => FZeta
    case QMut => F1
    case AbsMuta => throw Errors.Unreachable
  }

  // TODO: implement more metadata computations
  private def makeMeta(typ: Type): Metadata = typ match {
    case TBase(_) => MNone
    case _ => ???
  }

  def checkThreaded(exprs: Expressions): Seq[(Type, Effects)] =
    exprs.foldLeft[(_, Seq[(Type, Effects)])]((this, Seq()))({
      case ((TypeChecker(sigmaC, deltaC, rhoC, gammaC), res), expr) => {
        val effectsSoFar = res.map(_._2).foldLeft[Effects](Seq())(Effects.compose)
        val newChecker = TypeChecker(
          sigmaC, deltaC,
          Effects.applyToRegionCtx(effectsSoFar, rhoC),
          Effects.applyToVarCtx(effectsSoFar, gammaC),
        )
        (newChecker, res :+ newChecker.check(expr))
      }
    })._2

  def check(expr: Expression): (Type, Effects) = expr match {
    // T-AllocPrim
    case EAlloc(rgn, inner@EPrim(_)) => if (rho.contains(rgn) == false) {
      val (typ, eff) = this.check(inner)
      assert(eff.isEmpty)
      (TRef(rgn, QMut, typ), Seq(EffNewRegion(rgn, typ, F1, Map())))
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    // T-AllocTup
    case EAlloc(rgn, EProd(exprs)) => if (rho.contains(rgn) == false) {
      val (types, effects) = this.checkThreaded(exprs).unzip
      assert(types.forall(_.isInstanceOf[TRef]))
      val innerTypes = types.map {
        case TRef(_, QMut, typ) => typ
        case TRef(rgn, QImm, _) => throw Errors.InsufficientCapability(F1, FZeta, rgn)
        case _ => throw Errors.Unreachable
      }
      val subs = types.zipWithIndex.map {
        case (TRef(rgn, muta, typ), n) => PProj(n).asInstanceOf[ImmediatePath] -> rgn
        case _ => throw Errors.Unreachable
      }.toMap
      (TRef(rgn, QMut, TProd(innerTypes)),
       Effects.compose(
         effects.foldLeft[Effects](Seq())(Effects.compose),
         Seq(EffNewRegion(rgn, TProd(innerTypes), F1, subs))
       ))
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    // T-AllocClosure
    case EAlloc(rgn, EClosure(quantifiers, params, body)) => if (rho.contains(rgn) == false) {
      // seq[r] ∩ seq[ς]
      val newlyQuantifiedRegions = params.map {
        case (_, TRef(rgn, _, _)) => rgn
      } intersect {
        quantifiers.filter(q => q._2 == KRegion).map(_._1)
      }

      // seq[r -> (t, muta-to-frac(mu), mk-meta(t))]
      val quantifiedRegionBindings = params.filter {
        case (_, TRef(rgn, _, _)) => newlyQuantifiedRegions.contains(rgn)
      } map {
        case (_, TRef(rgn, muta, typ)) => rgn -> (typ, mutaToFrac(muta), makeMeta(typ))
      }

      // seq[x -> r]
      val argumentBindings = params.map { case (id, TRef(rgn, _, _)) => id -> rgn }

      val (retTyp, funEff) = TypeChecker(
        sigma, delta ++ quantifiers, rho ++ quantifiedRegionBindings, gamma ++ argumentBindings
      ).check(body)
      // FIXME: variable capture in closures

      val funTyp = TFun(quantifiers, params.map(_._2), funEff, retTyp)
      (TRef(rgn, QMut, funTyp), Seq(EffNewRegion(rgn, funTyp, F1, Map())))
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    // T-Copy
    case ECopy(rgn, expr) => this.check(expr) match {
      case (TRef(src, mu, typ@TBase(_)), eff) =>
        if (rho.contains(rgn) == false) {
          (TRef(rgn, QMut, typ), Effects.compose(eff, Seq(EffNewRegion(rgn, typ, F1, Map()))))
        } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case (TRef(_, _, typ), _) => throw Errors.TypeError(
        expected = TBase(AbsBaseType),
        found = typ
      )
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-Borrow
    case EBorrow(rgn, muta, id, pi) => gamma.get(id).flatMap(rgnId => {
      val (typPi, rgnPi, rhoPrime) = AdditionalJudgments.RegionValidAlongPath(rho)(muta, pi, rgnId)
      rhoPrime.get(rgnPi).map { case (typ, frac, mt) => (rgnPi, (typ, frac.norm, mt), rhoPrime) }
    }) match {
      case Some((rgnPi, (_, FNum(0), _), _)) =>
        throw Errors.InsufficientCapability(F1, FNum(0), rgnPi)
      case Some((rgnPi, (typ, frac, meta), rhoPrime)) => if (rhoPrime.contains(rgn) == false) {
        AdditionalJudgments.RegionWellFormed(rhoPrime)(muta, rgnPi)
        (TRef(rgn, muta, typ), Seq(EffBorrow(muta, rgnPi, rgn)))
      } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case None => ???
    }

    case EDeref(expr) => this.check(expr) match {
      case (TRef(rgn, mu, typ), eff) => (typ, eff)
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-Drop, T-FreeImmediate, T-Free
    case EDrop(rgn) => rho.get(rgn) match {
      // T-Drop
      case Some((typ, frac, MAlias(src))) => rho.get(src) match {
        case Some((srcTyp, srcFrac, srcMeta)) => (TBase(TUnit), Seq(EffDeleteRegion(rgn)))
        case None => ???
      }

      // T-FreeImmediate
      case Some((typ, FNum(1), MNone)) => (TBase(TUnit), Seq(EffDeleteRegion(rgn)))

      // T-Free
      case Some((typ, FNum(1), MAggregate(paths))) => paths.find {
        case (_, vRgn) => rho.contains(vRgn)
      } match {
        case Some((path, unfreedRgn)) => throw Errors.BadAggregateFree(rgn, path, unfreedRgn)
        case None => (TBase(TUnit), Seq(EffDeleteRegion(rgn)))
      }

      case Some((typ, frac, _)) => throw Errors.InsufficientCapability(F1, frac.norm, rgn)

      case None => ???
    }

      // T-VarImm, T-VarMut
    case EVar(id) => gamma.get(id) match {
      case Some(rgn) => rho.get(rgn) match {
        // T-VarMut
        case Some((typ, FNum(1), _)) => (TRef(rgn, QMut, typ), Seq())
        // T-VarImm
        case Some((typ, frac, _)) => if (frac != F0)
                                       (TRef(rgn, QImm, typ), Seq())
                                     else throw Errors.InsufficientCapability(FZeta, frac, rgn)
        case None => throw Errors.UnboundRegion(rgn)
      }
      case None => throw Errors.UnboundIdentifier(id)
    }

    // T-True, T-False, T-u32, T-Unit
    case EPrim(ETrue)
       | EPrim(EFalse) => (TBase(TBool), Seq())
    case EPrim(ENum(n)) => (TBase(Tu32), Seq()) // FIXME(awe): fix bounds on n
    case EPrim(EUnit) => (TBase(TUnit), Seq())

    // T-LetImm
    case ELet(QImm, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, mu, ty1), eff1) => {
        val gamma1 = Effects.applyToVarCtx(eff1, gamma)
        if (gamma1.values.find(_ == r1).nonEmpty)
          throw Errors.RegionAlreadyBound(r1, id, gamma1)

        val (ty2, eff2) = TypeChecker(
          sigma, delta, Effects.applyToRegionCtx(eff1, rho), gamma1 + (id -> r1)
        ).check(e2)
        // assert(rho2.contains(r1) == false)
        (ty2, Effects.compose(eff1, eff2))
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-LetMut
    case ELet(QMut, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, QMut, ty1), eff1) => {
        val gamma1 = Effects.applyToVarCtx(eff1, gamma)
        if (gamma1.values.find(_ == r1).nonEmpty)
          throw Errors.RegionAlreadyBound(r1, id, gamma1)

        val (ty2, eff2) = TypeChecker(
          sigma, delta, Effects.applyToRegionCtx(eff1, rho), gamma1 + (id -> r1)
        ).check(e2)
        // assert(rho2.contains(r1) == false)
        (ty2, Effects.compose(eff1, eff2))
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-Assign
    case EAssign(id, path, expr) => this.check(expr) match {
      case (TRef(rgn, QMut, typ), eff) => {
        if (gamma.get(id).isEmpty)
          throw Errors.UnboundIdentifier(id)
        (TBase(TUnit), Effects.compose(eff, Seq(EffUpdate(gamma(id), path, rgn))))
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, QMut, AbsType),
        found = typ
      )
    }

    // T-App
    case EApp(fun, tyargs, args) => this.check(fun) match {
      case (TRef(_, _, TFun(typarams, params, funEff, retTyp)), effF) => {
        // val (typs, TypeChecker(_, _, rhoPrime, gammaPrime)) =
        //   TypeChecker(sigma, delta, rhoF, gammaF).checkThread(args)

        // val subst = TypeSubstitution(typarams.map(_._1).zip(tyargs).toMap)

        // for (typ <- typs; param <- params)
        //   if (typ != subst(param)) throw Errors.TypeError(expected = subst(param), found = typ)
        // (retTyp, subst inRegionContext rhoPrime, subst inVarContext gammaPrime)
        ???
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, TFun(Seq(), Seq(), Seq(), AbsType)),
        found = typ
      )
    }

    // T-Seq
    case ESeq(e1, e2) => this.check(e1) match {
      case (TBase(TUnit), eff1) => {
        val (ty2, eff2) =
          TypeChecker(
            sigma, delta, Effects.applyToRegionCtx(eff1, rho), Effects.applyToVarCtx(eff1, gamma)
          ).check(e2)
        (ty2, Effects.compose(eff1, eff2))
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TBase(TUnit),
        found = typ
      )
    }

    // T-If
    case EIf(pred, cons, alt) => this.check(pred) match {
      case (TRef(_, _, TBase(TBool)), eff1) => {
        val (rho1, gamma1) = (Effects.applyToRegionCtx(eff1, rho), Effects.applyToVarCtx(eff1, gamma))
        (TypeChecker(sigma, delta, rho1, gamma1).check(cons),
         TypeChecker(sigma, delta, rho1, gamma1).check(alt)) match {
          case ((typ2, eff2), (typ3, eff3)) => {
            assert(typ2 == typ3)
            // FIXME: join the two environments somehow? or maybe that's not necessary anymore?
            (typ2, Effects.compose(eff1, eff2))
          }
        }
      }
      case (typ, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, TBase(TBool)),
        found = typ
      )
    }

    case _ => ???
  }
}

object AdditionalJudgments {
  case class RegionValidAlongPath(rho: RegionContext) {
    def apply(
      mu: MutabilityQuantifier, pi: Path, rgn: Region
    ): (Type, Region, RegionContext) = (rho.get(rgn), pi) match {
      // P-EpsilonPath
      case (Some((typ, frac, meta)), Seq()) => (mu, frac.norm) match {
        case (QMut, FNum(1)) => (typ, rgn, rho)
        case (QMut, frac) => throw Errors.InsufficientCapability(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.InsufficientCapability(FZeta, F0, rgn)
        case (QImm, _) => (typ, rgn, rho)
        case (AbsMuta, _) => throw Errors.Unreachable
      }

      // implied error condition
      case (Some((_, _, MNone)), immPath :: _) =>
        throw Errors.UnexpectedMetadata(MNone, MAggregate(Map(immPath -> AbsRegion)), rgn)

      // P-AliasPath
      case (Some((_, frac, MAlias(src))), immPath :: _) => (mu, frac.norm) match {
        // FIXME: the alias rule is problematic because we know the recursive call will always fail
        case (QMut, FNum(1)) => this(mu, pi, src)
        case (QMut, frac) => throw Errors.InsufficientCapability(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.InsufficientCapability(FZeta, F0, rgn)
        case (QImm, _) => this(mu, pi, src)
        case (AbsMuta, _) => throw Errors.Unreachable
      }

      // P-FieldPath and P-FieldPathAbs
      case (Some((typ, frac, MAggregate(piMap))), immPath :: path) => (mu, frac.norm) match {
        case (QMut, FNum(1)) => rgn match {
          // P-FieldPathAbs
          case RAbstract => ???
          case AbsRegion => throw Errors.Unreachable
          // P-FieldPath
          case _ => this(mu, path, piMap(immPath))
        }
        case (QMut, frac) => throw Errors.InsufficientCapability(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.InsufficientCapability(FZeta, F0, rgn)
        case (QImm, _) => rgn match {
          // P-FieldPathAbs
          case RAbstract => ???
          case AbsRegion => throw Errors.Unreachable
          // P-FieldPath
          case _ => this(mu, path, piMap(immPath))
        }
        case (AbsMuta, _) => throw Errors.Unreachable
      }

      case (None, _) => throw Errors.UnboundRegion(rgn)
    }
  }

  case class RegionWellFormed(rho: RegionContext) {
    def apply(mu: MutabilityQuantifier, rgn: Region): Unit = (mu, rho.get(rgn)) match {
      // WF-ImmEpsilonRegion
      case (QImm, Some((typ, frac, MNone))) =>
        if (frac.norm == F0) throw Errors.InsufficientCapability(FZeta, frac.norm, rgn)

      // WF-MutEpsilonRegion
      case (QMut, Some((typ, frac, MNone))) =>
        if (frac.norm != F1) throw Errors.InsufficientCapability(F1, frac.norm, rgn)

      // WF-ImmAliasRegion
      case (QImm, Some((typ, frac, MAlias(_)))) =>
        if (frac.norm == F0) throw Errors.InsufficientCapability(FZeta, frac.norm, rgn)

      // WF-MutAliasRegion
      case (QMut, Some((typ, frac, MAlias(_)))) =>
        if (frac.norm != F1) throw Errors.InsufficientCapability(F1, frac.norm, rgn)

      // WF-ImmAggregateRegion
      case (QImm, Some((typ, frac, MAggregate(paths)))) => {
        if (frac.norm == F0) throw Errors.InsufficientCapability(FZeta, frac.norm, rgn)
        for ((_, innerRgn) <- paths) {
          this(mu, innerRgn)
        }
      }

      // WF-MutAggregateRegion
      case (QMut, Some((typ, frac, MAggregate(paths)))) => {
        if (frac.norm != F1) throw Errors.InsufficientCapability(F1, frac.norm, rgn)
        for ((_, innerRgn) <- paths) {
          this(mu, innerRgn)
        }
      }

      case (AbsMuta, _) => throw Errors.Unreachable
      case (_, None) => throw Errors.UnboundRegion(rgn)
    }
  }
}
