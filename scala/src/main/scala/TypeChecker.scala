package oxide

import Substitution._
import Syntax._

case class TypeChecker(
  sigma: GlobalContext, delta: TyVarContext, rho: RegionContext, gamma: VarContext
) {
  def checkThread(expr: Expression): (Type, TypeChecker) = this.check(expr) match {
    case (typ, rhoPrime, gammaPrime) => (typ, TypeChecker(sigma, delta, rhoPrime, gammaPrime))
  }

  def checkThread(exprs: Expressions): (Seq[Type], TypeChecker) =
    exprs.foldLeft[(Seq[Type], TypeChecker)]((Seq(), this)) {
      case ((acc, checker), expr) => {
        val (typ, checkerPrime) = checker.checkThread(expr)
        (acc :+ typ, checkerPrime)
      }
    }

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

  def check(expr: Expression): (Type, RegionContext, VarContext) = expr match {
    // T-AllocPrim
    case EAlloc(rgn, inner@EPrim(_)) => if (rho.contains(rgn) == false) {
      val (typ, rhoPrime, gammaPrime) = this.check(inner)
      assert(rhoPrime == rho)
      assert(gammaPrime == gamma)
      (TRef(rgn, QMut, typ), rho + (rgn -> (typ, F1, MNone)), gamma)
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    // T-AllocTup
    case EAlloc(rgn, EProd(exprs)) => if (rho.contains(rgn) == false) {
      val (typs, TypeChecker(_, _, rhoPrime, gammaPrime)) = this.checkThread(exprs)
      val meta = MAggregate(typs.zipWithIndex.map {
        case (TRef(rgn, _, _), idx) => PProj(idx) -> rgn
        case (typ, _) => throw Errors.TypeError(
          expected = TRef(AbsRegion, AbsMuta, AbsType),
          found = typ
        )
      }.toMap)
      val innerTyps = typs.map {
        case TRef(_, _, typ) => typ
        case _ => throw Errors.Unreachable
      }
      (TRef(rgn, QMut, TProd(typs)), rhoPrime + (rgn -> (TProd(innerTyps), F1, meta)), gammaPrime)
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

      val (retTyp, rhoPrime, gammaPrime) = TypeChecker(
        sigma, delta ++ quantifiers, rho ++ quantifiedRegionBindings, gamma ++ argumentBindings
      ).check(body)

      val funTyp = TFun(quantifiers, params.map(_._2), retTyp)
      (TRef(rgn, QMut, funTyp), rhoPrime + (rgn -> (funTyp, F1, MNone)), gammaPrime)
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    // T-Copy
    case ECopy(rgn, expr) => this.check(expr) match {
      case (TRef(src, mu, typ@TBase(_)), rhoPrime, gammaPrime) =>
        if (rhoPrime.contains(rgn) == false) {
          (TRef(rgn, QMut, typ), rhoPrime + (rgn -> (typ, F1, MNone)), gammaPrime)
        } else throw Errors.RegionAlreadyInUse(rgn, rhoPrime)
      case (TRef(_, _, typ), _, _) => throw Errors.TypeError(
        expected = TBase(AbsBaseType),
        found = typ
      )
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-BorrowImm
    case EBorrow(rgn, QImm, id, pi) => gamma.get(id).flatMap(rgnId => {
      val (typPi, rgnPi, rhoPrime) = AdditionalJudgments.RegionValidAlongPath(rho)(QImm, pi, rgnId)
      rhoPrime.get(rgnPi).map { case (typ, frac, mt) => (rgnPi, (typ, frac.norm, mt), rhoPrime) }
    }) match {
      case Some((rgnPi, (_, FNum(0), _), _)) =>
        throw Errors.InsufficientCapability(F1, FNum(0), rgnPi)
      case Some((rgnPi, (typ, frac, meta), rhoPrime)) => if (rhoPrime.contains(rgn) == false) {
        AdditionalJudgments.RegionWellFormed(rhoPrime)(QImm, rgnPi)
        (TRef(rgn, QMut, typ),
         rhoPrime ++ Seq(rgnPi -> (typ, FDiv(frac, FNum(2)).norm, meta),
                         rgn -> ((typ, FDiv(frac, FNum(2)).norm, MAlias(rgnPi)))),
         gamma)
      } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case None => ???
    }

    // T-BorrowMut
    case EBorrow(rgn, QMut, id, pi) => gamma.get(id).flatMap(rgnId => {
      val (typPi, rgnPi, rhoPrime) = AdditionalJudgments.RegionValidAlongPath(rho)(QMut, pi, rgnId)
      rhoPrime.get(rgnPi).map { case (typ, frac, mt) => (rgnPi, (typ, frac.norm, mt), rhoPrime) }
    }) match {
      case Some((rgnPi, (typ, FNum(1), meta), rhoPrime)) => if (rhoPrime.contains(rgn) == false) {
        AdditionalJudgments.RegionWellFormed(rhoPrime)(QMut, rgnPi)
        (TRef(rgn, QMut, typ),
         rhoPrime ++ Seq(rgnPi -> (typ, F0, meta), rgn -> ((typ, F1, MAlias(rgnPi)))),
         gamma)
      } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case Some((rgnPi, (_, frac, _), _)) => throw Errors.InsufficientCapability(F1, frac, rgnPi)
      case None => ???
    }

    case EDeref(expr) => this.check(expr) match {
      case (TRef(rgn, mu, typ), rhoPrime, gammaPrime) => (typ, rhoPrime, gammaPrime)
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-Drop, T-FreeImmediate, T-Free
    case EDrop(rgn) => rho.get(rgn) match {
      // T-Drop
      case Some((typ, frac, MAlias(src))) => rho.get(src) match {
        case Some((srcTyp, srcFrac, srcMeta)) => (
          TBase(TUnit),
          rho - rgn + (src -> (srcTyp, FAdd(frac, srcFrac).norm, srcMeta)),
          gamma.filter {
            case (_, vRgn) => vRgn != rgn
          }
        )
        case None => ???
      }

      // T-FreeImmediate
      case Some((typ, FNum(1), MNone)) => (
        TBase(TUnit), rho - rgn,
        gamma.filter {
          case (_, vRgn) => vRgn != rgn
        }
      )

      // T-Free
      case Some((typ, FNum(1), MAggregate(paths))) => paths.find {
        case (_, vRgn) => rho.contains(vRgn)
      } match {
        case Some((path, unfreedRgn)) => throw Errors.BadAggregateFree(rgn, path, unfreedRgn)
        case None => (
          TBase(TUnit), rho - rgn,
          gamma.filter {
            case (_, vRgn) => vRgn != rgn
          }
        )
      }

      case Some((typ, frac, _)) => throw Errors.InsufficientCapability(F1, frac.norm, rgn)

      case None => ???
    }

    // T-True, T-False, T-u32, T-Unit
    case EPrim(ETrue)
       | EPrim(EFalse) => (TBase(TBool), rho, gamma)
    case EPrim(ENum(n)) => (TBase(Tu32), rho, gamma) // FIXME(awe): fix bounds on n
    case EPrim(EUnit) => (TBase(TUnit), rho, gamma)

    // T-LetImm
    case ELet(QImm, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, mu, ty1), rho1, gamma1) => {
        val (ty2, rho2, gamma2) = TypeChecker(
          sigma, delta, rho1, gamma1 + (id -> r1)
        ).check(e2)
        // assert(rho2.contains(r1) == false)
        (ty2, rho2, gamma2)
      }
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    // T-LetMut
    case ELet(QMut, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, QMut, ty1), rho1, gamma1) => {
        val (ty2, rho2, gamma2) = TypeChecker(
          sigma, delta, rho1, gamma1 + (id -> r1)
        ).check(e2)
        // assert(rho2.contains(r1) == false)
        (ty2, rho2, gamma2)
      }
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, AbsType),
        found = typ
      )
    }

    case EAssign(id, path :+ lastPath, expr) => gamma.get(id) match {
      case Some(rgn) => AdditionalJudgments.RegionValidAlongPath(rho)(QMut, path, rgn) match {
        case (typPi, rgnPi, rhoPi) => {
          AdditionalJudgments.RegionWellFormed(rhoPi)(QMut, rgnPi)
          TypeChecker(sigma, delta, rhoPi, gamma).check(expr) match {
            case (TRef(rgn, QMut, typ), rhoPrime, gammaPrime) => {
              val (typPi, FNum(1), MAggregate(map)) = rhoPrime(rgnPi)
              (TBase(TUnit),
               rhoPrime + (rgnPi -> (typPi, F1, MAggregate(map + (lastPath -> rgn)))),
               gammaPrime)
            }
            case (typ, _, _) => throw Errors.TypeError(
              expected = TRef(AbsRegion, QMut, AbsType),
              found = typ
            )
          }
        }
      }
      case None => throw Errors.UnboundIdentifier(id)
    }

    // T-AssignEpsilon
    case EAssign(id, Seq(), expr) => this.check(expr) match {
      case (TRef(rgn, QMut, typ), rhoPrime, gammaPrime) => {
        gamma.get(id) match {
          case Some(idRgn) => AdditionalJudgments.RegionWellFormed(rhoPrime)(QMut, idRgn)
          case None => throw Errors.UnboundIdentifier(id)
        }
        (TBase(TUnit), rhoPrime, gammaPrime + (id -> rgn))
      }
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, QMut, AbsType),
        found = typ
      )
    }

    // T-App
    case EApp(fun, tyargs, args) => this.check(fun) match {
      case (TRef(_, _, TFun(typarams, params, retTyp)), rhoF, gammaF) => {
        val (typs, TypeChecker(_, _, rhoPrime, gammaPrime)) =
          TypeChecker(sigma, delta, rhoF, gammaF).checkThread(args)

        val subst = TypeSubstitution(typarams.map(_._1).zip(tyargs).toMap)

        for (typ <- typs; param <- params)
          if (typ != subst(param)) throw Errors.TypeError(expected = subst(param), found = typ)
        (retTyp, rhoPrime, gammaPrime)
      }
      case (typ, _, _) => throw Errors.TypeError(
        expected = TRef(AbsRegion, AbsMuta, TFun(Seq(), Seq(), AbsType)),
        found = typ
      )
    }

    // T-Seq
    case ESeq(e1, e2) => this.check(e1) match {
      case (TBase(TUnit), rho1, gamma1) => TypeChecker(sigma, delta, rho1, gamma1).check(e2)
      case (typ, _, _) => throw Errors.TypeError(
        expected = TBase(TUnit),
        found = typ
      )
    }

    // T-If
    case EIf(pred, cons, alt) => this.check(pred) match {
      case (TRef(_, _, TBase(TBool)), rho1, gamma1) =>
        TypeChecker(sigma, delta, rho1, gamma1).check(cons) match {
          case (typ2, rho2, gamma2) => TypeChecker(sigma, delta, rho1, gamma1).check(alt) match {
            case (typ3, rho3, gamma3) => {
              assert(typ2 == typ3)
              // FIXME: join the two environments somehow? or maybe that's not necessary anymore?
              (typ3, rho3, gamma3)
            }
          }
        }
      case (typ, _, _) => throw Errors.TypeError(
        expected = TBase(TBool),
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
