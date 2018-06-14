package oxide

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
      rhoPrime.get(rgnPi).map(prod => (rgnPi, prod, rhoPrime))
    }) match { // FIXME: normalize fractions?
      case Some((rgnPi, (_, FNum(0), _), _)) => throw Errors.IllegalBorrow(F1, FNum(0), rgnPi)
      case Some((rgnPi, (typ, frac, meta), rhoPrime)) => if (rhoPrime.contains(rgn) == false) {
        // TODO: check valid borrow
        (TRef(rgn, QMut, typ),
         rhoPrime ++ Seq(rgnPi -> (typ, FDiv(frac, FNum(2)), MNone),
                         rgn -> ((typ, FDiv(frac, FNum(2)), MAlias(rgnPi)))),
         gamma)
      } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case None => ???
    }

    // T-BorrowMut
    case EBorrow(rgn, QMut, id, pi) => gamma.get(id).flatMap(rgnId => {
      val (typPi, rgnPi, rhoPrime) = AdditionalJudgments.RegionValidAlongPath(rho)(QMut, pi, rgnId)
      rhoPrime.get(rgnPi).map(prod => (rgnPi, prod, rhoPrime))
    }) match {
      case Some((rgnPi, (typ, FNum(1), meta), rhoPrime)) => if (rhoPrime.contains(rgn) == false) {
        // TODO: check valid borrow
        (TRef(rgn, QMut, typ),
         rhoPrime ++ Seq(rgnPi -> (typ, F0, MNone), rgn -> ((typ, F1, MAlias(rgnPi)))),
         gamma)
      } else throw Errors.RegionAlreadyInUse(rgn, rho)
      case Some((rgnPi, (_, frac, _), _)) => throw Errors.IllegalBorrow(F1, frac, rgnPi)
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

    case _ => ???
  }
}

object AdditionalJudgments {
  case class RegionValidAlongPath(rho: RegionContext) {
    def apply(
      mu: MutabilityQuantifier, pi: Path, rgn: Region
    ): (Type, Region, RegionContext) = (rho.get(rgn), pi) match {
      // P-EpsilonPath
      case (Some((typ, frac, MNone)), Seq()) => (mu, frac) match { // FIXME: normalize fractions?
        case (QMut, FNum(1)) => (typ, rgn, rho)
        case (QMut, frac) => throw Errors.IllegalBorrow(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.IllegalBorrow(FZeta, F0, rgn)
        case (QImm, _) => (typ, rgn, rho)
        case (AbsMuta, _) => throw Errors.Unreachable
      }
      // P-EpsilonPath: implied error condition
      case (Some((_, _, meta)), Seq()) => throw Errors.UnexpectedMetadata(meta, MNone, rgn)

      // implied error condition
      case (Some((_, _, MNone)), immPath :: _) =>
        throw Errors.UnexpectedMetadata(MNone, MAggregate(Map(immPath -> AbsRegion)), rgn)

      // P-AliasPath
      case (Some((_, frac, MAlias(src))), immPath :: _) => (mu, frac) match {
        // FIXME: the alias rule is problematic because we know the recursive call will always fail
        case (QMut, FNum(1)) => this(mu, pi, src)
        case (QMut, frac) => throw Errors.IllegalBorrow(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.IllegalBorrow(FZeta, F0, rgn)
        case (QImm, _) => this(mu, pi, src)
        case (AbsMuta, _) => throw Errors.Unreachable
      }

      // P-FieldPath and P-FieldPathAbs
      case (Some((typ, frac, MAggregate(piMap))), immPath :: path) => (mu, frac) match {
        case (QMut, FNum(1)) => rgn match {
          // P-FieldPathAbs
          case RAbstract => ???
          case AbsRegion => throw Errors.Unreachable
          // P-FieldPath
          case _ => this(mu, path, piMap(immPath))
        }
        case (QMut, frac) => throw Errors.IllegalBorrow(F1, frac, rgn)
        case (QImm, FNum(0)) => throw Errors.IllegalBorrow(FZeta, F0, rgn)
        case (QImm, _) => rgn match {
          // P-FieldPathAbs
          case RAbstract => ???
          case AbsRegion => throw Errors.Unreachable
          // P-FieldPath
          case _ => this(mu, path, piMap(immPath))
        }
        case (AbsMuta, _) => throw Errors.Unreachable
      }
    }
  }
}
