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
    case EAlloc(rgn, inner@EPrim(_)) => if (rho.contains(rgn) == false) {
      val (typ, rhoPrime, gammaPrime) = this.check(inner)
      assert(rhoPrime == rho)
      assert(gammaPrime == gamma)
      (TRef(rgn, QMut, typ), rho + (rgn -> (typ, F1, MNone)), gamma)
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    case EAlloc(rgn, EProd(exprs)) => if (rho.contains(rgn) == false) {
      val (typs, TypeChecker(_, _, rhoPrime, gammaPrime)) = this.checkThread(exprs)
      val meta = MAggregate(typs.zipWithIndex.map {
        case (TRef(rgn, _, _), idx) => PProj(idx) -> rgn
        case _ => ??? // TODO(awe): type error
      }.toMap)
      (TRef(rgn, QMut, TProd(typs)), rhoPrime + (rgn -> (TProd(typs), F1, meta)), gammaPrime)
    } else throw Errors.RegionAlreadyInUse(rgn, rho)

    case EPrim(ETrue)
       | EPrim(EFalse) => (TBase(TBool), rho, gamma)
    case EPrim(ENum(n)) => (TBase(Tu32), rho, gamma) // FIXME(awe): fix bounds on n
    case EPrim(EUnit) => (TBase(TUnit), rho, gamma)

    case ELet(QImm, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, mu, ty1), rho1, gamma1) => {
        val (ty2, rho2, gamma2) = TypeChecker(
          sigma, delta, rho1, gamma1 + (id -> r1)
        ).check(e2)
        assert(rho2.contains(r1) == false)
        (ty2, rho2, gamma2)
      }
      case _=> ???
    }

    case ELet(QMut, id, e1, e2) => this.check(e1) match {
      case (TRef(r1, QMut, ty1), rho1, gamma1) => {
        val (ty2, rho2, gamma2) = TypeChecker(
          sigma, delta, rho1, gamma1 + (id -> r1)
        ).check(e2)
        // assert(rho2.contains(r1) == false)
        (ty2, rho2, gamma2)
      }
      case _=> ???
    }

    case _ => ???
  }
}
