package oxide

import Errors.KindError
import Syntax._

object Substitution {
  case class TypeSubstitution(inner: Map[Var, GenType]) {
    def apply(typ: Type) = substitute(typ, inner)
    def inVarContext(gamma: VarContext) = substVarContext(gamma, inner)
    def inRegionContext(rho: RegionContext) = substRegionContext(rho, inner)
  }

  private def substitute(typ: Type, subst: Map[Var, GenType]): Type = typ match {
    case vari@TVar(_) => subst.getOrElse(vari, vari) match {
      case TTyp(typ) => typ
      case TRgn(_) => throw KindError(expected = KType, found = KRegion)
    }
    case TBase(_) => typ
    case TRef(rgn, mu, typ) => TRef(substitute(rgn, subst), mu, substitute(typ, subst))
    case TFun(_, _, _) => typ // FIXME: capture-avoidance is work
    case TArray(typ, len) => TArray(substitute(typ, subst), len)
    case TSlice(typ) => TSlice(substitute(typ, subst))
    case TProd(typs) => TProd(typs.map(substitute(_, subst)))
    case TStruct(name, typargs) => TStruct(name, typargs.map {
      case TTyp(typ) => TTyp(substitute(typ, subst))
      case TRgn(rgn) => TRgn(substitute(rgn, subst))
    })
    case AbsType => throw Errors.Unreachable
  }

  private def substitute(rgn: Region, subst: Map[Var, GenType]): Region = rgn match {
    case rgn@RVar(_) => subst.getOrElse(rgn, rgn) match {
      case TRgn(rgnPrime) => rgnPrime
      case TTyp(_) => throw KindError(expected = KRegion, found = KType)
    }
    case _ => rgn
  }

  private def substitute(meta: Metadata, subst: Map[Var, GenType]): Metadata = meta match {
    case MNone => MNone
    case MAlias(rgn) => MAlias(substitute(rgn, subst))
    case MAggregate(map) => MAggregate(
      map.map {
        case (pi, rgn) => pi -> substitute(rgn, subst)
      }
    )
  }

  private def substVarContext(gamma: VarContext, subst: Map[Var, GenType]): VarContext =
    gamma.map {
      case (id, rgn) => id -> substitute(rgn, subst)
    }

  private def substRegionContext(rho: RegionContext, subst: Map[Var, GenType]): RegionContext =
    rho.map {
      case (rgn, (typ, frac, meta)) =>
        substitute(rgn, subst) -> (substitute(typ, subst), frac, substitute(meta, subst))
    }
}
