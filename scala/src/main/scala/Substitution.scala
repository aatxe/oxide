package oxide

import Errors.KindError
import Syntax._

object Substitution {
  case class TypeSubstitution(inner: Map[Var, GenType]) {
    def apply(typ: Type) = substitute(typ, inner)
  }

  private def substitute(typ: Type, subst: Map[Var, GenType]): Type = typ match {
    case vari@TVar(_) => subst.getOrElse(vari, vari) match {
      case TTyp(typ) => typ
      case TRgn(_) => throw KindError(expected = KType, found = KRegion)
    }
    case TBase(_) => typ
    case TRef(rgn@RVar(_), mu, typ) => subst.getOrElse(rgn, rgn) match {
      case TRgn(rgn) => TRef(rgn, mu, substitute(typ, subst))
      case TTyp(_) => throw KindError(expected = KRegion, found = KType)
    }
    case TRef(rgn, mu, typ) => TRef(rgn, mu, substitute(typ, subst))
    case TFun(_, _, _) => ??? // FIXME: capture-avoidance is work
    case TArray(typ, len) => TArray(substitute(typ, subst), len)
    case TSlice(typ) => TSlice(substitute(typ, subst))
    case TProd(typs) => TProd(typs.map(substitute(_, subst)))
    case TStruct(name, typargs) => TStruct(name, typargs.map {
      case TTyp(typ) => TTyp(substitute(typ, subst))
      case TRgn(rgn@RVar(_)) => subst.getOrElse(rgn, rgn) match {
        case rgn@TRgn(_) => rgn
        case TTyp(_) => throw KindError(expected = KRegion, found = KType)
      }
      case rgn@TRgn(_) => rgn
    })
    case AbsType => throw Errors.Unreachable
  }
}
