package oxide

object Syntax {
  type Identifier = String

  sealed trait MutabilityQuantifier
  case object QImm extends MutabilityQuantifier
  case object QMut extends MutabilityQuantifier

  sealed trait ImmediatePath
  case class PField(id: Identifier) extends ImmediatePath
  case class PProj(idx: Int) extends ImmediatePath
  case class PIndex(idx: Int) extends ImmediatePath
  case object PDeref extends ImmediatePath

  type Path = Seq[ImmediatePath]

  sealed trait Fraction {
    lazy val norm = FractionNormalizer.normalize(this)
  }
  case object FZeta extends Fraction
  case class FNum(n: Int) extends Fraction
  case class FDiv(numerator: Fraction, denominator: Fraction) extends Fraction
  case class FAdd(lhs: Fraction, rhs: Fraction) extends Fraction

  val F0 = FNum(0)
  val F1 = FNum(1)

  sealed trait Region
  case class RVar(n: Int) extends Region with Var
  case class RConcrete(n: Int) extends Region
  case object RAbstract extends Region

  sealed trait BaseType
  case object TBool extends BaseType
  case object Tu32 extends BaseType
  case object TUnit extends BaseType

  sealed trait Kind
  case object KType extends Kind
  case object KRegion extends Kind

  sealed trait Var
  type Quantifier = (Var, Kind)
  type Quantifiers = Seq[Quantifier]

  /*=========*\
  ||  Types  ||
  \*=========*/

  sealed trait Type
  case class TVar(id: Identifier) extends Type with Var
  case class TBase(bt: BaseType) extends Type
  case class TRef(rgn: Region, mu: MutabilityQuantifier, typ: Type) extends Type
  case class TFun(quantifiers: Quantifiers, typparams: Seq[TRef], ret: Type) extends Type
  case class TArray(typ: Type, len: Int) extends Type
  case class TSlice(typ: Type) extends Type
  case class TProd(typs: Seq[Type]) extends Type
  case class TStruct(name: Identifier, typargs: GenTypes) extends Type
  type Types = Seq[Type]

  sealed trait GenType
  case class TTyp(typ: Type) extends GenType
  case class TRgn(rgn: Region) extends GenType
  type GenTypes = Seq[GenType]

  /*=========*\
  || Effects ||
  \*=========*/

  sealed trait Effect {
    def commutesWith(that: Effect): Boolean = Effects.commutes(this, that)
  }

  case class EffNewRegion(
    rgn: Region, typ: Type, frac: Fraction, subs: Map[ImmediatePath, Region]
  ) extends Effect
  case class EffDeleteRegion(rgn: Region) extends Effect
  case class EffBorrow(mu: MutabilityQuantifier, rgn1: Region, rgn2: Region) extends Effect
  case class EffSlice(mu: MutabilityQuantifier, rgn1: Region, rgn2: Region) extends Effect
  case class EffUpdate(rgn1: Region, pi: Path, rgn2: Region) extends Effect
  type Effects = Seq[Effect]

  /*===============*\
  ||  Expressions  ||
  \*===============*/

  sealed trait Primitive
  case object ETrue extends Primitive
  case object EFalse extends Primitive
  case class ENum(n: Int) extends Primitive
  case object EUnit extends Primitive

  sealed trait Expression
  case class EVar(id: Identifier) extends Expression
  case class EPrim(prim: Primitive) extends Expression
  case class EAlloc(rgn: RConcrete, expr: Expression) extends Expression
  case class ECopy(rgn: RConcrete, expr: Expression) extends Expression
  case class EDrop(rgn: RConcrete) extends Expression
  case class EBorrow(
    rgn: RConcrete, mu: MutabilityQuantifier, id: Identifier, pi: Path
  ) extends Expression
  case class EDeref(expr: Expression) extends Expression
  case class ESlice(
    rgn: RConcrete, mu: MutabilityQuantifier, e1: Expression, e2: Expression, e3: Expression
  ) extends Expression
  case class ELet(
    mu: MutabilityQuantifier, id: Identifier, e1: Expression, e2: Expression
  ) extends Expression
  case class EAssign(id: Identifier, pi: Path, expr: Expression) extends Expression
  case class EClosure(
    quantifiers: Quantifiers, params: Seq[(Identifier, TRef)], body: Expression
  ) extends Expression
  case class EMoveClosure(
    quantifiers: Quantifiers, params: Seq[(Identifier, TRef)], body: Expression
  ) extends Expression
  case class EApp(fun: Expression, typargs: GenTypes, args: Expressions) extends Expression
  case class ESeq(e1: Expression, e2: Expression) extends Expression
  case class EIf(pred: Expression, cons: Expression, alt: Expression) extends Expression
  case class EMatch(discrim: Expression, arms: Seq[MatchArm]) extends Expression
  case class EFor(
    mu: MutabilityQuantifier, id: Identifier, e: Expression, body: Expression
  ) extends Expression
  case class EProd(exprs: Expressions) extends Expression
  case class EArray(exprs: Expressions) extends Expression
  case class EStructRecord(
    name: Identifier, typargs: GenTypes, args: Seq[(Identifier, Expression)]
  ) extends Expression
  case class EStructTuple(name: Identifier, typargs: GenTypes, args: Expressions) extends Expression
  case class EEnumRecord(
    name: Identifier, variant: Identifier, typargs: GenTypes, args: Seq[(Identifier, Expression)]
  ) extends Expression
  case class EEnumTuple(
    name: Identifier, variant: Identifier, typargs: GenTypes, args: Expressions
  ) extends Expression
  type Expressions = Seq[Expression]

  /*============*\
  ||  Patterns  ||
  \*============*/

  sealed trait Pattern
  case object PWildcard extends Pattern
  case class PProd(
    variant: Identifier, args: Seq[(MutabilityQuantifier, Identifier)]
  ) extends Pattern
  case class PStruct(
    variant: Identifier, args: Seq[(Identifier, MutabilityQuantifier, Identifier)]
  ) extends Pattern
  type MatchArm = (Pattern, Expression)

  /*============*\
  ||  Contexts  ||
  \*============*/

  type VarContext = Map[Identifier, Region]
  type TyVarContext = Map[Var, Kind]
  type RegionContext = Map[Region, (Type, Fraction, Metadata)]
  type GlobalContext = Unit // FIXME(awe)

  implicit class RichVarContext(ctx: VarContext) {
    def apply(rgn: Region) = ctx.find({ case (id, idRgn) => idRgn == rgn }).get
  }

  sealed trait Metadata
  case object MNone extends Metadata
  case class MAlias(from: Region) extends Metadata
  case class MAggregate(map: Map[ImmediatePath, Region]) extends Metadata

  /*=====================*\
  ||  Abstract Versions  ||
  \*=====================*/

  case object AbsMuta extends MutabilityQuantifier
  case object AbsRegion extends Region
  case object AbsBaseType extends BaseType
  case object AbsType extends Type
}
