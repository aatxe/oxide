package oxide

import scala.language.implicitConversions

import Syntax._

object DSL {
  def imm = QImm
  def mut = QMut

  def proj(id: Identifier) = PField(id)
  def proj(idx: Int) = PProj(idx)
  def idx(idx: Int) = PIndex(idx)
  def deref = PDeref

  def none = F0
  def whole = F1
  def zeta = FZeta

  implicit def numToFraction(n: Int): Fraction = FNum(n)
  implicit class RichFraction(frac: Fraction) {
    def /(other: Fraction) = FDiv(frac, other)
    def +(other: Fraction) = FAdd(frac, other)
  }

  def tick(n: Int) = RConcrete(n)
  def vari(n: Int) = RVar(n)

  def bool = TBase(TBool)
  def u32 = TBase(Tu32)
  def unitT = TBase(TUnit)

  def star = KType
  def RGN = KRegion

  implicit class RichVar(vari: Var) {
    def <|(kind: Kind): Quantifier = (vari, kind)
  }
  def forall(quantifiers: Quantifier*): Quantifiers = quantifiers.toSeq

  implicit class RichQuantifiers(quantifiers: Quantifiers) {
    def apply(arrow: (Seq[TRef], Effects, Type)) = TFun(quantifiers, arrow._1, arrow._2, arrow._3)

    // EClosure
    def apply(arrow: (Seq[(Identifier, TRef)], Expression)) =
      EClosure(quantifiers, arrow._1, arrow._2)

    // EMoveClosure
    def move(arrow: (Seq[(Identifier, TRef)], Expression)) =
      EMoveClosure(quantifiers, arrow._1, arrow._2)
  }

  def vari(id: Identifier) = TVar(id)
  implicit def baseTypeToType(bt: BaseType): Type = TBase(bt)
  def ref(rgn: Region)(mu: MutabilityQuantifier)(typ: Type) = TRef(rgn, mu, typ)

  def Fn(tys: TRef*): Seq[TRef] = tys.toSeq
  implicit class RichTRefs(trefs: Seq[TRef]) {
    def ->(ret: Type): (Seq[TRef], Effects, Type) = (trefs, Seq(), ret)
    def -(eff: Effects): ArgsEffPair = ArgsEffPair(trefs, eff)
  }
  case class ArgsEffPair(trefs: Seq[TRef], eff: Effects) {
    def >(ret: Type): (Seq[TRef], Effects, Type) = (trefs, eff, ret)
  }
  implicit def quantifierlessFunctions(p: (Seq[TRef], Effects, Type)): Type =
    TFun(Seq(), p._1, p._2, p._3)

  def array(typ: Type, len: Int) = TArray(typ, len)
  def slice(typ: Type) = TSlice(typ)

  def tup(typs: Type*) = TProd(typs.toSeq)
  implicit def tupToProd2(a: (Type, Type)): TProd = TProd(Seq(a._1, a._2))
  implicit def tupToProd3(a: (Type, Type, Type)): TProd = TProd(Seq(a._1, a._2, a._3))
  implicit def tupToProd4(a: (Type, Type, Type, Type)): TProd = TProd(Seq(a._1, a._2, a._3, a._4))

  implicit def idToIdPath(id: Identifier): (Identifier, Path) = (id, Seq())
  implicit class RichIdentifier(id: Identifier) {
    def apply(typargs: GenType*) = TStruct(id, typargs.toSeq)

    def dot(path: ImmediatePath): (Identifier, Path) = (id, Seq(path))
    def dot(path: Path): (Identifier, Path) = (id, path)

    def be(expr: Expression): (Identifier, Expression) = (id, expr)

    def <|(typ: TRef): (Identifier, TRef) = (id, typ)
  }

  implicit def typeToGenType(typ: Type): GenType = TTyp(typ)
  implicit def rgnToGenType(rgn: Region): GenType = TRgn(rgn)

  def newrgn(typ: Type, frac: Fraction, subs: Map[ImmediatePath, Region]) =
    PartialEffNewRegion(typ, frac, subs)
  case class PartialEffNewRegion(typ: Type, frac: Fraction, subs: Map[ImmediatePath, Region]) {
    def as(rgn: Region) = EffNewRegion(rgn, typ, frac, subs)
  }

  def delrgn(rgn: Region) = EffDeleteRegion(rgn)

  def borrow(mu: MutabilityQuantifier, rgn: Region) = PartialEffBorrow(mu, rgn)
  case class PartialEffBorrow(mu: MutabilityQuantifier, rgn1: Region) {
    def as(rgn2: Region) = EffBorrow(mu, rgn1, rgn2)
  }

  def slice(mu: MutabilityQuantifier, rgn: Region) = PartialEffSlice(mu, rgn)
  case class PartialEffSlice(mu: MutabilityQuantifier, rgn1: Region) {
    def as(rgn2: Region) = EffSlice(mu, rgn1, rgn2)
  }

  def update(rgn1: Region, pi: Path) = PartialEffUpdate(rgn1, pi)
  case class PartialEffUpdate(rgn1: Region, pi: Path) {
    def to(rgn2: Region) = EffUpdate(rgn1, pi, rgn2)
  }

  implicit class RichEffects(eff: Effects) {
    lazy val commutingGroups = Effects.commutingGroups(eff)

    def onRegionCtx(rho: RegionContext): RegionContext = Effects.applyToRegionCtx(eff, rho)
    def onVarCtx(gamma: VarContext): VarContext = Effects.applyToVarCtx(eff, gamma)
  }

  implicit def boolToPrim(b: Boolean): Primitive = if (b) ETrue else EFalse
  implicit def boolToExpr(b: Boolean): Expression = if (b) ETrue else EFalse
  implicit def intToPrim(n: Int): Primitive = ENum(n)
  implicit def intToExpr(n: Int): Expression = EPrim(ENum(n))
  def unit = EUnit

  implicit def identifierToExpr(id: Identifier): Expression = EVar(id)
  implicit def primToExpr(prim: Primitive): Expression = EPrim(prim)
  def alloc(rgn: RConcrete)(expr: Expression) = EAlloc(rgn, expr)
  def copy(rgn: RConcrete)(expr: Expression) = ECopy(rgn, expr)
  def drop(rgn: RConcrete) = EDrop(rgn)
  def borrow(rgn: RConcrete)(mu: MutabilityQuantifier)(idPath: (Identifier, Path)) =
    EBorrow(rgn, mu, idPath._1, idPath._2)
  def deref(expr: Expression) = EDeref(expr)

  implicit class RichExpression(expr: Expression) {
    def apply(exprs: (Expression, Expression)) = (expr, exprs._1, exprs._2)

    // EApp
    def apply(tyargs: GenType*)(args: Expression*) = EApp(expr, tyargs, args)
    def apply(args: Expression*) = EApp(expr, Seq(), args)

    def to(other: Expression) = (expr, other)

    // sequence
    def |>(other: Expression) = ESeq(expr, other)
  }
  def slice(rgn: RConcrete)(mu: MutabilityQuantifier)(exprs: (Expression, Expression, Expression)) =
    ESlice(rgn, mu, exprs._1, exprs._2, exprs._3)

  def let(mu: MutabilityQuantifier)(idExpr: (Identifier, Expression))(body: Expression) =
    ELet(mu, idExpr._1, idExpr._2, body)

  implicit class RichIdPath(idPath: (Identifier, Path)) {
    def :=(expr: Expression) = EAssign(idPath._1, idPath._2, expr)

    def dot(path: ImmediatePath): (Identifier, Path) = (idPath._1, idPath._2 :+ path)
    def dot(path: Path): (Identifier, Path) = (idPath._1, idPath._2 ++ path)
  }

  def fn(pairs: (Identifier, TRef)*): Seq[(Identifier, TRef)] = pairs.toSeq
  implicit class RichIdRefSeq(seq: Seq[(Identifier, TRef)]) {
    def apply(body: Expression) = (seq, body)
  }
  implicit def quantifierlessClosure(p: (Seq[(Identifier, TRef)], Expression)): Expression =
    EClosure(Seq(), p._1, p._2)
  def move(arrow: (Seq[(Identifier, TRef)], Expression)) = EMoveClosure(Seq(), arrow._1, arrow._2)

  def ite(pred: Expression)(cons: Expression)(alt: Expression) = EIf(pred, cons, alt)

  // TODO: EMatch, EFor

  def tup(exprs: Expression*) = EProd(exprs.toSeq)
  implicit def tupToProd2(a: (Expression, Expression)): EProd = EProd(Seq(a._1, a._2))
  implicit def tupToProd3(a: (Expression, Expression, Expression)): EProd =
    EProd(Seq(a._1, a._2, a._3))
  implicit def tupToProd4(a: (Expression, Expression, Expression, Expression)): EProd =
    EProd(Seq(a._1, a._2, a._3, a._4))

  // TODO: EArray, EStructRecord, EStructTuple, EEnumRecord, EEnumTuple
}
