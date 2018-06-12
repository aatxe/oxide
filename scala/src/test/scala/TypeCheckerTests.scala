import org.scalatest._

import oxide.Syntax._
import oxide.TypeChecker

class TypeCheckerTests extends FlatSpec with Matchers {
  "Binding a variable to an allocated primitive" should "type check" in {
    TypeChecker((), Map(), Map(), Map()).check(
      ELet(QMut, "x", EAlloc(RConcrete(0), EPrim(ENum(5))),
           EPrim(EUnit))
    ) should be (
      TBase(TUnit), Map(RConcrete(0) -> (TBase(Tu32), F1, MNone)), Map("x" -> RConcrete(0))
    )
  }
}
