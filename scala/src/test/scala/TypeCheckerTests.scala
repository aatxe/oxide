import org.scalatest._

import oxide.DSL._
import oxide.Errors._
import oxide.Syntax._
import oxide.TypeChecker

class TypeCheckerTests extends FlatSpec with Matchers {
  "The Oxide type checker" should "type check binding a variable to an allocated primitive" in {
    TypeChecker((), Map(), Map(), Map()).check(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        unit
      }
    ) should be (
      unitT, Map(tick(0) -> (u32, whole, MNone)), Map("x" -> tick(0))
    )
  }

  it should "type check copying a primitive" in {
    // NOTE(awe 2018-06-14): this fails because the borrow doesn't get dropped.
    TypeChecker((), Map(), Map(), Map()).check(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        let (mut) ("y" be copy (tick(1)) (borrow (tick(2)) (imm) ("x"))) {
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (u32, whole, MNone),
          tick(1) -> (u32, whole, MNone)),
      Map("x" -> tick(0), "y" -> tick(1))
    )
  }

  it should "type check a single mutable borrow from a region" in {
    TypeChecker((), Map(), Map(), Map()).check(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        let (mut) ("y" be borrow (tick(1)) (mut) ("x")) {
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (u32, none, MNone),
          tick(1) -> (u32, whole, MAlias(tick(0)))),
      Map("x" -> tick(0), "y" -> tick(1))
    )
  }

  it should "not type check borrowing mutably twice from the same region" in {
    a [IllegalBorrow] should be thrownBy {
      TypeChecker((), Map(), Map(), Map()).check(
        let (mut) ("x" be alloc (tick(0)) (5)) {
          let (mut) ("y" be borrow (tick(1)) (mut) ("x")) {
            let (mut) ("z" be borrow (tick(2)) (mut) ("x")) {
              unit
            }
          }
        }
      )
    }
  }

  it should "type check a mutable borrow from within an aggregate region" in {
    TypeChecker((), Map(), Map(), Map()).check(
      let (mut) ("x" be alloc (tick(0)) (tup(alloc (tick(1)) (5)))) {
        let (mut) ("y" be borrow (tick(2)) (mut) ("x" dot proj(0))) {
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (tup(u32), whole, MAggregate(Map(proj(0) -> tick(1)))),
          tick(1) -> (u32, none, MNone),
          tick(2) -> (u32, whole, MAlias(tick(1)))),
      Map("x" -> tick(0), "y" -> tick(2))
    )
  }

  it should "type check borrowing immutably twice from the same region" in {
    val regionCtx =

    TypeChecker((), Map(), Map(), Map()).check(
      let (imm) ("x" be alloc (tick(0)) (5)) {
        let (imm) ("y" be borrow (tick(1)) (imm) ("x")) {
          let (imm) ("z" be borrow (tick(2)) (imm) ("x")) {
            unit
          }
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> ((u32, whole / 2 / 2, MNone)),
          tick(1) -> ((u32, whole / 2, MAlias(tick(0)))),
          tick(2) -> ((u32, whole / 2 / 2, MAlias(tick(0))))),
      Map("x" -> tick(0), "y" -> tick(1), "z" -> tick(2))
    )
  }
}
