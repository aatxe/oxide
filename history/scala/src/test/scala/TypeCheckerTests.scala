import org.scalatest._

import oxide.DSL._
import oxide.Errors._
import oxide.Syntax._
import oxide.TypeChecker

class TypeCheckerTests extends FlatSpec with Matchers {
  "The Oxide type checker" should "type check binding a variable to an allocated primitive" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        unit
      }
    ) should be (
      unitT, Map(tick(0) -> (u32, whole, MNone))
    )
  }

  it should "type check copying a primitive" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        let (mut) ("y" be copy (tick(1)) (borrow (tick(2)) (imm) ("x"))) {
          drop (tick(2)) |>
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (u32, whole, MNone),
          tick(1) -> (u32, whole, MNone))
    )
  }

  it should "type check a single mutable borrow from a region" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        let (mut) ("y" be borrow (tick(1)) (mut) ("x")) {
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (u32, none, MNone),
          tick(1) -> (u32, whole, MAlias(tick(0))))
    )
  }

  it should "not type check borrowing mutably twice from the same region" in {
    a [InsufficientCapability] should be thrownBy {
      TypeChecker.checkPost(
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
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (tup(alloc (tick(1)) (5)))) {
        let (mut) ("y" be borrow (tick(2)) (mut) ("x" dot proj(0))) {
          unit
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (tup(u32), whole, MAggregate(Map(proj(0) -> tick(1)))),
          tick(1) -> (u32, none, MNone),
          tick(2) -> (u32, whole, MAlias(tick(1))))
    )
  }

  it should "type check borrowing immutably twice from the same region" in {
    val regionCtx =

    TypeChecker.checkPost(
      let (imm) ("x" be alloc (tick(0)) (5)) {
        let (imm) ("y" be borrow (tick(1)) (imm) ("x")) {
          let (imm) ("z" be borrow (tick(2)) (imm) ("x")) {
            unit
          }
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> ((u32, whole / 4, MNone)),
          tick(1) -> ((u32, whole / 2, MAlias(tick(0)))),
          tick(2) -> ((u32, whole / 4, MAlias(tick(0)))))
    )
  }

  it should "type check simple if expressions" in {
    TypeChecker.checkPost(
      let (imm) ("pred" be alloc (tick(0)) (true)) {
        let (imm) (
          "x" be (
            ite (borrow (tick(1)) (imm) ("pred")) {
              alloc (tick(2)) (5)
            } {
              alloc (tick(2)) (8)
            }
          )
        ) {
          drop (tick(1))
        }
      }
    ) should be (
      unitT,
      Map(tick(0) -> (bool, whole, MNone),
          tick(2) -> (u32, whole, MNone))
    )
  }

  it should "not type check allocating a region at different types with branching" in {
    a [AssertionError] should be thrownBy {
      TypeChecker.checkPost(
        let (imm) ("pred" be alloc (tick(0)) (true)) {
          let (imm) (
            "x" be (
              ite (borrow (tick(1)) (imm) ("pred")) {
                alloc (tick(2)) (5)
              } {
                alloc (tick(2)) (false)
              }
            )
          ) {
            drop (tick(1))
          }
        }
      )
    }
  }

  it should "type check an assignment within an aggregate region" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (tup(alloc (tick(1)) (5)))) {
        (("x" dot proj(0)) := (alloc (tick(2)) (4))) |>
        drop (tick(1))
      }
    ) should be (
      unitT,
      Map(tick(0) -> (tup(u32), whole, MAggregate(Map(proj(0) -> tick(2)))),
          tick(2) -> (u32, whole, MNone))
    )
  }

  it should "type check dropping an aggregate region after its components" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (tup(alloc (tick(1)) (5)))) {
        (drop (tick(1))) |>
        drop (tick(0))
      }
    ) should be (
      unitT, Map()
    )
  }

  it should "not type check dropping an aggregate region before its components" in {
    a [BadAggregateFree] should be thrownBy {
      TypeChecker.checkPost(
        let (mut) ("x" be alloc (tick(0)) (tup(alloc (tick(1)) (5)))) {
          (drop (tick(0))) |>
            drop (tick(1))
        }
      )
    }
  }

  it should "type check the identity function and its application" in {
    val funTyp =
      forall(vari(0) <| RGN) {
        Fn(ref (vari(0)) (mut) (u32)) -> ref (tick(1)) (mut) (u32)
      }

    TypeChecker.checkPost(
      let (imm) ("f" be alloc (tick(0)) {
        forall(vari(0) <| RGN) {
          fn("x" <| ref (vari(0)) (mut) (u32)) {
            borrow (tick(1)) (mut) ("x")
          }
        }
      }) {
        (borrow (tick(2)) (imm) ("f"))(tick(3))(alloc (tick(3)) (5))
      }
    ) should be (
      ref (tick(1)) (mut) (u32),
      Map(tick(0) -> (funTyp, whole / 2, MNone),
          tick(1) -> (u32, whole, MAlias(tick(3))),
          tick(2) -> (funTyp, whole / 2, MAlias(tick(0))),
          tick(3) -> (u32, none, MNone)) // FIXME: tick(3) has whole permissions currently
    )
  }

  it should "type check a simple program using dereference" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (5)) {
        let (mut) ("y" be borrow (tick(1)) (mut) ("x")) {
          deref (borrow (tick(2)) (imm) ("y"))
        }
      }
    ) should be (
      u32,
      Map(tick(0) -> (u32, none, MNone),
          tick(1) -> (u32, whole / 2, MAlias(tick(0))),
          tick(2) -> (u32, whole / 2, MAlias(tick(1))))
    )
  }

  it should "type check a basic branching program" in {
    TypeChecker.checkPost(
      let (mut) ("x" be alloc (tick(0)) (true)) {
        let (mut) ("y" be (
                     ite(borrow (tick(3)) (imm) ("x")) {
                       (alloc (tick(1)) (8))
                     } {
                       (alloc (tick(1)) (1))
                     }
                   )) {
          deref (borrow (tick(2)) (imm) ("y"))
        }
      }
    ) should be (
      u32,
      Map(tick(0) -> (bool, whole / 2, MNone),
          tick(3) -> (bool, whole / 2, MAlias(tick(0))),
          tick(1) -> (u32, whole / 2, MNone),
          tick(2) -> (u32, whole / 2, MAlias(tick(1))))
    )
  }

  it should "type check a branching program with a mutable borrow opposite an alloc" in {
    TypeChecker.checkPost(
      let (mut) ("pred" be alloc (tick(0)) (true)) {
        let (mut) ("x" be alloc (tick(4)) (7)) {
          let (mut) ("y" be (
                       ite(borrow (tick(3)) (imm) ("pred")) {
                         (borrow (tick(1)) (mut) ("x"))
                       } {
                         (alloc (tick(1)) (1))
                       }
                     )) {
            deref (borrow (tick(2)) (imm) ("y"))
          }
        }
      }
    ) should be (
      u32,
      Map(tick(0) -> (bool, whole / 2, MNone),
          tick(4) -> (u32, none, MNone),
          tick(3) -> (bool, whole / 2, MAlias(tick(0))),
          tick(1) -> (u32, whole / 2, MNone), // FIXME: MAlias(tick(4)) in the first branch
          tick(2) -> (u32, whole / 2, MAlias(tick(1))))
    )
  }
}
