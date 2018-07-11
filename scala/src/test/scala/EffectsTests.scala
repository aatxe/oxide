import org.scalatest._
import matchers._

import oxide.DSL._
import oxide.Errors._
import oxide.Syntax._

class EffectsTests extends FlatSpec with Matchers {
  "A newrgn effect" should "commute with a non-interfering newrgn" in {
    val eff1 = newrgn (Tu32, whole, Map()) as tick(0)
    val eff2 = newrgn (Tu32, whole, Map()) as tick(1)
    eff1 should commuteWith (eff2)
  }

  it should "not commute with a newrgn that contains it" in {
    val eff1 = newrgn (Tu32, whole, Map()) as tick(0)
    val eff2 = newrgn (tup(Tu32, Tu32),
                       whole,
                       Map(proj(0) -> tick(0), proj(1) -> tick(1))
    ) as tick(2)
    eff1 should not (commuteWith (eff2))
  }

  it should "commute with an unrelated borrow" in {
    val eff1 = newrgn (Tu32, whole, Map()) as tick(0)
    val eff2 = borrow (mut, tick(1)) as (tick(2))
    eff1 should commuteWith (eff2)
  }

  it should "not commute with a borrow from itself" in {
    val eff1 = newrgn (Tu32, whole, Map()) as tick(0)
    val eff2 = borrow (mut, tick(0)) as (tick(1))
    eff1 should not (commuteWith (eff2))
  }

  "Effects.commutingGroups" should "yield groups with only elements of the original effect" in {
    val eff = Seq(
      newrgn (Tu32, whole, Map()) as tick(0),
      newrgn (Tu32, whole, Map()) as tick(1),
      newrgn (tup(Tu32, Tu32), whole, Map(proj(0) -> tick(0), proj(1) -> tick(1))) as tick(2),
      borrow (mut, tick(0)) as tick(3),
      borrow (imm, tick(1)) as tick(4),
      borrow (imm, tick(1)) as tick(5),
      delrgn (tick(5)),
    )

    assert {
      eff.commutingGroups.flatten.forall(e => eff.find(_ == e).nonEmpty)
    }
  }

  it should "have the same total size as the original effect" in {
    val eff = Seq(
      newrgn (Tu32, whole, Map()) as tick(0),
      newrgn (Tu32, whole, Map()) as tick(1),
      newrgn (tup(Tu32, Tu32), whole, Map(proj(0) -> tick(0), proj(1) -> tick(1))) as tick(2),
      borrow (mut, tick(0)) as tick(3),
      borrow (imm, tick(1)) as tick(4),
      borrow (imm, tick(1)) as tick(5),
      delrgn (tick(5)),
    )

    assert {
      eff.commutingGroups.flatten.size == eff.size
    }
  }

  it should "collect effects into maximal mutually-commuting sets" in {
    val eff = Seq(
      newrgn (Tu32, whole, Map()) as tick(0),
      newrgn (Tu32, whole, Map()) as tick(1),
      newrgn (tup(Tu32, Tu32), whole, Map(proj(0) -> tick(0), proj(1) -> tick(1))) as tick(2),
      borrow (mut, tick(0)) as tick(3),
      borrow (imm, tick(1)) as tick(4),
      borrow (imm, tick(1)) as tick(5),
      delrgn (tick(5)),
    )

    eff.commutingGroups should be (Seq(
      Set(
        newrgn (Tu32, whole, Map()) as tick(0),
        newrgn (Tu32, whole, Map()) as tick(1),
      ),
      Set(
        newrgn (tup(Tu32, Tu32), whole, Map(proj(0) -> tick(0), proj(1) -> tick(1))) as tick(2),
      ),
      Set(
        borrow (mut, tick(0)) as tick(3),
        borrow (imm, tick(1)) as tick(4),
        borrow (imm, tick(1)) as tick(5),
      ),
      Set(
        delrgn (tick(5)),
      ),
    ))
  }

  case class CommutesWithMatcher(eff2: Effect) extends Matcher[Effect] {
    def apply(eff1: Effect) = {
      MatchResult(
        eff1 commutesWith eff2,
        s"Effect $eff1 did not commute with effect $eff2",
        s"Effect $eff1 commutes with effect $eff2"
      )
    }
  }
  def commuteWith(eff2: Effect) = CommutesWithMatcher(eff2)
}
