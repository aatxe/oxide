package oxide

import Syntax._

object Effects {
  type CommutingGroup = Set[Effect]
  type CommutingGroups = Seq[CommutingGroup]

  def commutes(eff1: Effect, eff2: Effect): Boolean = (eff1, eff2) match {
    case (EffNewRegion(r1, _, _, sub1), EffNewRegion(r2, _, _, sub2)) =>
      r1 != r2 && sub2.values.find(_ == r1).isEmpty && sub1.values.find(_ == r2).isEmpty
    case (EffNewRegion(r1, _, _, sub1), EffDeleteRegion(r2)) =>
      r1 != r2 && sub1.values.find(_ == r2).isEmpty
    case (EffNewRegion(r1, _, _, sub1), EffBorrow(_, r2, rPrime2)) =>
      r1 != r2 && r1 != rPrime2 && sub1.values.find(r => r == r2 || r == rPrime2).isEmpty
    case (EffNewRegion(r1, _, _, sub1), EffSlice(_, r2, rPrime2)) =>
      r1 != r2 && r1 != rPrime2 && sub1.values.find(r => r == r2 || r == rPrime2).isEmpty
    case (EffNewRegion(r1, _, _, sub1), EffUpdate(r2, _, rPrime2)) =>
      r1 != r2 && r1 != rPrime2 && sub1.values.find(r => r == r2 || r == rPrime2).isEmpty
    case (eff1, eff2@EffNewRegion(_, _, _, _)) => commutes(eff2, eff1)

    case (EffDeleteRegion(r1), EffDeleteRegion(r2)) => r1 != r2
    case (EffDeleteRegion(r1), EffBorrow(_, r2, rPrime2)) => r1 != r2 && r1 != rPrime2
    case (EffDeleteRegion(r1), EffSlice(_, r2, rPrime2)) => r1 != r2 && r1 != rPrime2
    case (EffDeleteRegion(r1), EffUpdate(r2, _, rPrime2)) => r1 != r2 && r1 != rPrime2
    case (eff1, eff2@EffDeleteRegion(_)) => commutes(eff2, eff1)

    case (EffBorrow(mu1, r1, rPrime1), EffBorrow(mu2, r2, rPrime2)) =>
      ((r1 != r2) || (mu1 == QImm && mu2 == QImm)) && rPrime1 != rPrime2
    case (EffBorrow(mu1, r1, rPrime1), EffSlice(mu2, r2, rPrime2)) =>
      ((r1 != r2) || (mu1 == QImm && mu2 == QImm)) && rPrime1 != rPrime2
    case (EffBorrow(_, r1, rPrime1), EffUpdate(r2, _, rPrime2)) =>
      r1 != r2 && r1 != rPrime2 && rPrime1 != r2 && rPrime1 != rPrime2
    case (eff1, eff2@EffBorrow(_, _, _)) => commutes(eff2, eff1)

    case (EffSlice(mu1, r1, rPrime1), EffSlice(mu2, r2, rPrime2)) =>
      ((r1 != r2) || (mu1 == QImm && mu2 == QImm)) && rPrime1 != rPrime2
    case (EffSlice(_, r1, rPrime1), EffUpdate(r2, _, rPrime2)) =>
      r1 != r2 && r1 != rPrime2 && rPrime1 != r2 && rPrime1 != rPrime2
    case (eff1, eff2@EffSlice(_, _, _)) => commutes(eff2, eff1)

    case (EffUpdate(r1, pi1, _), EffUpdate(r2, pi2, _)) => r1 != r2 || pi1 != pi2
  }

  def commutingGroups(eff: Effects): CommutingGroups =
    eff.foldLeft[CommutingGroups](Seq(Set())) {
      case (groups :+ latestGroup, eff) if latestGroup.forall(commutes(_, eff)) =>
        groups :+ (latestGroup + eff)
      case (groups, eff) => groups :+ Set(eff)
    }

  def compose(eff1: Effects, eff2: Effects): Effects =
    commutingGroups(eff1).zip(commutingGroups(eff2)).map {
      case (group1, group2) => compose(group1, group2)
    }.flatten

  def compose(eff1: CommutingGroup, eff2: CommutingGroup): CommutingGroup = ???
    /**
      This is not quite right. Or the notion of a commuting group is not quite right.

      Consider the row: e1 e2 e3 e4

      If e1 and e2 commute, they can form a group [e1 e2], but we'll say e2 and e3 don't commute, but
      e3 and e4 do.
      So, we'll get the groups: [e1 e2] [e3 e4]
      But what if e4 commutes with e1 and e2?
      Doesn't it make more sense to instead yield [e1 e2 e4] [e3]?

      I _think_ if we move every effect to the earliest it could possibly be, implementing
      composiiton will be much easier.

      That is: if we are trying to compose: e1 e2 e3 e4 with an effect e5 that commutes with e3 and
      undoes e1, we want to get the resulting effect: e2 e3 e4 (or perhaps e2 e4 e3)..perhap

      The best way to think of compose might actually be to separate it into a sequencing step and
      then a simplification step. The sequencing is trivial (eff1 ++ eff2), but the simplification
      might be more easily defined than whatever it is I'm actually trying to write here.

      Simplification sketch:
      1. Use the current commuting groups procedure.

      2. Starting from the last group, for each effect, check if it commutes with everything in the
         immediately preceding group. If it does, move it to that group.

      After step 2, we should have each effect occuring as early as it possibly can. Then, we have
      to actually remove any effects that will invert one another. Namely, delrgn should cancel out
      any region-creating effects for the same region. That might be the only simplification.

      3. To do so, we should go through looking at each adjacent commuting group and remove both
         effects when we find a cancelling pair. I think this could make more things commute and so
         we might need to return to step 2 and continue iterating until we reach a fixed point.
      */
}
