package oxide

import Syntax._

object Effects {
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

  def commutingGroups(eff: Effects): Seq[Set[Effect]] =
    eff.foldLeft[Seq[Set[Effect]]](Seq(Set())) {
      case (groups :+ latestGroup, eff) if latestGroup.forall(commutes(_, eff)) =>
        groups :+ (latestGroup + eff)
      case (groups, eff) => groups :+ Set(eff)
    }

  def compose(eff1: Effects, eff2: Effects): Effects = ???
}
