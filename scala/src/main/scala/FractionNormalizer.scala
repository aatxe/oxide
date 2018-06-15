package oxide

import Syntax._

object FractionNormalizer {
  val cache: scala.collection.mutable.Map[Fraction, Fraction] = scala.collection.mutable.Map()

  def normalize(fraction: Fraction): Fraction = cache.get(fraction) match {
    case Some(norm) => norm
    case None => {
      cache += fraction -> normalizeImpl(fraction)
      cache(fraction)
    }
  }

  // In general, this may not simplify enough, but it should work fine for now.
  private def normalizeImpl(fraction: Fraction): Fraction = fraction match {
    case FZeta | FNum(_) => fraction
    case FAdd(f1, f2) => (normalize(f1), normalize(f2)) match {
      // FIXME: this match is non-exhaustive
      case (FNum(n1), FNum(n2)) => FNum(n1 + n2)
      case (FDiv(n1, FNum(d1)), FDiv(n2, FNum(d2))) if d1 == d2 =>
        normalize(FDiv(FAdd(n1, n2), FNum(d1)))
      case (FDiv(FNum(n1), FNum(d1)), FDiv(FNum(n2), FNum(d2))) =>
        normalize(
          FAdd(FDiv(FNum(n1 * d2), FNum(d1 * d2)),
               FDiv(FNum(n2 * d1), FNum(d1 * d2)))
        )
      case (FZeta, f2) => FAdd(FZeta, normalize(f2))
      case (f1, FZeta) => FAdd(FZeta, normalize(f1))
    }
    case FDiv(FNum(0), _) => FNum(0)
    case FDiv(FNum(n), FNum(1)) => FNum(n)
    case FDiv(FNum(n), FNum(d)) => {
      val gcd = BigInt(n).gcd(BigInt(d)).intValue
      def proc(x: Fraction) = if (gcd == 1) identity(x) else normalize(x)
      proc(FDiv(FNum(n / gcd), FNum(d / gcd)))
    }
    case FDiv(FDiv(num, FNum(d1)), FNum(d2)) => normalize(FDiv(num, FNum(d1 * d2)))
    case FDiv(num, denom) => normalize(FDiv(normalize(num), normalize(denom)))
  }
}
