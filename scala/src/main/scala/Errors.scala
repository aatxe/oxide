package oxide

import Syntax._

object Errors {
  case class RegionAlreadyInUse(rgn: RConcrete, ctx: RegionContext) extends RuntimeException(
    s"Region $rgn was already in use in $ctx."
  )
}
