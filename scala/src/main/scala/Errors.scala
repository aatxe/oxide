package oxide

import Syntax._

object Errors {
  case class RegionAlreadyInUse(rgn: RConcrete, ctx: RegionContext) extends RuntimeException(
    s"Region $rgn was already in use in $ctx."
  )

  case class TypeError(expected: Type, found: Type) extends RuntimeException(
    s"""A type error occurred.

        Expected: $expected

        Found: $found"""
  )

  case class InsufficientCapability(
    needed: Fraction, had: Fraction, rgn: Region
  ) extends RuntimeException(
    s"Using $rgn: needed $needed capability, but only had $had."
  )

  case class UnexpectedMetadata(
    found: Metadata, expected: Metadata, rgn: Region
  ) extends RuntimeException(
    s"""Region $rgn had unexpected metadata.

        Expected: $expected

        Found: $found"""
  )

  case class UnboundIdentifier(id: Identifier) extends RuntimeException(
    s"Attempted to use unbound identifier: $id"
  )

  case class UnboundRegion(rgn: Region) extends RuntimeException(
    s"Attempted to use unbound region: $rgn"
  )

  case class BadAggregateFree(
    aggregate: Region, path: ImmediatePath, unfreedRegion: Region
  ) extends RuntimeException(
    s"Cannot free aggregate region $aggregate, region $unfreedRegion was left unfreed at $path."
  )

  case object Unreachable extends RuntimeException(
    "This point in the program should've been unreachable."
  )
}
