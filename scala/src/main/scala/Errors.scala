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

  case class IllegalBorrow(
    needed: Fraction, had: Fraction, rgn: Region
  ) extends RuntimeException(
    s"Region $rgn could not be borrowed. A $needed capability was needed, but we only had $had."
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

  case object Unreachable extends RuntimeException(
    "This point in the program should've been unreachable."
  )
}
