/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

/*
 * Collection of the primitive types for IR.
 */
private[genc] object PrimitiveTypes {

  sealed abstract class PrimitiveType {
    def isLogical: Boolean = this match {
      case BoolType => true
      case _ => false
    }

    def isIntegral: Boolean = this match {
      case _: IntegralPrimitiveType => true
      case _ => false
    }
  }

  sealed abstract class IntegralPrimitiveType extends PrimitiveType {
    def isSigned: Boolean =
      this == Int8Type ||
      this == Int16Type ||
      this == Int32Type ||
      this == Int64Type

    def isUnsigned: Boolean =
      this == UInt8Type ||
      this == UInt16Type ||
      this == UInt32Type ||
      this == UInt64Type

    def toUnsigned: IntegralPrimitiveType = this match {
      case Int8Type => UInt8Type
      case Int16Type => UInt16Type
      case Int32Type => UInt32Type
      case Int64Type => UInt64Type
      case _ => sys.error(s"cannot invoke toUnsigned on $this")
    }
  }

  sealed trait SizedPrimitiveType extends PrimitiveType {
    def byteSize: Int = this match {
      case CharType | BoolType | Int8Type | UInt8Type => 1
      case Int16Type | UInt16Type => 2
      case Int32Type | UInt32Type => 4
      case Int64Type | UInt64Type => 8
    }
  }

  case object CharType extends IntegralPrimitiveType with SizedPrimitiveType
  case object Int8Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object Int16Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object Int32Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object Int64Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object UInt8Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object UInt16Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object UInt32Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object UInt64Type extends IntegralPrimitiveType with SizedPrimitiveType
  case object BoolType extends PrimitiveType with SizedPrimitiveType
  case object UnitType extends PrimitiveType
  case object StringType extends PrimitiveType

}
