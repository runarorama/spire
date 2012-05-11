package spire.math

/** Arbitrary-precision natural numbers. */
sealed class Nat(private val rep: Vector[Int]) {

  /** Converts this natural number to a byte array in big-endian byte-order. */
  def toBytes: Array[Byte] = {
    val bitLen =
      if (rep.length > 0)
        ((rep.length - 1) << 5) + (32 - Integer.numberOfLeadingZeros(rep(0)))
      else 1
    val byteLen = bitLen/8 + 1
    val byteArr = new Array[Byte](byteLen)
    def loop(i: Int, copied: Int, next: Int, index: Int): Array[Byte] =
      if (i < 0)
        byteArr
      else {
        if (copied == 4) {
          val ni = getInt(index)
          byteArr(i) = ni.toByte
          loop(i - 1, 1, ni, index + 1)
        } else {
          val ni = next >>> 8
          byteArr(i) = ni.toByte
          loop(i - 1, copied + 1, ni, index)
        }
      }
    loop(byteLen - 1, 4, 0, 0)
  }

  /** Gets the `n`th integer value in the little-endian representation of this natural. */
  private def getInt(n: Int): Int =
    if (n >= rep.length) 0 else rep(rep.length - n - 1)

  /** Converts this natural number to a `Long`. */
  def toLong = {
    def loop(res: Long, i: Int): Long =
      if (i >= 0)
        loop((res << 32) + (getInt(i) & Nat.LONG_MASK), i - 1)
      else res
    loop(0, 1)
  }
}

object Nat {
  /** A natural number from an integer. The `Int` is treated as if it were unsigned. */
  def fromInt(n: Int): Nat = build(Vector(n))

  /** 
   * Constructs a natural number from the binary representation.
   * The array is assumed to be in big-endian int-order with the
   * most significant integer first.
   */
  private def build(rep: Vector[Int]): Nat = {
    val vlen = rep.length
    def loop(keep: Int): Vector[Int] =
      if (keep < vlen && rep(keep) == 0)
        loop(keep + 1)
      else if (keep == 0) rep else
        rep.drop(keep).take(vlen)
    new Nat(loop(0))
  }

  private val LONG_MASK = 0xffffffffL
}

