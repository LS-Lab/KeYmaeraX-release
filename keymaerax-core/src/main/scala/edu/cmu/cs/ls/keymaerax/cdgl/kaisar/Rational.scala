// Pared down version of spire BigRational type per MIT license
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import java.math.RoundingMode

import scala.math.BigInt

case class Rational (n: BigInt, d: BigInt) {
  def numerator: BigInt = n

  def denominator: BigInt = d

  def numeratorAsLong: Long = n.toLong

  def numeratorIsValidLong: Boolean = n.isValidLong

  def numeratorAbsIsValidLong: Boolean = n.isValidLong && (n.toLong != Long.MinValue)

  def denominatorAsLong: Long = d.toLong

  def denominatorIsValidLong: Boolean = d.isValidLong

  def denominatorAbsIsValidLong: Boolean = d.isValidLong && (d.toLong != Long.MinValue)

  def reciprocal: Rational = if (signum < 0)
    Rational(-d, -n)
  else
    Rational(d, n)

  def signum: Int = n.signum

  def isWhole: Boolean = d == 1

  def isZero: Boolean = false

  def isOne: Boolean = false

  def isValidChar: Boolean = false

  def isValidByte: Boolean = false

  def isValidShort: Boolean = false

  def isValidInt: Boolean = false

  def isValidLong: Boolean = false

  def toBigInt: BigInt = n / d

  //def doubleValue: Double = Rational.toDouble(n, d)

  def unary_- : Rational = Rational(-n, d)

  def +(r: Rational): Rational = {
    val dgcd: BigInt = d.gcd(r.d)
    if (dgcd == 1) {
      Rational(r.d * n + r.n * d, r.d * d)
    } else {
      val lden: BigInt = d / dgcd
      val rden: BigInt = r.d / dgcd
      val num: BigInt = rden * n + r.n * lden
      val ngcd: BigInt = num.gcd(dgcd)
      if (ngcd == 1)
        Rational(num, lden * r.d)
      else
        Rational(num / ngcd, (r.d / ngcd) * lden)
    }
  }

  def -(r: Rational): Rational = {
    val dgcd: BigInt = d.gcd(r.d)
    if (dgcd == 1) {
      Rational(r.d * n - r.n * d, r.d * d)
    } else {
      val lden: BigInt = d / dgcd
      val rden: BigInt = r.d / dgcd
      val num: BigInt = rden * n - r.n * lden
      val ngcd: BigInt = num.gcd(dgcd)
      if (ngcd == 1)
        Rational(num, lden * r.d)
      else
        Rational(num / ngcd, (r.d / ngcd) * lden)
    }
  }

  def *(r: Rational): Rational = {
    val a = n.gcd(r.d)
    val b = d.gcd(r.n)
    Rational((n / a) * (r.n / b), (d / b) * (r.d / a))
  }


  def /(r: Rational): Rational = {
      val a = n.gcd(r.n)
      val b = d.gcd(r.d)
      val num = (n / a) * (r.d / b)
      val den = (d / b) * (r.n / a)
      if (den.signum < 0) Rational(-num, -den) else Rational(num, den)
  }

  def floor: Rational =
    if (isWhole) this
    else if (n.signum >= 0) Rational(n / d, BigInt(1))
    else Rational(n / d - 1, BigInt(1))

  def ceil: Rational =
    if (isWhole) this
    else if (n.signum >= 0) Rational(n / d + 1, BigInt(1))
    else Rational(n / d, BigInt(1))

  def round: Rational =
    if (n.signum >= 0) {
      val m = n % d
      if (m >= (d - m)) Rational(n , d + 1) else Rational(n , d)
    } else {
      val m = -(n % d)
      if (m >= (d - m)) Rational(n , d - 1) else Rational(n , d)
    }

  def pow(exp: Int): Rational = if (exp == 0)
    Rational(1, 1)
  else if (exp < 0)
    Rational(d pow -exp, n pow -exp)
  else
    Rational(n pow exp, d pow exp)

  def compareToOne: Int = n compare d

  def compare(r: Rational): Int = {
    val dgcd = d.gcd(r.d)
    if (dgcd == 1)
      (n * r.d) compare (r.n * d)
    else
      ((r.d / dgcd) * n) compare ((d / dgcd) * r.n)
  }

  override def equals(that: Any): Boolean = that match {
    case that: Rational => this.n == that.n && this.d == that.d
    case _ => super.equals(that)
  }

  override def hashCode: Int =
    29 * (37 * n.## + d.##)

  override def toString: String = if (isWhole) n.toString else s"$n/$d"

  def <(rhs: Rational): Boolean = compare(rhs) < 0
  def <=(rhs: Rational): Boolean = compare(rhs) <= 0
  def >(rhs: Rational): Boolean = compare(rhs) > 0
  def >=(rhs: Rational): Boolean = compare(rhs) >= 0

  def toInt: Int = (n / d).toInt

  def max(rhs: Rational): Rational = if (this >= rhs) this else rhs
  def min(rhs: Rational): Rational = if (this <= rhs) this else rhs
  def abs: Rational = if (this <= Rational(0,1)) -this else this

  def toBigDecimal(scale: Int, mode: RoundingMode): BigDecimal = {
    val n = new java.math.BigDecimal(numerator.bigInteger)
    val d = new java.math.BigDecimal(denominator.bigInteger)
    BigDecimal(n.divide(d, scale, mode))
  }

  val SCALE = 10
  val RND_MODE = RoundingMode.HALF_DOWN
  def ratPow(num: Int, denom: Int): Rational = {
    val pow = num.toDouble / denom.toDouble
    val db = math.pow(toBigDecimal(SCALE, RND_MODE).toDouble, pow)
    Rational(BigDecimal(db))
  }  //.nroot(denom).pow(numAbs)
}

object Rational {
  def apply(x: BigDecimal): Rational = {
    if (x.ulp >= 1) {
      apply(x.toBigInt, 1)
    } else {
      val n = (x / x.ulp).toBigInt
      val d = (BigDecimal(1.0) / x.ulp).toBigInt
      apply(n, d)
    }
  }
}

//  private def Rational(n: BigInt, d: BigInt): Rational = new Rational(n, if(d.isOne) BigInt.one else d)
//}
  /*
  def +(rhs: Rational): Rational = Rational(n + rhs.n)
  def -(rhs: Rational): Rational = Rational(n - rhs.n)
  def *(rhs: Rational): Rational = Rational(n * rhs.n)
  def /(rhs: Rational): Rational = Rational(n / rhs.n)
  def pow(num: Int, denom: Int): Rational = {
  def unary_- : Rational = Rational(-n)
  def eq(other: Rational): Boolean = (n == other.n)
  def diseq(other: Rational): Boolean = (n != other.n)
  def intApprox: Int = n.toInt

}
*/