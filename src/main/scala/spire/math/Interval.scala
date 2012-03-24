package spire.math

import Implicits._

sealed trait Bound[T] {
  implicit def order:Order[T]

  def toUpper:Upper[T]
  def toLower:Lower[T]

  def compare(rhs:Bound[T]):Int
  def comparePt(t:T):Int

  def unop(f:T => T):Bound[T]
  def binop(rhs:Bound[T])(f:(T, T) => T):Bound[T]

  def <(rhs:Bound[T]) = compare(rhs) < 0
  def <=(rhs:Bound[T]) = compare(rhs) < 1
  def >(rhs:Bound[T]) = compare(rhs) > 0
  def >=(rhs:Bound[T]) = compare(rhs) > -1

  def min(rhs:Bound[T]):Bound[T] = if (this < rhs) this else rhs
  def max(rhs:Bound[T]):Bound[T] = if (this > rhs) this else rhs
}

class BoundRingOps[T:Ring](lhs:Bound[T]) {
  def abs = lhs.unop(_.abs)
  def unary_- = lhs.unop(-_)
  def +(rhs:T) = lhs.unop(_ + rhs)
  def -(rhs:T) = lhs.unop(_ - rhs)
  def *(rhs:T) = lhs.unop(_ * rhs)
  def +(rhs:Bound[T]) = lhs.binop(rhs)(_ + _)
  def -(rhs:Bound[T]) = lhs.binop(rhs)(_ - _)
  def *(rhs:Bound[T]) = lhs.binop(rhs)(_ * _)
  def pow(rhs:Int) = lhs.unop(_ pow rhs)
}

class BoundEuclideanRingOps[T:EuclideanRing](lhs:Bound[T]) {
  def /~(rhs:T) = lhs.unop(_ /~ rhs)
  def /~(rhs:Bound[T]) = lhs.binop(rhs)(_ /~ _)
}

class BoundFieldOps[T:Field](lhs:Bound[T]) {
  def /(rhs:T) = lhs.unop(_ / rhs)
  def /(rhs:Bound[T]) = lhs.binop(rhs)(_ / _)
}

trait Lower[T] extends Bound[T] { def toLower = this }
trait Upper[T] extends Bound[T] { def toUpper = this }

trait Unbound[T] extends Bound[T] {
  def unop(f:T => T):Bound[T] = this
  def binop(rhs:Bound[T])(f:(T, T) => T):Bound[T] = this
}

case class UnboundBelow[T]()(implicit val order:Order[T]) extends Lower[T] with Unbound[T] {
  def compare(rhs:Bound[T]) = rhs match {
    case UnboundBelow() => 0
    case _ => -1
  }
  def comparePt(t:T) = -1
  def toUpper = UnboundAbove[T]
}

case class UnboundAbove[T]()(implicit val order:Order[T]) extends Upper[T] with Unbound[T] {
  def compare(rhs:Bound[T]) = rhs match {
    case UnboundAbove() => 0
    case _ => 1
  }
  def comparePt(t:T) = 1
  def toLower = UnboundBelow[T]
}

trait Closed[T] {
  implicit def order:Order[T]
  def x:T
  def compare(rhs:Bound[T]) = rhs match {
    case UnboundBelow() => 1
    case UnboundAbove() => -1
    case ClosedBelow(y) => x cmp y
    case ClosedAbove(y) => x cmp y
    case OpenBelow(y) => if (x <= y) -1 else 1
    case OpenAbove(y) => if (x < y) -1 else 1
  }
  def comparePt(t:T) = x cmp t
  def binop(rhs:Bound[T])(f:(T, T) => T):Bound[T] = rhs match {
    case UnboundBelow() => UnboundBelow()
    case UnboundAbove() => UnboundBelow()
    case OpenBelow(y) => OpenBelow(f(x, y))
    case OpenAbove(y) => OpenBelow(f(x, y))
    case ClosedBelow(y) => ClosedBelow(f(x, y))
    case ClosedAbove(y) => ClosedBelow(f(x, y))
  }
}

case class ClosedBelow[T](x:T)(implicit val order:Order[T]) extends Lower[T] with Closed[T] {
  def toUpper = ClosedAbove(x)
  def unop(f:T => T) = ClosedBelow(f(x))
  override def binop(rhs:Bound[T])(f:(T, T) => T):Lower[T] = super.binop(rhs)(f).toLower
}

case class ClosedAbove[T](x:T)(implicit val order:Order[T]) extends Upper[T] with Closed[T] {
  def toLower = ClosedBelow(x)
  def unop(f:T => T) = ClosedAbove(f(x))
  override def binop(rhs:Bound[T])(f:(T, T) => T):Upper[T] = super.binop(rhs)(f).toUpper
}

trait Open[T] {
  implicit def order:Order[T]
  def x:T
  def binop(rhs:Bound[T])(f:(T, T) => T):Bound[T] = rhs match {
    case UnboundBelow() => UnboundBelow()
    case UnboundAbove() => UnboundBelow()
    case OpenBelow(y) => OpenBelow(f(x, y))
    case OpenAbove(y) => OpenBelow(f(x, y))
    case ClosedBelow(y) => OpenBelow(f(x, y))
    case ClosedAbove(y) => OpenBelow(f(x, y))
  }
}

case class OpenBelow[T](x:T)(implicit val order:Order[T]) extends Lower[T] with Open[T] {
  def compare(rhs:Bound[T]) = rhs match {
    case UnboundBelow() => 1
    case UnboundAbove() => -1
    case ClosedBelow(y) => if (x < y) -1 else 1
    case ClosedAbove(y) => if (x < y) -1 else 1
    case OpenBelow(y) => x cmp y
    case OpenAbove(y) => if (x < y) -1 else 1
  }
  def comparePt(t:T) = if (x < t) -1 else 1
  def toUpper = OpenAbove(x)
  def unop(f:T => T) = OpenBelow(f(x))
  override def binop(rhs:Bound[T])(f:(T, T) => T):Lower[T] = super.binop(rhs)(f).toLower
}

case class OpenAbove[T](x:T)(implicit val order:Order[T]) extends Upper[T] with Open[T] {
  def compare(rhs:Bound[T]) = rhs match {
    case UnboundBelow() => 1
    case UnboundAbove() => -1
    case ClosedBelow(y) => if (x <= y) -1 else 1
    case ClosedAbove(y) => if (x <= y) -1 else 1
    case OpenBelow(y) => if (x <= y) -1 else 1
    case OpenAbove(y) => x cmp y
  }
  def comparePt(t:T) = if (x <= t) -1 else 1
  def toLower = OpenBelow(x)
  def unop(f:T => T) = OpenAbove(f(x))
  override def binop(rhs:Bound[T])(f:(T, T) => T):Upper[T] = super.binop(rhs)(f).toUpper
}

object ContinuousInterval {
  def apply[T:Order](lower:Lower[T], upper:Upper[T]) = Interval(lower, upper)
}

case class Interval[T](lower:Lower[T], upper:Upper[T])(implicit val order:Order[T]) {
  protected[math] def coerce(a:Bound[T], b:Bound[T]) = Interval(a.toLower, b.toUpper)

  def isAbove(t:T) = 0 < lower.comparePt(t)
  def isBelow(t:T) = upper.comparePt(t) < 0
  def isAt(t:T) = lower.comparePt(t) == 0 && 0 == upper.comparePt(t)
  def contains(t:T) = lower.comparePt(t) <= 0 && 0 <= upper.comparePt(t)
  def crosses(t:T) = lower.comparePt(t) < 0 && 0 < upper.comparePt(t)

  def mask(rhs:Interval[T]):Interval[T] = coerce(lower max rhs.lower, upper min rhs.upper)

  def split(t:T):(Interval[T], Interval[T]) = {
    val below = coerce(UnboundBelow[T], OpenAbove(t))
    val above = coerce(OpenBelow(t), UnboundAbove[T])
    (this mask below, this mask above)
  }
}

object Interval {
  implicit def ringIntervalOps[T:Ring:Order](i:Interval[T]) = new RingIntervalOps(i)
  implicit def euclideanRingIntervalOps[T:EuclideanRing](i:Interval[T]) = new EuclideanRingIntervalOps(i)
  implicit def fieldIntervalOps[T:Field](i:Interval[T]) = new FieldIntervalOps(i)
}

final class RingIntervalOps[T](lhs:Interval[T])(implicit num:Ring[T], o:Order[T]) {

  implicit def boundRingOps(b:Bound[T]) = new BoundRingOps(b)

  def splitAtZero = lhs.split(num.zero)

  def abs = {
    val a = lhs.lower.abs
    val b = lhs.upper.abs
    if (lhs.crosses(num.zero)) lhs.coerce(ClosedBelow(num.zero), a max b)
    else if (a < b) lhs.coerce(a, b)
    else lhs.coerce(b, a)
  }
  
  def unary_- = lhs.coerce(-lhs.upper, -lhs.lower)
  
  def +(rhs:Interval[T]):Interval[T] = lhs.coerce(lhs.lower + rhs.lower, lhs.upper + rhs.upper)
  def +(rhs:T):Interval[T] = lhs.coerce(lhs.lower + rhs, lhs.upper + rhs)
  
  def -(rhs:Interval[T]):Interval[T] = lhs.coerce(lhs.lower - rhs.upper, lhs.upper - rhs.lower)
  def -(rhs:T):Interval[T] = lhs.coerce(lhs.lower - rhs, lhs.upper - rhs)
  
  def *(rhs:Interval[T]):Interval[T] = {
    val tcz = lhs.crosses(num.zero)
    val rcz = rhs.crosses(num.zero)
  
    val ll = lhs.lower * rhs.lower
    val lu = lhs.lower * rhs.upper
    val ul = lhs.upper * rhs.lower
    val uu = lhs.upper * rhs.upper
  
    if (tcz && rcz) {
      lhs.coerce(lu min ul, ll max uu)
    } else if (tcz) {
      lhs.coerce(ll min lu, ul max uu)
    } else if (rcz) {
      lhs.coerce(ll min ul, lu max uu)
    } else if (lhs.isBelow(num.zero) == rhs.isBelow(num.zero)) {
      lhs.coerce(ll min uu, ll max uu)
    } else {
      lhs.coerce(lu min ul, lu max ul)
    }
  }
  def *(rhs:T):Interval[T] = {
    val a = lhs.lower * rhs
    val b = lhs.upper * rhs
    if (a < b) lhs.coerce(a, b) else lhs.coerce(b, a)
  }

  def pow(rhs:Int):Interval[T] = {
    val a = lhs.lower pow rhs
    val b = lhs.upper pow rhs
  
    if (lhs.contains(num.zero) && rhs % 2 == 0) {
      lhs.coerce(ClosedBelow(num.zero), a max b)
    } else {
      if (a < b) lhs.coerce(a, b) else lhs.coerce(b, a)
    }
  }
}

final class EuclideanRingIntervalOps[T](lhs:Interval[T])(implicit num:EuclideanRing[T]) {

  implicit def boundEuclideanRingOps(b:Bound[T]) = new BoundEuclideanRingOps(b)

  def /~(rhs:Interval[T]):Interval[T] = {
    if (rhs.contains(num.zero)) sys.error("divide-by-zero possible")

    val ll = lhs.lower /~ rhs.lower
    val lu = lhs.lower /~ rhs.upper
    val ul = lhs.upper /~ rhs.lower
    val uu = lhs.upper /~ rhs.upper

    val bz = rhs.isBelow(num.zero)

    if (lhs.crosses(num.zero)) {
      if (bz) lhs.coerce(uu, lu) else lhs.coerce(ll, ul)
    } else if (lhs.isAbove(num.zero)) {
      if (bz) lhs.coerce(uu, ll) else lhs.coerce(lu, ul)
    } else {
      if (bz) lhs.coerce(ul, lu) else lhs.coerce(ll, uu)
    }
  }
  def /~(rhs:T) = {
    val a = lhs.lower /~ rhs
    val b = lhs.upper /~ rhs
    if (a < b) lhs.coerce(a, b) else lhs.coerce(b, a)
  }
}

final class FieldIntervalOps[T](lhs:Interval[T])(implicit num:Field[T]) {

  implicit def boundFieldOps(b:Bound[T]) = new BoundFieldOps(b)

  def /(rhs:Interval[T]):Interval[T] = {
    if (rhs.contains(num.zero)) sys.error("divide-by-zero possible")

    val ll = lhs.lower / rhs.lower
    val lu = lhs.lower / rhs.upper
    val ul = lhs.upper / rhs.lower
    val uu = lhs.upper / rhs.upper

    val bz = rhs.isBelow(num.zero)

    if (lhs.crosses(num.zero)) {
      if (bz) lhs.coerce(uu, lu) else lhs.coerce(ll, ul)
    } else if (lhs.isAbove(num.zero)) {
      if (bz) lhs.coerce(uu, ll) else lhs.coerce(lu, ul)
    } else {
      if (bz) lhs.coerce(ul, lu) else lhs.coerce(ll, uu)
    }
  }
  def /(rhs:T) = {
    val a = lhs.lower / rhs
    val b = lhs.upper / rhs
    if (a < b) lhs.coerce(a, b) else lhs.coerce(b, a)
  }
}

//case class Interval[T](lower:Lower[T], upper:Upper[T])(implicit val order:Order[T])
//extends GenInterval[T, Interval[T]] {
//  protected[this] def coerce(a:Bound[T], b:Bound[T]) = Interval(a.toLower, b.toUpper)
//}
//
//case class RingInterval[T](lower:Lower[T], upper:Upper[T])(implicit val order:Order[T], val num:Ring[T])
//extends GenRingInterval[T, RingInterval[T]] {
//  protected[this] def coerce(a:Bound[T], b:Bound[T]) = RingInterval(a.toLower, b.toUpper)
//}
//
//case class DiscreteInterval[T](lower:Lower[T], upper:Upper[T])(implicit f:Integral[T])
//extends GenDiscreteInterval[T, DiscreteInterval[T]] {
//  implicit def num:EuclideanRing[T] = f
//  implicit def order:Order[T] = f
//  protected[this] def coerce(a:Bound[T], b:Bound[T]) = DiscreteInterval(a.toLower, b.toUpper)
//}
//
//case class ContinuousInterval[T](lower:Lower[T], upper:Upper[T])(implicit f:Fractional[T])
//extends GenContinuousInterval[T, ContinuousInterval[T]] {
//  implicit def num:Field[T] = f
//  implicit def order:Order[T] = f
//  protected[this] def coerce(a:Bound[T], b:Bound[T]) = ContinuousInterval(a.toLower, b.toUpper)
//}
