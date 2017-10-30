package pt.lib

import pt.lib._
import pt.lib.Scratch.myvars
import pt.lib.Sum_Type._

object Failure {
  def fail[T]():T = {
    throw new Exception ("Raised error during proofchecking")
  }
}



object Countable {

  trait countable[A] {
  }
  object countable {
    implicit def `Quickcheck_Exhaustive.countable_unit`: countable[Unit] = new
        countable[Unit] {
    }
    implicit def `Scratch.countable_myvars`: countable[Scratch.myvars] = new
        countable[Scratch.myvars] {
    }
    implicit def
    `Quickcheck_Exhaustive.countable_sum`[A : countable, B : countable]:
    countable[Sum_Type.sum[A, B]]
    = new countable[Sum_Type.sum[A, B]] {
    }
  }

} /* object Countable */

object Orderings {

  trait ord[A] {
    val `Orderings.less_eq`: (A, A) => Boolean
    val `Orderings.less`: (A, A) => Boolean
  }
  def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
    A.`Orderings.less_eq`(a, b)
  def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
  object ord {
    implicit def `Code_Numeral.ord_integer`: ord[BigInt] = new ord[BigInt] {
      val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
      val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
    }
  }

  def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

} /* object Orderings */

object Num {

  abstract sealed class num
  final case class One() extends num
  final case class Bit0(a: num) extends num
  final case class Bit1(a: num) extends num

  def length(n:num):Int = n match {
    case One() => 1
    case Bit0(a) => 1 + length(a)
    case Bit1(a) => 1 + length(a)
  }

  def exp(n:Int,m:Int):Int = (n,m) match {
    case (_,0) => 1
    case (n,m) => n*exp(n,m-1)
  }

  def toInt(n:num):Int = n match {
    case One() => 1
    case Bit0(a) => 2 * toInt(a)
    case Bit1(a) => 1 + 2 * toInt(a)
  }

} /* object Num */
object Enum {

  trait enum[A] extends Finite_Set.finite[A] {
    val `Enum.enum`: List[A]
    val `Enum.enum_all`: (A => Boolean) => Boolean
    val `Enum.enum_ex`: (A => Boolean) => Boolean
  }
  def enum[A](implicit A: enum[A]): List[A] = A.`Enum.enum`
  def enum_all[A](a: A => Boolean)(implicit A: enum[A]): Boolean =
    A.`Enum.enum_all`(a)
  def enum_ex[A](a: A => Boolean)(implicit A: enum[A]): Boolean =
    A.`Enum.enum_ex`(a)
  object enum {
    implicit def `Enum.enum_unit`: enum[Unit] = new enum[Unit] {
      val `Enum.enum` = enum_unita
      val `Enum.enum_all` = (a: Unit => Boolean) => enum_all_unit(a)
      val `Enum.enum_ex` = (a: Unit => Boolean) => enum_ex_unit(a)
    }
    /*implicit def `Scratch.enum_myvars`: enum[Scratch.myvars] = new
        enum[Scratch.myvars] {
      val `Enum.enum` = Scratch.enum_myvarsa
      val `Enum.enum_all` = (a: Scratch.myvars => Boolean) =>
        Scratch.enum_all_myvars(a)
      val `Enum.enum_ex` = (a: Scratch.myvars => Boolean) =>
        Scratch.enum_ex_myvars(a)
    }*/
    implicit def `Enum.enum_sum`[A : enum, B : enum]: enum[Sum_Type.sum[A, B]] =
      new enum[Sum_Type.sum[A, B]] {
        val `Enum.enum` = enum_suma[A, B]
        val `Enum.enum_all` = (a: (Sum_Type.sum[A, B]) => Boolean) =>
          enum_all_sum[A, B](a)
        val `Enum.enum_ex` = (a: (Sum_Type.sum[A, B]) => Boolean) =>
          enum_ex_sum[A, B](a)
      }
  }

  def equal_funa[A : enum, B : HOL.equal](f: A => B, g: A => B): Boolean =
    enum_all[A](((x: A) => HOL.eq[B](f(x), g(x))))

  def enum_all_sum[A : enum, B : enum](p: (Sum_Type.sum[A, B]) => Boolean):
  Boolean
  =
    enum_all[A](((x: A) => p(Sum_Type.Inl[A, B](x)))) &&
      enum_all[B](((x: B) => p(Sum_Type.Inr[B, A](x))))

  def enum_ex_sum[A : enum, B : enum](p: (Sum_Type.sum[A, B]) => Boolean): Boolean
  =
    enum_ex[A](((x: A) => p(Sum_Type.Inl[A, B](x)))) ||
      enum_ex[B](((x: B) => p(Sum_Type.Inr[B, A](x))))

  def enum_suma[A : enum, B : enum]: List[Sum_Type.sum[A, B]] =
    Lista.map[A, Sum_Type.sum[A, B]](((a: A) => Sum_Type.Inl[A, B](a)),
      enum[A]) ++
      Lista.map[B, Sum_Type.sum[A, B]](((a: B) => Sum_Type.Inr[B, A](a)), enum[B])

  def enum_all_unit(p: Unit => Boolean): Boolean = p(())

  def enum_ex_unit(p: Unit => Boolean): Boolean = p(())

  def enum_unita: List[Unit] = List(())

} /* object Enum */

object Finite_Set {

  trait finite[A] extends Countable.countable[A] {
  }
  object finite {
    implicit def `Finite_Set.finite_unit`: finite[Unit] = new finite[Unit] {
    }
    implicit def `Scratch.finite_myvars`: finite[Scratch.myvars] = new
        finite[Scratch.myvars] {
    }
    implicit def
    `Finite_Set.finite_sum`[A : finite, B : finite]: finite[Sum_Type.sum[A, B]]
    = new finite[Sum_Type.sum[A, B]] {
    }
  }

} /* object Finite_Set */

object Sum_Type {

  abstract sealed class sum[A, B]
  final case class Inl[A, B](a: A) extends sum[A, B]
  final case class Inr[B, A](a: B) extends sum[A, B]

  def equal_suma[A : HOL.equal, B : HOL.equal](x0: sum[A, B], x1: sum[A, B]):
  Boolean
  =
    (x0, x1) match {
      case (Inl(x1), Inr(x2)) => false
      case (Inr(x2), Inl(x1)) => false
      case (Inr(x2), Inr(y2)) => HOL.eq[B](x2, y2)
      case (Inl(x1), Inl(y1)) => HOL.eq[A](x1, y1)
    }

} /* object Sum_Type */

object Lista {

  def equal_lista[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
    case (Nil, x21 :: x22) => false
    case (x21 :: x22, Nil) => false
    case (x21 :: x22, y21 :: y22) =>
      HOL.eq[A](x21, y21) && equal_lista[A](x22, y22)
    case (Nil, Nil) => true
  }

  def nth[A](x0: List[A], n: Nat.nat): A = (x0, n) match {
    case (x :: xs, n) =>
      (if (Nat.equal_nat(n, Nat.zero_nat)) x
      else nth[A](xs, Nat.minus_nat(n, Nat.one_nat)))
  }

  def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
    case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
    case (f, Nil, s) => s
  }

  def nulla[A](x0: List[A]): Boolean = x0 match {
    case Nil => true
    case x :: xs => false
  }

  def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
    case (p, Nil) => Nil
    case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
  }

  def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
    case (Nil, y) => false
    case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
  }

  def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
    (if (member[A](xs, x)) xs else x :: xs)

  def list_ex[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
    case (p, Nil) => false
    case (p, x :: xs) => p(x) || list_ex[A](p, xs)
  }

  def remove1[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
    case (x, Nil) => Nil
    case (x, y :: xs) => (if (HOL.eq[A](x, y)) xs else y :: remove1[A](x, xs))
  }

  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil) => Nil
    case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
  }

  def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
    case (x, Nil) => Nil
    case (x, y :: xs) =>
      (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
  }

  def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
    case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
    case (n, Nil) => n
  }

  def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
    case (p, Nil) => true
    case (p, x :: xs) => p(x) && list_all[A](p, xs)
  }

  def size_list[A]: (List[A]) => Nat.nat =
    ((a: List[A]) => gen_length[A](Nat.zero_nat, a))

} /* object Lista */

object Nat {

  abstract sealed class nat
  final case class Nata(a: BigInt) extends nat

  def plus_nat(m: nat, n: nat): nat =
    Nata(Code_Numeral.integer_of_nat(m) + Code_Numeral.integer_of_nat(n))

  def one_nat: nat = Nata(BigInt(1))

  def Suc(n: nat): nat = plus_nat(n, one_nat)

  def less_nat(m: nat, n: nat): Boolean =
    Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

  def zero_nat: nat = Nata(BigInt(0))

  def equal_nat(m: nat, n: nat): Boolean =
    Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

  def minus_nat(m: nat, n: nat): nat =
    Nata(Orderings.max[BigInt](BigInt(0),
      Code_Numeral.integer_of_nat(m) -
        Code_Numeral.integer_of_nat(n)))

  def less_eq_nat(m: nat, n: nat): Boolean =
    Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)

} /* object Nat */

object Code_Numeral {

  def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
    case Nat.Nata(x) => x
  }

  def integer_of_int(x0: Int.int): BigInt = x0 match {
    case Int.int_of_integer(k) => k
  }

} /* object Code_Numeral */


object Int {

  abstract sealed class int
  final case class int_of_integer(a: BigInt) extends int

  def equal_inta(k: int, l: int): Boolean =
    Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

  def one_int: int = int_of_integer(BigInt(1))

  def zero_int: int = int_of_integer(BigInt(0))

  def uminus_int(k: int): int =
    int_of_integer((- (Code_Numeral.integer_of_int(k))))

} /* object Int */

object HOL {

  trait equal[A] {
    val `HOL.equal`: (A, A) => Boolean
  }
  def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
  object equal {
    implicit def `Product_Type.equal_unit`: equal[Unit] = new equal[Unit] {
      val `HOL.equal` = (a: Unit, b: Unit) => Product_Type.equal_unita(a, b)
    }
    implicit def
    `Syntax.equal_formula`[A : equal, B : equal, C : Enum.enum : equal]:
    equal[Syntax.formula[A, B, C]]
    = new equal[Syntax.formula[A, B, C]] {
      val `HOL.equal` = (a: Syntax.formula[A, B, C], b: Syntax.formula[A, B, C])
      => (a == b)
    }
    implicit def `Scratch.equal_myvars`: equal[Scratch.myvars] = new
        equal[Scratch.myvars] {
      val `HOL.equal` = (a: Scratch.myvars, b: Scratch.myvars) =>
        (a == b)
    }
    implicit def `Optiona.equal_option`[A : equal]: equal[Option[A]] = new
        equal[Option[A]] {
      val `HOL.equal` = (a: Option[A], b: Option[A]) =>
        Optiona.equal_optiona[A](a, b)
    }
    implicit def
    `Sum_Type.equal_sum`[A : equal, B : equal]: equal[Sum_Type.sum[A, B]] = new
        equal[Sum_Type.sum[A, B]] {
      val `HOL.equal` = (a: Sum_Type.sum[A, B], b: Sum_Type.sum[A, B]) =>
        Sum_Type.equal_suma[A, B](a, b)
    }
    implicit def
    `Syntax.equal_trm`[A : equal, B : Enum.enum : equal]:
    equal[Syntax.trm[A, B]]
    = new equal[Syntax.trm[A, B]] {
      val `HOL.equal` = (a: Syntax.trm[A, B], b: Syntax.trm[A, B]) =>
        (a == b)
    }
    implicit def `Lista.equal_list`[A : equal]: equal[List[A]] = new
        equal[List[A]] {
      val `HOL.equal` = (a: List[A], b: List[A]) => Lista.equal_lista[A](a, b)
    }
    implicit def `Set.equal_set`[A : equal]: equal[Set.set[A]] = new
        equal[Set.set[A]] {
      val `HOL.equal` = (a: Set.set[A], b: Set.set[A]) => Set.equal_seta[A](a, b)
    }
    implicit def `Int.equal_int`: equal[Int.int] = new equal[Int.int] {
      val `HOL.equal` = (a: Int.int, b: Int.int) => Int.equal_inta(a, b)
    }
    implicit def `Enum.equal_fun`[A : Enum.enum, B : equal]: equal[A => B] = new
        equal[A => B] {
      val `HOL.equal` = (a: A => B, b: A => B) => Enum.equal_funa[A, B](a, b)
    }
  }

  def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

  def All[A : Enum.enum](p: A => Boolean): Boolean = Enum.enum_all[A](p)

} /* object HOL */

object Product_Type {

  def equal_unita(u: Unit, v: Unit): Boolean = true

  def fst[A, B](x0: (A, B)): A = x0 match {
    case (x1, x2) => x1
  }

  def snd[A, B](x0: (A, B)): B = x0 match {
    case (x1, x2) => x2
  }

  def equal_prod[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
    (x0, x1) match {
      case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
    }

} /* object Product_Type */

object Rat {

  abstract sealed class rat
  final case class Frct(a: (Int.int, Int.int)) extends rat

  def quotient_of(x0: rat): (Int.int, Int.int) = x0 match {
    case Frct(x) => x
  }

  def one_rat: rat = Frct((Int.one_int, Int.one_int))

  def zero_rat: rat = Frct((Int.zero_int, Int.one_int))

  def equal_rat(a: rat, b: rat): Boolean =
    Product_Type.equal_prod[Int.int, Int.int](quotient_of(a), quotient_of(b))

  def uminus_rat(p: rat): rat = Frct({
    val a: (Int.int, Int.int) = quotient_of(p)
    val (aa, b): (Int.int, Int.int) = a;
    (Int.uminus_int(aa), b)
  })

} /* object Rat */
object String {

  abstract sealed class char
  final case class zero_char() extends char
  final case class Char(a: Num.num) extends char {
    override def toString = Character.toString(((Num.toInt(a).toChar)))

  }

} /* object String */

object Set {

  abstract sealed class set[A]
  final case class seta[A](a: List[A]) extends set[A]
  final case class coset[A](a: List[A]) extends set[A]

  def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
    case (x, coset(xs)) => ! (Lista.member[A](xs, x))
    case (x, seta(xs)) => Lista.member[A](xs, x)
  }

  def less_eq_set[A : HOL.equal](a: set[A], b: set[A]): Boolean = (a, b) match {
    case (coset(xs), seta(ys)) =>
      (if (Lista.nulla[A](xs) && Lista.nulla[A](ys)) false
      else { sys.error("subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV");
        (((_: Unit) =>
          less_eq_set[A](coset[A](xs), seta[A](ys)))).apply(())
      })
    case (a, coset(ys)) => Lista.list_all[A](((y: A) => ! (member[A](y, a))), ys)
    case (seta(xs), b) => Lista.list_all[A](((x: A) => member[A](x, b)), xs)
  }

  def equal_seta[A : HOL.equal](a: set[A], b: set[A]): Boolean =
    less_eq_set[A](a, b) && less_eq_set[A](b, a)

  def image[A : Enum.enum : HOL.equal, B](f: A => B, x1: set[A]): set[B] = (f, x1)
  match {
    case (f, coset(xs)) =>
      seta[B](Lista.map[A, B](f, Lista.fold[A,
        List[A]](((a: A) => (b: List[A]) => Lista.remove1[A](a, b)), xs,
        Enum.enum[A])))
    case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
  }

  def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
    case (x, coset(xs)) => coset[A](Lista.removeAll[A](x, xs))
    case (x, seta(xs)) => seta[A](Lista.insert[A](x, xs))
  }

  def remove[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
    case (x, coset(xs)) => coset[A](Lista.insert[A](x, xs))
    case (x, seta(xs)) => seta[A](Lista.removeAll[A](x, xs))
  }

  def vimage[A : Enum.enum, B : HOL.equal](f: A => B, b: set[B]): set[A] =
    seta[A](Lista.filter[A](((x: A) => member[B](f(x), b)), Enum.enum[A]))

  def Collect[A : Enum.enum](p: A => Boolean): set[A] =
    seta[A](Lista.filter[A](p, Enum.enum[A]))

  def bot_set[A]: set[A] = seta[A](Nil)

  def inf_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
    case (a, coset(xs)) =>
      Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => remove[A](aa, b)), xs, a)
    case (a, seta(xs)) =>
      seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
  }

  def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
    case (coset(xs), a) =>
      coset[A](Lista.filter[A](((x: A) => ! (member[A](x, a))), xs))
    case (seta(xs), a) =>
      Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
  }

  def top_set[A]: set[A] = coset[A](Nil)

  def minus_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
    case (a, coset(xs)) =>
      seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
    case (a, seta(xs)) =>
      Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => remove[A](aa, b)), xs, a)
  }

  def uminus_set[A](x0: set[A]): set[A] = x0 match {
    case coset(xs) => seta[A](xs)
    case seta(xs) => coset[A](xs)
  }

} /* object Set */

object Real {

  abstract sealed class real
  final case class Ratreal(a: Rat.rat) extends real

  def one_real: real = Ratreal(Rat.one_rat)

  def zero_real: real = Ratreal(Rat.zero_rat)

  def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
    case (Ratreal(x), Ratreal(y)) => Rat.equal_rat(x, y)
  }

  def uminus_real(x0: real): real = x0 match {
    case Ratreal(x) => Ratreal(Rat.uminus_rat(x))
  }

} /* object Real */

object Predicate {

  abstract sealed class pred[A]
  final case class Seq[A](a: Unit => seq[A]) extends pred[A]

  abstract sealed class seq[A]
  final case class Empty[A]() extends seq[A]
  final case class Insert[A](a: A, b: pred[A]) extends seq[A]
  final case class Join[A](a: pred[A], b: seq[A]) extends seq[A]

  def applya[A, B](f: A => pred[B], x1: seq[A]): seq[B] = (f, x1) match {
    case (f, Empty()) => Empty[B]()
    case (f, Insert(x, p)) => Join[B](f(x), Join[B](bind[A, B](p, f), Empty[B]()))
    case (f, Join(p, xq)) => Join[B](bind[A, B](p, f), applya[A, B](f, xq))
  }

  def bind[A, B](x0: pred[A], f: A => pred[B]): pred[B] = (x0, f) match {
    case (Seq(g), f) => Seq[B](((_: Unit) => applya[A, B](f, g(()))))
  }

  def member[A : HOL.equal](xa0: seq[A], x: A): Boolean = (xa0, x) match {
    case (Empty(), x) => false
    case (Insert(y, p), x) => HOL.eq[A](x, y) || (eval[A](p)).apply(x)
    case (Join(p, xq), x) => (eval[A](p)).apply(x) || member[A](xq, x)
  }

  def eval[A : HOL.equal](x0: pred[A]): A => Boolean = x0 match {
    case Seq(f) => ((a: A) => member[A](f(()), a))
  }

  def holds(p: pred[Unit]): Boolean = (eval[Unit](p)).apply(())

  def bot_pred[A]: pred[A] = Seq[A](((_: Unit) => Empty[A]()))

  def single[A](x: A): pred[A] = Seq[A](((_: Unit) => Insert[A](x, bot_pred[A])))

  def sup_pred[A](x0: pred[A], x1: pred[A]): pred[A] = (x0, x1) match {
    case (Seq(f), Seq(g)) =>
      Seq[A](((_: Unit) =>
        (f(()) match {
          case Empty() => g(())
          case Insert(x, p) => Insert[A](x, sup_pred[A](p, Seq[A](g)))
          case Join(p, xq) => adjunct[A](Seq[A](g), Join[A](p, xq))
        })))
  }

  def adjunct[A](p: pred[A], x1: seq[A]): seq[A] = (p, x1) match {
    case (p, Empty()) => Join[A](p, Empty[A]())
    case (p, Insert(x, q)) => Insert[A](x, sup_pred[A](q, p))
    case (p, Join(q, xq)) => Join[A](q, adjunct[A](p, xq))
  }

  def if_pred(b: Boolean): pred[Unit] =
    (if (b) single[Unit](()) else bot_pred[Unit])

} /* object Predicate */

object Complete_Lattices {

  def Sup_set[A : HOL.equal](x0: Set.set[Set.set[A]]): Set.set[A] = x0 match {
    case Set.seta(xs) =>
      Lista.fold[Set.set[A],
        Set.set[A]](((a: Set.set[A]) => (b: Set.set[A]) =>
        Set.sup_set[A](a, b)),
        xs, Set.bot_set[A])
  }

} /* object Complete_Lattices */

object Optiona {

  def equal_optiona[A : HOL.equal](x0: Option[A], x1: Option[A]): Boolean =
    (x0, x1) match {
      case (None, Some(x2)) => false
      case (Some(x2), None) => false
      case (Some(x2), Some(y2)) => HOL.eq[A](x2, y2)
      case (None, None) => true
    }

  def is_none[A](x0: Option[A]): Boolean = x0 match {
    case Some(x) => false
    case None => true
  }

} /* object Optiona */

object Proof_Checker {

  abstract sealed class rrule[A, B, C]
  final case class ImplyR[A, B, C]() extends rrule[A, B, C]
  final case class AndR[A, B, C]() extends rrule[A, B, C]
  final case class CohideR[A, B, C]() extends rrule[A, B, C]
  final case class CohideRR[A, B, C]() extends rrule[A, B, C]
  final case class TrueR[A, B, C]() extends rrule[A, B, C]
  final case class EquivR[A, B, C]() extends rrule[A, B, C]
  final case class Skolem[A, B, C]() extends rrule[A, B, C]
  final case class HideR[A, B, C]() extends rrule[A, B, C]
  final case class CutRight[A, B, C](a: Syntax.formula[A, B, C]) extends
    rrule[A, B, C]
  final case class EquivifyR[A, B, C]() extends rrule[A, B, C]
  final case class CommuteEquivR[A, B, C]() extends rrule[A, B, C]


  abstract sealed class lrule[A, B, C]
  final case class ImplyL[A, B, C]() extends lrule[A, B, C]
  final case class AndL[A, B, C]() extends lrule[A, B, C]
  final case class EquivForwardL[A, B, C]() extends lrule[A, B, C]
  final case class EquivBackwardL[A, B, C]() extends lrule[A, B, C]
  final case class HideL[A, B, C]() extends lrule[A, B, C]
  final case class NotL[A, B, C]() extends lrule[A, B, C]
  final case class CutLeft[A, B, C](a: Syntax.formula[A, B, C]) extends
    lrule[A, B, C]
  final case class EquivL[A, B, C]() extends lrule[A, B, C]


  abstract sealed class ruleApp[A, B, C]
  final case class URename[C, A, B](a: C, b: C) extends ruleApp[A, B, C]
  final case class BRename[C, A, B](a: C, b: C) extends ruleApp[A, B, C]
  final case class Rrule[A, B, C](a: rrule[A, B, C], b: Nat.nat) extends
    ruleApp[A, B, C]
  final case class Lrule[A, B, C](a: lrule[A,B,C], b: Nat.nat) extends ruleApp[A, B, C]
  final case class CloseId[A, B, C](a: Nat.nat, b: Nat.nat) extends
    ruleApp[A, B, C]
  final case class Cohide2[A, B, C](a: Nat.nat, b: Nat.nat) extends
    ruleApp[A, B, C]
  final case class Cut[A, B, C](a: Syntax.formula[A, B, C]) extends
    ruleApp[A, B, C]

  abstract sealed class axRule
  final case class CT() extends axRule
  final case class CQ() extends axRule
  final case class CE() extends axRule
  final case class G() extends axRule
  final case class monb() extends axRule

  abstract sealed class axiom
  final case class AloopIter() extends axiom
  final case class AI() extends axiom
  final case class Atest() extends axiom
  final case class Abox() extends axiom
  final case class Achoice() extends axiom
  final case class AK() extends axiom
  final case class AV() extends axiom
  final case class Aassign() extends axiom
  final case class Adassign() extends axiom
  final case class Advar() extends axiom
  final case class AdConst() extends axiom
  final case class AdPlus() extends axiom
  final case class AdMult() extends axiom
  final case class ADW() extends axiom
  final case class ADE() extends axiom
  final case class ADC() extends axiom
  final case class ADS() extends axiom
  final case class ADIGeq() extends axiom
  final case class ADIGr() extends axiom
  final case class ADG() extends axiom
  final case class AEquivReflexive() extends axiom
  final case class ADiffEffectSys() extends axiom
  final case class AAllElim() extends axiom
  final case class ADiffLinear() extends axiom
  final case class ABoxSplit() extends axiom
  final case class AImpSelf() extends axiom
  final case class Acompose() extends axiom
  final case class AconstFcong() extends axiom
  final case class AdMinus() extends axiom
  final case class AassignEq() extends axiom
  final case class AallInst() extends axiom


  abstract sealed class pt[A, B, C]
  final case class FOLRConstant[A, B, C](a: Syntax.formula[A, B, C]) extends
    pt[A, B, C]
  final case class
  RuleApp[A, B, C](a: pt[A, B, C], b: ruleApp[A, B, C], c: Nat.nat)
    extends pt[A, B, C]
  final case class AxRule[A, B, C](a: axRule) extends pt[A, B, C]
  final case class
  PrUSubst[A, B, C](a: pt[A, B, C], b: USubst.subst_ext[A, B, C, Unit])
    extends pt[A, B, C]
  final case class Ax[A, B, C](a: axiom) extends pt[A, B, C]
  final case class
  FNC[A, B,
  C](a: pt[A, B, C],
     b: (List[Syntax.formula[A, B, C]], List[Syntax.formula[A, B, C]]),
     c: ruleApp[A, B, C])
    extends pt[A, B, C]
  final case class Pro[A, B, C](a: pt[A, B, C], b: pt[A, B, C]) extends
    pt[A, B, C]
  final case class
  Start[A, B,
  C](a: (List[Syntax.formula[A, B, C]], List[Syntax.formula[A, B, C]]))
    extends pt[A, B, C]
  final case class Sub[A, B, C](a: pt[A, B, C], b: pt[A, B, C], c: Nat.nat)
    extends pt[A, B, C]

  def closeI[A](x0: List[A], uu: Nat.nat): List[A] = (x0, uu) match {
    case (Nil, uu) => sys.error("undefined")

    case (x :: xs, n) =>
      (if (Nat.equal_nat(n, Nat.zero_nat)) xs
      else x :: closeI[A](xs, Nat.minus_nat(n, Nat.one_nat)))
  }

  def replaceI[A](x0: List[A], uu: Nat.nat, uv: A): List[A] = (x0, uu, uv) match {
    case (Nil, uu, uv) => sys.error("undefined")
    case (x :: xs, n, y) =>
      (if (Nat.equal_nat(n, Nat.zero_nat)) y :: xs
      else x :: replaceI[A](xs, Nat.minus_nat(n, Nat.one_nat), y))
  }

} /* object Proof_Checker */

object USubst {

  abstract sealed class subst_ext[A, B, C, D]
  final case class
  subst_exta[A, C, B,
  D](a: A => Option[Syntax.trm[Sum_Type.sum[A, C], C]],
     b: A => Option[Syntax.trm[A, C]],
     c: C => Option[Syntax.formula[Sum_Type.sum[A, C], B, C]],
     d: B => Option[Syntax.formula[A, Sum_Type.sum[B, Unit], C]],
     e: C => Option[Syntax.hp[A, B, C]],
     f: C => Option[Syntax.ODE[A, C]], g: D)
    extends subst_ext[A, B, C, D]

} /* object USubst */

object Scratch {

  abstract sealed class myvars
  final case class i1() extends myvars
  final case class i2() extends myvars
  final case class i3() extends myvars
  final case class i4() extends myvars
  final case class i5() extends myvars
  final case class i6() extends myvars
  final case class i7() extends myvars
  final case class i8() extends myvars
  final case class i9() extends myvars
  final case class i10() extends myvars
  final case class i11() extends myvars

  def enum_myvarsa: List[myvars] =
    List(i1(), i2(), i3(), i4(), i5(), i6(), i7(), i8(), i9(), i10(), i11())

  def ddl_P(p: myvars): Syntax.formula[myvars, myvars, myvars] =
    Syntax.Predicational[myvars, myvars, myvars](p)

  def ddl_f0(f: myvars): Syntax.trm[myvars, myvars] =
    Syntax.Function[myvars, myvars](f, Syntax.empty[myvars, myvars])

  def ddl_singleton[A](t: Syntax.trm[A, myvars], i: myvars): Syntax.trm[A, myvars]
  =
    if (i == i1()) t else Syntax.Const[A, myvars](Real.zero_real)

  def ddl_f1(f: myvars, x: myvars): Syntax.trm[myvars, myvars] =
    Syntax.Function[myvars,
      myvars](f, ((a: myvars) =>
      ddl_singleton[myvars](Syntax.Var[myvars,
        myvars](x),
        a)))

  def ddl_p1(p: myvars, x: myvars): Syntax.formula[myvars, myvars, myvars] =
    Syntax.Prop[myvars, myvars,
      myvars](p, ((a: myvars) =>
      ddl_singleton[myvars](Syntax.Var[myvars, myvars](x),
        a)))

} /* object Scratch */


object Syntax {

  abstract sealed class trm[A, B]
  final case class Var[B, A](a: B) extends trm[A, B]
  final case class Const[A, B](a: Real.real) extends trm[A, B]
  final case class Function[A, B](a: A, b: B => trm[A, B]) extends trm[A, B]
  final case class Functional[A, B](a: A) extends trm[A, B]
  final case class Plus[A, B](a: trm[A, B], b: trm[A, B]) extends trm[A, B]
  final case class Times[A, B](a: trm[A, B], b: trm[A, B]) extends trm[A, B]
  final case class DiffVar[B, A](a: B) extends trm[A, B]
  final case class Differential[A, B](a: trm[A, B]) extends trm[A, B]


  abstract sealed class ODE[A, B]
  final case class OVar[B, A](a: B) extends ODE[A, B]
  final case class OSing[B, A](a: B, b: trm[A, B]) extends ODE[A, B]
  final case class OProd[A, B](a: ODE[A, B], b: ODE[A, B]) extends ODE[A, B]


  abstract sealed class formula[A, B, C]
  final case class Geq[A, C, B](a: trm[A, C], b: trm[A, C]) extends
    formula[A, B, C]
  final case class Prop[C, A, B](a: C, b: C => trm[A, C]) extends formula[A, B, C]
  final case class Not[A, B, C](a: formula[A, B, C]) extends formula[A, B, C]
  final case class And[A, B, C](a: formula[A, B, C], b: formula[A, B, C]) extends
    formula[A, B, C]
  final case class Exists[C, A, B](a: C, b: formula[A, B, C]) extends
    formula[A, B, C]
  final case class Diamond[A, B, C](a: hp[A, B, C], b: formula[A, B, C]) extends
    formula[A, B, C]
  final case class InContext[B, A, C](a: B, b: formula[A, B, C]) extends
    formula[A, B, C]

  abstract sealed class hp[A, B, C]
  final case class Pvar[C, A, B](a: C) extends hp[A, B, C]
  final case class Assign[C, A, B](a: C, b: trm[A, C]) extends hp[A, B, C]
  final case class DiffAssign[C, A, B](a: C, b: trm[A, C]) extends hp[A, B, C]
  final case class Test[A, B, C](a: formula[A, B, C]) extends hp[A, B, C]
  final case class EvolveODE[A, C, B](a: ODE[A, C], b: formula[A, B, C]) extends
    hp[A, B, C]
  final case class Choice[A, B, C](a: hp[A, B, C], b: hp[A, B, C]) extends
    hp[A, B, C]
  final case class Sequence[A, B, C](a: hp[A, B, C], b: hp[A, B, C]) extends
    hp[A, B, C]
  final case class Loop[A, B, C](a: hp[A, B, C]) extends hp[A, B, C]

  def Or[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C] =
    Not[A, B, C](And[A, B, C](Not[A, B, C](p), Not[A, B, C](q)))

  def TT[A, B, C]: formula[A, B, C] =
    Geq[A, C, B](Const[A, C](Real.zero_real), Const[A, C](Real.zero_real))

  def Box[A, B, C](alpha: hp[A, B, C], p: formula[A, B, C]): formula[A, B, C] =
    Not[A, B, C](Diamond[A, B, C](alpha, Not[A, B, C](p)))

  def Equiv[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C] =
    Or[A, B,
      C](And[A, B, C](p, q), And[A, B, C](Not[A, B, C](p), Not[A, B, C](q)))

  def Minus[A, B](theta_1: trm[A, B], theta_2: trm[A, B]): trm[A, B] =
    Plus[A, B](theta_1,
      Times[A, B](theta_2,
        Const[A, B](Real.uminus_real(Real.one_real))))


  def Equals[A, B, C](thetaa: trm[A, B], theta: trm[A, B]): formula[A, C, B] =
    And[A, C, B](Geq[A, B, C](thetaa, theta), Geq[A, B, C](theta, thetaa))

  def Forall[A, B, C](x: A, p: formula[B, C, A]): formula[B, C, A] =
    Not[B, C, A](Exists[A, B, C](x, Not[B, C, A](p)))

  def Greater[A, B, C](thetaa: trm[A, B], theta: trm[A, B]): formula[A, C, B] =
    And[A, C,
      B](Geq[A, B, C](thetaa, theta),
      Not[A, C, B](Geq[A, B, C](theta, thetaa)))

  def Implies[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C]
  =
    Or[A, B, C](q, Not[A, B, C](p))


  def empty[A, B]: A => trm[B, A] = ((_: A) => Const[B, A](Real.zero_real))

  def Predicational[A, B, C](p: A): formula[B, A, C] =
    InContext[A, B,
      C](p, Geq[B, C,
      A](Const[B, C](Real.zero_real),
      Const[B, C](Real.zero_real)))

} /* object Syntax */

object Parser {

  import pt.lib.Int._
  import pt.lib.Nat._
  import pt.lib.Rat._
  import pt.lib.Real._
  import pt.lib.Proof_Checker._
  import pt.lib.Syntax._
  import pt.lib.Scratch._

  type myvars = pt.lib.Scratch.myvars

  case class ParseException(pos:Int) extends Exception {
    override def toString:String = {s"ParseException(${pos})"}
  }

  type Parse[T] = ((String, Int) => (T, Int))
  val TOKEN_CAPACITY = 20

  def newSB = new StringBuilder(TOKEN_CAPACITY, "")

  var sbAlphaNum = newSB

  def alphanum(str: String, i: Int): (String, Int) = {
    val len = str.length
    var j = i
    while (j < len) {
      var c = str(j)
      if (c.isLetterOrDigit) {
        sbAlphaNum.+=(c)
        j = j + 1
      } else {
        val res = sbAlphaNum.toString()
        sbAlphaNum = newSB
        return (res, j)
      }
    }
    val res = sbAlphaNum.toString()
    sbAlphaNum = newSB
    (res, j)
  }

  def eatSym(lit:String):Parse[Unit]= {(str:String,i:Int) =>
    val len = lit.length
    val len2 = str.length
    var j = 0
    while(j < len && i+j < len2)
    {
      if(str(i+j) != lit(j)) {
        throw ParseException(i + j)
      }
      j = j + 1
    }
    ((),i+j)
  }

  val idMap:Map[String,myvars] = Map(
    ("i1",i1()),
    ("i2",i2()),
    ("i3",i3()),
    ("i4",i4()),
    ("i5",i5()),
    ("i6",i6()),
    ("i7",i7()),
    ("i8",i8()),
    ("i9",i9()),
    ("i10",i10()),
    ("i11",i11())
  )

  val intOfId:Map[myvars,Int] = Map(
    (i1(),0),
    (i2(),1),
    (i3(),2),
    (i4(),3),
    (i5(),4),
    (i6(),5),
    (i7(),6),
    (i8(),7),
    (i9(),8),
    (i10(),9),
    (i11(),10)

  )

  @inline
  val mv:Parse[myvars] = {(str,i) =>
    val (ident,j) = alphanum(str,i)
    (idMap(ident),j)
  }

  @inline
  val unit:Parse[Unit] = {(str,i) =>
    eatSym("()")(str,i)
  }

  @inline
  def sum[T1,T2](l:Parse[T1],r:Parse[T2]):Parse[sum[T1,T2]] = {(str,i) =>
    val i2 = eatChar(str,i,'(')
    val (ident,i3) = alphanum(str,i2)
    val i4 = eatChar(str,i3,' ')
    val (res:sum[T1,T2], beforeParen) =
      ident match {
        case "Inl" =>
          val (lres, i5) = l(str,i4)
          (Inl(lres),i5)
        case "Inr" =>
          val (rres, i5) = r(str,i4)
          (Inr(rres),i5)
      }
    val i6 = eatChar(str,beforeParen,')')
    (res,i6)
  }

  @inline
  def option[T](t:Parse[T]):Parse[Option[T]] = { (str, i) =>
    //println("The i'th char is:" + str(i))
    if(str(i) == '(') { // some case
      //println("Checking someness-ness: " + str + " " + i)
      val ((_id, elem), i2) = p1(eatSym("Some"), t)(str,i)
      (Some(elem),i2)
    } else {
      //println("Checking non-ness: " + str + " " + i)
      val (ident, i2) = eatSym("None")(str,i)
      (None,i2)
    }
  }

  @inline
  private def eatChar(str:String,i:Int,c:Char):Int = {
    if(str(i) != c) {
      throw ParseException(i)
    }
    i+1
  }

  @inline
  def p0[T](f0:Parse[T]):Parse[T] ={(str,i) =>
    val (res,j) = f0(str,eatChar(str,i,'('))
    val k = eatChar(str,j,')')
    (res,k)
  }

  @inline
  def p1[T1,T2](f1:Parse[T1],f2:Parse[T2]):Parse[(T1,T2)] ={(str,i) =>
    val i1 = eatChar(str,i,'(')
    val (res1,i2) = f1(str,i1)
    val i3 = eatChar(str,i2,' ')
    val (res2,i4) = f2(str,i3)
    val i5 = eatChar(str,i4,')')
    ((res1,res2),i5)
  }

  @inline
  def p2[T1,T2,T3](f1:Parse[T1],f2:Parse[T2],f3:Parse[T3]):Parse[(T1,T2,T3)] ={(str,i) =>
    val i1 = eatChar(str,i,'(')
    val (res1,i2) = f1(str,i1)
    val i3 = eatChar(str,i2,' ')
    val (res2,i4) = f2(str,i3)
    val i5 = eatChar(str,i4,' ')
    val (res3,i6) = f3(str,i5)
    val i7 = eatChar(str,i6,')')
    ((res1,res2,res3),i7)
  }

  @inline
  def p3[T1,T2,T3,T4](f1:Parse[T1],f2:Parse[T2],f3:Parse[T3],f4:Parse[T4]):Parse[(T1,T2,T3,T4)] ={(str,i) =>
    val i1 = eatChar(str,i,'(')
    val (res1,i2) = f1(str,i1)
    val i3 = eatChar(str,i2,' ')
    val (res2,i4) = f2(str,i3)
    val i5 = eatChar(str,i4,' ')
    val (res3,i6) = f3(str,i5)
    val i7 = eatChar(str,i6,' ')
    val (res4,i8) = f4(str,i7)
    val i9 = eatChar(str,i8,')')
    ((res1,res2,res3,res4),i9)
  }

  @inline
  def p6[T1,T2,T3,T4,T5,T6,T7](f1:Parse[T1],f2:Parse[T2],f3:Parse[T3],f4:Parse[T4],f5:Parse[T5],f6:Parse[T6],f7:Parse[T7]):Parse[(T1,T2,T3,T4,T5,T6,T7)] ={(str,i) =>
    val i1 = eatChar(str,i,'(')
    val (res1,i2) = f1(str,i1)
    val i3 = eatChar(str,i2,' ')
    val (res2,i4) = f2(str,i3)
    val i5 = eatChar(str,i4,' ')
    val (res3,i6) = f3(str,i5)
    val i7 = eatChar(str,i6,' ')
    val (res4,i8) = f4(str,i7)
    val i9 = eatChar(str,i8,' ')
    val (res5,i10) = f5(str,i9)
    val i11 = eatChar(str,i10,' ')
    val (res6,i12) = f6(str,i11)
    val i13 = eatChar(str,i12,' ')
    val (res7,i14) = f7(str,i13)
    val i15 = eatChar(str,i14,')')
    ((res1,res2,res3,res4,res5,res6,res7),i15)
  }

  @inline
  def ptup[T1,T2] = p1[T1,T2]_

  val axMap:Map[String,axiom] = Map(
  ("AloopIter",AloopIter()),
  ("AI",AI()),
  ("Atest",Atest()),
  ("Abox",Abox()),
  ("Achoice",Achoice()),
  ("AK",AK()),
  ("AV",AV()),
  ("Aassign",Aassign()),
  ("Adassign",Adassign()),
  ("Advar",Advar()),
  ("AdConst",AdConst()),
  ("AdPlus",AdPlus()),
  ("AdMult",AdMult()),
  ("ADW",ADW()),
  ("ADE",ADE()),
  ("ADC",ADC()),
  ("ADS",ADS()),
  ("ADIGeq",ADIGeq()),
  ("AEquivReflexive",AEquivReflexive()),
  ("ADiffEffectSys",ADiffEffectSys()),
  ("ADIGr",ADIGr()),
  ("ADG",ADG()),
  ("AAllElim",AAllElim()),
  ("ADiffLinear",ADiffLinear()),
  ("ABoxSplit",ABoxSplit()),
  ("AImpSelf",AImpSelf()),
  ("Acompose",Acompose()),
  ("AconstFcong",AconstFcong()),
  ("AassignEq",AassignEq()),
  ("AdMinus",AdMinus()),
  ("AallInst",AallInst())
  )

  @inline
  val axiom:Parse[axiom] = {(str,i) =>
    val (axname,j) = p0(alphanum)(str,i)
    val ax = axMap(axname)
    (ax,j)
  }

  val axruleMap:Map[String,axRule] = Map(
    ("CT", CT()),
    ("CQ",CQ()),
    ("CE",CE()),
    ("G",G()),
    ("monb",monb())
  )

  @inline
  val axrule:Parse[axRule] = {(str,i) =>
    val (axname,j) = p0(alphanum)(str,i)
    val ax = axruleMap(axname)
    (ax,j)
  }


  @inline
  val natLit:Parse[Int] = {(str,i) =>
    val (nstr,j) = alphanum(str,i)
    (nstr.toInt, j)
  }

  @inline
  val nat:Parse[nat] = {(str,i) =>
    val ((_,n),j) = p1(eatSym("Nata"),natLit)(str,i)
    (Nata(n), j)
  }

  @inline
  val intLit:Parse[Int] = {(str,i) =>
    if(str(i) == '-') {
      val (n,j) = natLit(str,i+1)
      (-n,j)
    } else {
      natLit(str,i)
    }
  }

  @inline
  val int:Parse[int] = {(str,i) =>
    val ((_,n),j) = p1(eatSym("int_of_integer"),intLit)(str,i)
    (int_of_integer(n), j)
  }

  @inline
  val rat:Parse[rat] = {(str,i) =>
    val ((_,tup),j) = p1(eatSym("Frct"),ptup(int,int))(str,i)
    (Rat.Frct(tup),j)
  }

  @inline
  val real:Parse[real] = { (str, i) =>
    val ((_,ratt),j) = p1(eatSym("Ratreal"),rat)(str,i)
    (Real.Ratreal(ratt),j)
  }

  @inline
  def zc[T1,T2]:trm[T1,T2] = Const(Real.Ratreal(Rat.Frct((Int.int_of_integer(0),Int.int_of_integer(1)))))

  @inline
  def list[T](p:Parse[T]):Parse[List[T]] = { (str, i) =>
    var elems:List[T] = List()
    val i2 = eatChar(str,i,'(')
    var j = i2
    while(str(j) != ')') {
      val (elem,j1) = p(str,j)
      elems = elem :: elems
      j = if(str(j1) == ' ') {j1 + 1} else j1
    }
    val j2 = eatChar(str,j,')')
    (elems.reverse,j2)
  }

  @inline
  def noneElse[T](p:Parse[(myvars => Option[T])]):Parse[(myvars => Option[T])] = {(str,i) =>
    if(i+1 < str.length && str(i) == 'n' && str(i+1) == 's') {
      ({_ => None}, i+2)
    } else {
      p(str,i)
    }
  }

  @inline
  def bff[T](p:Parse[T]):Parse[(myvars => T)] = {(str,i) =>
    val (l:List[T],i1) = list(p)(str,i)
    val arr:IndexedSeq[T] = l.toIndexedSeq
    ({case e => arr(intOfId(e))}, i1)
  }


  def emptyElse[T](base:T, p:Parse[T],l:Parse[(myvars => T)]):Parse[(myvars => T)] = {(str,i) =>
    if(str(i) == 'e') {
      if(i+2 < str.length && str(i+1) == 's' && str(i+2) == 't') {
        ({j => base}, i+3)
      } else ({j => base},i+1)
    } else if (i+1 < str.length && str(i)=='(' && str(i+1) == 's') {
      val j1 =  if(i+3 < str.length && str(i+2) == 's' && str(i+3) == 't') (i+4) else i+2
      val j2 = eatChar(str,j1,' ')
      val (elem,j3) = p(str,j2)
      val j4 = eatChar(str,j3,')')
      ({case i1() => elem case _ => base},j4)
    } else {
      l(str,i)
    }
  }

  def ode[F](fid:Parse[F]):Parse[ODE[F,myvars]] = { (str,i) =>
    val i1 = eatChar(str,i,'(')
    val(con,i2) = alphanum(str,i1)
    val i3 = eatChar(str, i2, ' ')
    val (res:ODE[F,myvars], beforeParen:Int) =
      con match {
        case "OVar" =>
          val (c,i4) = mv(str,i3)
          (OVar[myvars,F](c),i4)
        case "OSing" =>
          val (x,i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (t, i6) = trm(fid)(str,i5)
          (OSing[myvars,F](x,t),i6)
        case "OProd" =>
          val (ode1,i4) = ode(fid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (ode2,i6) = ode(fid)(str,i5)
          (OProd[F,myvars](ode1,ode2),i6)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }

  def hp[F,P](fid:Parse[F],pid:Parse[P]):Parse[hp[F,P,myvars]] = { (str, i) =>
    val i1 = eatChar(str,i,'(')
    val(con,i2) = alphanum(str,i1)
    val i3 = eatChar(str, i2, ' ')
    val (res:hp[F,P,myvars], beforeParen:Int) =
      con match {
        case "Pvar" =>
          val (a, i4) = mv(str,i3)
          (Pvar(a),i4)
        case "Assign" =>
          val (x, i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (t, i6) = trm(fid)(str,i5)
          (Assign(x,t),i6)
        case "DiffAssign" =>
          val (x, i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (t, i6) = trm(fid)(str,i5)
          (DiffAssign(x,t),i6)
        case "Test" =>
          val (p, i4) = formula(fid,pid)(str,i3)
          (Test(p), i4)
        case "EvolveODE" =>
          val (o, i4) = ode(fid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (p,i6) = formula(fid,pid)(str,i5)
          (EvolveODE(o,p),i6)
        case "Choice" =>
          val (a, i4) = hp(fid,pid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (b, i6) = hp(fid,pid)(str,i5)
          (Choice(a,b),i6)
        case "Sequence" =>
          val (a, i4) = hp(fid,pid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (b, i6) = hp(fid,pid)(str,i5)
          (Sequence(a,b),i6)
        case "Loop" =>
          val (a, i4) = hp(fid,pid)(str,i3)
          (Loop(a),i4)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }

  def formula[F,P](fid:Parse[F],pid:Parse[P]):Parse[formula[F,P,myvars]] = { (str, i) =>
    val i1 = eatChar(str,i,'(')
    val(con,i2) = alphanum(str,i1)
    val i3 = eatChar(str, i2, ' ')
    val (res:formula[F,P,myvars], beforeParen:Int) =
      con match {
        case "Geq" =>
          val(t1, i4) = trm[F](fid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val(t2, i6) = trm[F](fid)(str,i5)
          (Geq[F,myvars,P](t1,t2),i6)
        case "Prop" =>
          val (name, i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (args,i6) = emptyElse[trm[F,myvars]](Const(Real.zero_real), trm(fid),bff(trm(fid)))(str,i5)
          (Prop[myvars,F,P](name,args), i6)
        case "Not" =>
          val (f,i4) = formula[F,P](fid,pid)(str,i3)
          (Not[F,P,myvars](f),i4)
        case "And" =>
          val (p,i4) = formula[F,P](fid,pid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (q,i6) = formula[F,P](fid,pid)(str,i5)
          (And[F,P,myvars](p,q),i6)
        case "Exists" =>
          val (name, i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (q,i6) = formula[F,P](fid,pid)(str,i5)
          (Exists[myvars,F,P](name,q),i6)
        case "Diamond" =>
          val (a, i4) = hp[F,P](fid,pid)(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (q,i6) = formula[F,P](fid,pid)(str,i5)
          (Diamond[F,P,myvars](a,q), i6)
        case "InContext" =>
          val (name, i4) = pid(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (q,i6) = formula[F,P](fid,pid)(str,i5)
          (InContext[P,F,myvars](name,q),i6)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }

  /* D](a: A => Option[Syntax.trm[Sum_Type.sum[A, C], C]],
     b: A => Option[Syntax.trm[A, C]],
     c: C => Option[Syntax.formula[Sum_Type.sum[A, C], B, C]],
     d: B => Option[Syntax.formula[A, Sum_Type.sum[B, Unit], C]],
     e: C => Option[Syntax.hp[A, B, C]],
     f: C => Option[Syntax.ODE[A, C]], g: D)
    extends subst_ext[A, B, C, D]
*/
  val subst:Parse[USubst.subst_ext[myvars,myvars,myvars,Unit]] = {(str,i) =>
    val ((_id, fun,funl,pred,con,hpp,oode), i1:Int) = p6(eatSym("subst_exta"),
      noneElse(bff(option(trm(sum(mv,mv))))),
      noneElse(bff(option(trm(mv)))),
      noneElse(bff(option(formula(sum(mv,mv),mv)))),
      noneElse(bff(option(formula(mv,sum(mv,unit))))),
      noneElse(bff(option(hp(mv,mv)))),
      noneElse(bff(option(ode(mv))))
    )(str,i)
    (USubst.subst_exta[myvars,myvars,myvars,Unit](fun,funl,pred,con,hpp,oode,()),i1)
  }

  def trm[ID](id:Parse[ID]):Parse[trm[ID,myvars]] = {(str,i) =>
    if (str(i) == 'z') {
      if(i+2 < str.length && str(i+1) == 's' && str(i+2) == 't') {
        (zc[ID,myvars],i+3)
      } else {
        (zc[ID,myvars],i+1)
      }
    } else {
      val i1 = eatChar(str, i, '(')
      val (con, i2) = alphanum(str, i1)
      val i3 = eatChar(str, i2, ' ')
      val (res:trm[ID,Parser.myvars], beforeParen:Int) =
        con match {
          case "Var" =>
            val (r,i4) = mv(str,i3)
            (Var[myvars,ID](r),i4)
          case "Const" =>
            val (r,i4) = real(str,i3)
            (Const[ID,myvars](r),i4)
          case "z" => zc
          case "Function" =>
            val (name, i4) = id(str,i3)
            val i5 = eatChar(str,i4,' ')
            val (args,i6) = emptyElse[trm[ID,myvars]](Const(Real.zero_real),trm(id),bff(trm(id)))(str,i5)
            //val i7 = eatChar(str,i6,')')
            (Function[ID,myvars](name,args), i6)
          case "Functional" =>
            val (name, i4) = id(str,i3)
            (Functional[ID,myvars](name),i4)
          case "Plus" =>
            val (left, i4) = trm[ID](id)(str,i3)
            val i5 = eatChar(str,i4,' ')
            val (right, i6) = trm[ID](id)(str,i5)
            (Plus[ID,myvars](left,right),i6)
          case "Times" =>
            val (left, i4) = trm[ID](id)(str,i3)
            val i5 = eatChar(str,i4,' ')
            val (right, i6) = trm[ID](id)(str,i5)
            (Times[ID,myvars](left,right),i6)
          case "Differential" =>
            val (child, i4) = trm[ID](id)(str,i3)
            (Differential[ID,myvars](child),i4)
          case "DiffVar" =>
            val (name, i4) = mv(str,i3)
            (DiffVar[myvars,ID](name),i4)
        }
      val iEnd = eatChar(str,beforeParen,')')
      (res,iEnd)
    }
  }

  @inline
  val sequent:Parse[(List[formula[myvars,myvars,myvars]],List[formula[myvars,myvars,myvars]])] = {(str,i) =>
    ptup(list(formula(mv,mv)),list(formula(mv,mv)))(str,i)
  }

  val leftRule:Parse[lrule[myvars,myvars,myvars]] = {(str,i) =>
    val i1 = eatChar(str, i, '(')
    val (con, i2) = alphanum(str, i1)
    val (res:lrule[Scratch.myvars,Scratch.myvars,Scratch.myvars], beforeParen:Int) =
      con match {
        case "HideL" => (HideL(), i2)
        case "ImplyL" => (ImplyL(), i2)
        case "AndL" => (AndL(), i2)
        case "NotL" => (NotL(), i2)
        case "EquivBackwardL" => (EquivBackwardL(), i2)
        case "EquivForwardL" => (EquivForwardL(), i2)
        case "EquivL" => (EquivL(), i2)
        case "CutLeft" =>
          val i3 = eatChar(str, i2, ' ')
          val (f,i4) = formula(mv,mv)(str,i3)
          (CutLeft(f),i4)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }

  val rightRule:Parse[rrule[myvars,myvars,myvars]] = {(str,i) =>
    val i1 = eatChar(str, i, '(')
    val (con, i2) = alphanum(str, i1)
    val (res:rrule[Scratch.myvars,Scratch.myvars,Scratch.myvars], beforeParen:Int) =
      con match {
        case "CutRight" =>
          val i3 = eatChar(str, i2, ' ')
          val (f,i4) = formula(mv,mv)(str,i3)
          (CutRight(f),i4)
        case "ImplyR" => (ImplyR(),i2)
        case "AndR" =>(AndR(), i2)
        case "HideR" => (HideR(),i2)
        case "CohideR" => (CohideR(),i2)
        case "CohideRR" => (CohideRR(), i2)
        case "TrueR" => (TrueR(),i2)
        case "EquivR" => (EquivR(),i2)
        case "EquivifyR" => (EquivifyR(),i2)
        case "CommuteEquivR" => (CommuteEquivR(),i2)
        case "Skolem" => (Skolem(),i2)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }


    val ruleAppl:Parse[ruleApp[myvars,myvars,myvars]] = {(str,i) =>
    val i1 = eatChar(str, i, '(')
    val (con, i2) = alphanum(str, i1)
    val i3 = eatChar(str, i2, ' ')
    val (res:ruleApp[Scratch.myvars,Scratch.myvars,Scratch.myvars], beforeParen:Int) =
      con match {
        case "URename" =>
          val (w,i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = mv(str,i5)
          (URename(w,r),i6)
        case "BRename" =>
          val (w,i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = mv(str,i5)
          (BRename(w,r),i6)
        case "Rrule" =>
          val (rule, i4) = rightRule(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (n,i6) = nat(str,i5)
          (Rrule(rule,n),i6)
        case "Lrule" =>
          val (rule, i4) = leftRule(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (n,i6) = nat(str,i5)
          (Lrule(rule,n),i6)
        case "CloseId" =>
          val (w,i4) = nat(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = nat(str,i5)
          (CloseId(w,r),i6)
        case "Cohide2" =>
          val (w,i4) = nat(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = nat(str,i5)
          (Cohide2(w,r),i6)
        case "Cut" =>
          val (f,i4) = formula(mv,mv)(str,i3)
          (Cut(f),i4)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }

  val proofTerm:Parse[pt[myvars,myvars,myvars]] = {(str,i) =>
    val i1 = eatChar(str, i, '(')
    val (con, i2) = alphanum(str, i1)
    val i3 = eatChar(str, i2, ' ')
    val (res:pt[Scratch.myvars,Scratch.myvars,Scratch.myvars], beforeParen:Int) =
      con match {
        case "FOLRConstant" =>
          val (f,i4) = formula(mv,mv)(str,i3)
          (FOLRConstant(f),i4)
        case "RuleApp" =>
          val (child,i4) = proofTerm(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (rApp,i6) = ruleAppl(str,i5)
          val i7 = eatChar(str,i6,' ')
          val (n, i8) = nat(str,i7)
          (RuleApp(child,rApp,n),i8)
        case "AxRule" =>
          val (ar,i4) = axrule(str,i3)
          (AxRule(ar),i4)
        case "PrUSubst" =>
          val (pterm,i4) = proofTerm(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (sub,i6) = subst(str,i5)
          (PrUSubst(pterm,sub),i6)
        case "Ax" =>
          val (a,i4) = axiom(str,i3)
          (Ax(a),i4)
        case "FNC" =>
          val (child,i4) = proofTerm(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (newCon,i6) = sequent(str,i5)
          val i7 = eatChar(str,i6,' ')
          val (rApp, i8) = ruleAppl(str,i7)
          (FNC(child,newCon,rApp),i8)
        case "Pro" =>
          val (pterm1,i4) = proofTerm(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (pterm2,i6) = proofTerm(str,i5)
          (Pro(pterm1,pterm2),i6)
        case "Start" =>
          val (seq,i4) = sequent(str,i3)
          (Start(seq),i4)
        case "Sub" =>
          val (pterm1,i4) = proofTerm(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (pterm2,i6) = proofTerm(str,i5)
          val i7 = eatChar(str,i6,' ')
          val (n,i8) = nat(str,i7)
          (Sub(pterm1,pterm2,n),i8)
      }
    val iEnd = eatChar(str,beforeParen,')')
    (res,iEnd)
  }


}