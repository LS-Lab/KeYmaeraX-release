package pt

import pt.Int.int_of_integer
import pt.Rat.Frct
import pt.Real.Ratreal

import scala.io.Source

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

  def ofInt(n:Int):num =
    if(n == 1) { One()}
    else if(n % 2 == 0) {Bit0(ofInt(n/2))}
    else  {Bit1(ofInt(n/2))}


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
    implicit def `Scratch.enum_myvars`: enum[Scratch.myvars] = new
        enum[Scratch.myvars] {
      val `Enum.enum` = Scratch.enum_myvarsa
      val `Enum.enum_all` = (a: Scratch.myvars => Boolean) =>
        Scratch.enum_all_myvars(a)
      val `Enum.enum_ex` = (a: Scratch.myvars => Boolean) =>
        Scratch.enum_ex_myvars(a)
    }
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

  def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
    case (f, a, Nil) => a
    case (f, a, x :: xs) => foldl[A, B](f, (f(a))(x), xs)
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
      => Syntax.equal_formulaa[A, B, C](a, b)
    }
    implicit def `Scratch.equal_myvars`: equal[Scratch.myvars] = new
        equal[Scratch.myvars] {
      val `HOL.equal` = (a: Scratch.myvars, b: Scratch.myvars) =>
        Scratch.equal_myvarsa(a, b)
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
        Syntax.equal_trma[A, B](a, b)
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

  val c:Char = 'a'
} /* object Rat */
object String {

  object Char {
    def ofChar(c:scala.Char):String.char = {
      Char(Num.ofInt(c.toInt))
    }
  }
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
  final case class BRenameR[C, A, B](a: C, b: C) extends rrule[A, B, C]


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
  final case class BRenameL[C, A, B](a: C, b: C) extends lrule[A, B, C]


  abstract sealed class ruleApp[A, B, C]
  final case class URename[C, A, B](a: C, b: C) extends ruleApp[A, B, C]
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

  def SPredicates[A, B, C, D](x0: subst_ext[A, B, C, D]):
  C => Option[Syntax.formula[Sum_Type.sum[A, C], B, C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sPredicates
    }

  def SFunctions[A, B, C, D](x0: subst_ext[A, B, C, D]):
  A => Option[Syntax.trm[Sum_Type.sum[A, C], C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sFunctions
    }

  def SFunls[A, B, C, D](x0: subst_ext[A, B, C, D]): A => Option[Syntax.trm[A, C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sFunls
    }

  def SFV[A, B,
  C : Enum.enum : HOL.equal](sigma: subst_ext[A, B, C, Unit],
                             x1: Sum_Type.sum[A, Sum_Type.sum[B, C]]):
  Set.set[Sum_Type.sum[C, C]]
  =
    (sigma, x1) match {
      case (sigma, Sum_Type.Inl(i)) =>
        Set.sup_set[Sum_Type.sum[C, C]](((SFunctions[A, B, C, Unit](sigma)).apply(i)
        match {
          case None =>
            Set.bot_set[Sum_Type.sum[C, C]]
          case Some(a) =>
            Static_Semantics.FVT[Sum_Type.sum[A, C], C](a)
        }),
          ((SFunls[A, B, C, Unit](sigma)).apply(i)
          match {
            case None => Set.bot_set[Sum_Type.sum[C, C]]
            case Some(a) => Static_Semantics.FVT[A, C](a)
          }))
      case (sigma, Sum_Type.Inr(Sum_Type.Inl(i))) => Set.bot_set[Sum_Type.sum[C, C]]
      case (sigma, Sum_Type.Inr(Sum_Type.Inr(i))) =>
        ((SPredicates[A, B, C, Unit](sigma)).apply(i) match {
          case None => Set.bot_set[Sum_Type.sum[C, C]]
          case Some(a) => Static_Semantics.FVF[Sum_Type.sum[A, C], B, C](a)
        })
    }

  def SPrograms[A, B, C, D](x0: subst_ext[A, B, C, D]):
  C => Option[Syntax.hp[A, B, C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sPrograms
    }

  def SContexts[A, B, C, D](x0: subst_ext[A, B, C, D]):
  B => Option[Syntax.formula[A, Sum_Type.sum[B, Unit], C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sContexts
    }

  def SDom[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](sigma: subst_ext[A, B, C, Unit]):
  Set.set[Sum_Type.sum[A, Sum_Type.sum[B, C]]]
  =
    Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
      C]]](Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
      C]]](Set.sup_set[Sum_Type.sum[A,
      Sum_Type.sum[B, C]]](Set.sup_set[Sum_Type.sum[A,
      Sum_Type.sum[B, C]]](Set.image[A,
      Sum_Type.sum[A, Sum_Type.sum[B, C]]](((a: A) =>
      Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)),
      Set.uminus_set[A](Set.Collect[A](((x: A)
      =>
        Optiona.is_none[Syntax.trm[Sum_Type.sum[A, C],
          C]]((SFunctions[A, B, C, Unit](sigma)).apply(x)))))),
      Set.image[A,
        Sum_Type.sum[A, Sum_Type.sum[B, C]]](((a: A) =>
        Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)),
        Set.uminus_set[A](Set.Collect[A](((x: A) =>
          Optiona.is_none[Syntax.trm[A,
            C]]((SFunls[A, B, C, Unit](sigma)).apply(x))))))),
      Set.image[B, Sum_Type.sum[A,
        Sum_Type.sum[B, C]]](((x: B) =>
        Sum_Type.Inr[Sum_Type.sum[B, C],
          A](Sum_Type.Inl[B, C](x))),
        Set.uminus_set[B](Set.Collect[B](((x: B) =>
          Optiona.is_none[Syntax.formula[A,
            Sum_Type.sum[B, Unit],
            C]]((SContexts[A, B, C, Unit](sigma)).apply(x))))))),
      Set.image[C, Sum_Type.sum[A,
        Sum_Type.sum[B, C]]](((x: C) =>
        Sum_Type.Inr[Sum_Type.sum[B, C],
          A](Sum_Type.Inr[C, B](x))),
        Set.uminus_set[C](Set.Collect[C](((x: C) =>
          Optiona.is_none[Syntax.formula[Sum_Type.sum[A, C], B,
            C]]((SPredicates[A, B, C, Unit](sigma)).apply(x))))))),
      Set.image[C, Sum_Type.sum[A, Sum_Type.sum[B,
        C]]](((x: C) =>
        Sum_Type.Inr[Sum_Type.sum[B, C], A](Sum_Type.Inr[C, B](x))),
        Set.uminus_set[C](Set.Collect[C](((x: C) =>
          Optiona.is_none[Syntax.hp[A, B,
            C]]((SPrograms[A, B, C, Unit](sigma)).apply(x)))))))

  def TsubstFO[A, B,
  C](x0: Syntax.trm[Sum_Type.sum[A, B], C],
     sigma: B => Syntax.trm[A, C]):
  Syntax.trm[A, C]
  =
    (x0, sigma) match {
      case (Syntax.Var(v), sigma) => Syntax.Var[C, A](v)
      case (Syntax.DiffVar(v), sigma) => Syntax.DiffVar[C, A](v)
      case (Syntax.Const(r), sigma) => Syntax.Const[A, C](r)
      case (Syntax.Functional(f), sigma) =>
        (f match {
          case Sum_Type.Inl(a) => Syntax.Functional[A, C](a)
          case Sum_Type.Inr(a) => sigma(a)
        })
      case (Syntax.Function(f, args), sigma) =>
        (f match {
          case Sum_Type.Inl(fa) =>
            Syntax.Function[A, C](fa, ((i: C) =>
              TsubstFO[A, B, C](args(i), sigma)))
          case Sum_Type.Inr(a) => sigma(a)
        })
      case (Syntax.Plus(theta_1, theta_2), sigma) =>
        Syntax.Plus[A, C](TsubstFO[A, B, C](theta_1, sigma),
          TsubstFO[A, B, C](theta_2, sigma))
      case (Syntax.Times(theta_1, theta_2), sigma) =>
        Syntax.Times[A, C](TsubstFO[A, B, C](theta_1, sigma),
          TsubstFO[A, B, C](theta_2, sigma))
      case (Syntax.Differential(theta), sigma) =>
        Syntax.Differential[A, C](TsubstFO[A, B, C](theta, sigma))
    }

  def OsubstFO[A, B,
  C](x0: Syntax.ODE[Sum_Type.sum[A, B], C],
     sigma: B => Syntax.trm[A, C]):
  Syntax.ODE[A, C]
  =
    (x0, sigma) match {
      case (Syntax.OVar(c), sigma) => Syntax.OVar[C, A](c)
      case (Syntax.OSing(x, theta), sigma) =>
        Syntax.OSing[C, A](x, TsubstFO[A, B, C](theta, sigma))
      case (Syntax.OProd(oDE1, oDE2), sigma) =>
        Syntax.oprod[A, C](OsubstFO[A, B, C](oDE1, sigma),
          OsubstFO[A, B, C](oDE2, sigma))
    }

  def PsubstFO[A, B, C,
  D](x0: Syntax.hp[Sum_Type.sum[A, B], C, D],
     sigma: B => Syntax.trm[A, D]):
  Syntax.hp[A, C, D]
  =
    (x0, sigma) match {
      case (Syntax.Pvar(a), sigma) => Syntax.Pvar[D, A, C](a)
      case (Syntax.Assign(x, theta), sigma) =>
        Syntax.Assign[D, A, C](x, TsubstFO[A, B, D](theta, sigma))
      case (Syntax.DiffAssign(x, theta), sigma) =>
        Syntax.DiffAssign[D, A, C](x, TsubstFO[A, B, D](theta, sigma))
      case (Syntax.Test(phi), sigma) =>
        Syntax.Test[A, C, D](FsubstFO[A, B, C, D](phi, sigma))
      case (Syntax.EvolveODE(ode, phi), sigma) =>
        Syntax.EvolveODE[A, D,
          C](OsubstFO[A, B, D](ode, sigma),
          FsubstFO[A, B, C, D](phi, sigma))
      case (Syntax.Choice(alpha, beta), sigma) =>
        Syntax.Choice[A, C,
          D](PsubstFO[A, B, C, D](alpha, sigma),
          PsubstFO[A, B, C, D](beta, sigma))
      case (Syntax.Sequence(alpha, beta), sigma) =>
        Syntax.Sequence[A, C,
          D](PsubstFO[A, B, C, D](alpha, sigma),
          PsubstFO[A, B, C, D](beta, sigma))
      case (Syntax.Loop(alpha), sigma) =>
        Syntax.Loop[A, C, D](PsubstFO[A, B, C, D](alpha, sigma))
    }

  def FsubstFO[A, B, C,
  D](x0: Syntax.formula[Sum_Type.sum[A, B], C, D],
     sigma: B => Syntax.trm[A, D]):
  Syntax.formula[A, C, D]
  =
    (x0, sigma) match {
      case (Syntax.Geq(theta_1, theta_2), sigma) =>
        Syntax.Geq[A, D,
          C](TsubstFO[A, B, D](theta_1, sigma),
          TsubstFO[A, B, D](theta_2, sigma))
      case (Syntax.Prop(p, args), sigma) =>
        Syntax.Prop[D, A, C](p, ((i: D) => TsubstFO[A, B, D](args(i), sigma)))
      case (Syntax.Not(phi), sigma) =>
        Syntax.Not[A, C, D](FsubstFO[A, B, C, D](phi, sigma))
      case (Syntax.And(phi, psi), sigma) =>
        Syntax.And[A, C,
          D](FsubstFO[A, B, C, D](phi, sigma),
          FsubstFO[A, B, C, D](psi, sigma))
      case (Syntax.Exists(x, phi), sigma) =>
        Syntax.Exists[D, A, C](x, FsubstFO[A, B, C, D](phi, sigma))
      case (Syntax.Diamond(alpha, phi), sigma) =>
        Syntax.Diamond[A, C,
          D](PsubstFO[A, B, C, D](alpha, sigma),
          FsubstFO[A, B, C, D](phi, sigma))
      case (Syntax.InContext(c, phi), sigma) =>
        Syntax.InContext[C, A, D](c, FsubstFO[A, B, C, D](phi, sigma))
    }

  def PPsubst[A, B, C,
  D](x0: Syntax.hp[A, Sum_Type.sum[B, C], D],
     sigma: C => Syntax.formula[A, B, D]):
  Syntax.hp[A, B, D]
  =
    (x0, sigma) match {
      case (Syntax.Pvar(a), sigma) => Syntax.Pvar[D, A, B](a)
      case (Syntax.Assign(x, theta), sigma) => Syntax.Assign[D, A, B](x, theta)
      case (Syntax.DiffAssign(x, theta), sigma) =>
        Syntax.DiffAssign[D, A, B](x, theta)
      case (Syntax.Test(phi), sigma) =>
        Syntax.Test[A, B, D](PFsubst[A, B, C, D](phi, sigma))
      case (Syntax.EvolveODE(ode, phi), sigma) =>
        Syntax.EvolveODE[A, D, B](ode, PFsubst[A, B, C, D](phi, sigma))
      case (Syntax.Choice(alpha, beta), sigma) =>
        Syntax.Choice[A, B,
          D](PPsubst[A, B, C, D](alpha, sigma),
          PPsubst[A, B, C, D](beta, sigma))
      case (Syntax.Sequence(alpha, beta), sigma) =>
        Syntax.Sequence[A, B,
          D](PPsubst[A, B, C, D](alpha, sigma),
          PPsubst[A, B, C, D](beta, sigma))
      case (Syntax.Loop(alpha), sigma) =>
        Syntax.Loop[A, B, D](PPsubst[A, B, C, D](alpha, sigma))
    }

  def PFsubst[A, B, C,
  D](x0: Syntax.formula[A, Sum_Type.sum[B, C], D],
     sigma: C => Syntax.formula[A, B, D]):
  Syntax.formula[A, B, D]
  =
    (x0, sigma) match {
      case (Syntax.Geq(theta_1, theta_2), sigma) =>
        Syntax.Geq[A, D, B](theta_1, theta_2)
      case (Syntax.Prop(p, args), sigma) => Syntax.Prop[D, A, B](p, args)
      case (Syntax.Not(phi), sigma) =>
        Syntax.Not[A, B, D](PFsubst[A, B, C, D](phi, sigma))
      case (Syntax.And(phi, psi), sigma) =>
        Syntax.And[A, B,
          D](PFsubst[A, B, C, D](phi, sigma),
          PFsubst[A, B, C, D](psi, sigma))
      case (Syntax.Exists(x, phi), sigma) =>
        Syntax.Exists[D, A, B](x, PFsubst[A, B, C, D](phi, sigma))
      case (Syntax.Diamond(alpha, phi), sigma) =>
        Syntax.Diamond[A, B,
          D](PPsubst[A, B, C, D](alpha, sigma),
          PFsubst[A, B, C, D](phi, sigma))
      case (Syntax.InContext(c, phi), sigma) =>
        (c match {
          case Sum_Type.Inl(ca) =>
            Syntax.InContext[B, A, D](ca, PFsubst[A, B, C, D](phi, sigma))
          case Sum_Type.Inr(a) => sigma(a)
        })
    }

  def Tsubst[A, B, C](x0: Syntax.trm[A, B], sigma: subst_ext[A, C, B, Unit]):
  Syntax.trm[A, B]
  =
    (x0, sigma) match {
      case (Syntax.Var(x), sigma) => Syntax.Var[B, A](x)
      case (Syntax.DiffVar(x), sigma) => Syntax.DiffVar[B, A](x)
      case (Syntax.Const(r), sigma) => Syntax.Const[A, B](r)
      case (Syntax.Function(f, args), sigma) =>
        ((SFunctions[A, C, B, Unit](sigma)).apply(f) match {
          case None => ((a: B => Syntax.trm[A, B]) => Syntax.Function[A, B](f, a))
          case Some(a) => ((b: B => Syntax.trm[A, B]) => TsubstFO[A, B, B](a, b))
        })(((i: B) => Tsubst[A, B, C](args(i), sigma)))
      case (Syntax.Functional(f), sigma) =>

        ((SFunls[A, C, B, Unit](sigma)).apply(f) match {
          case None =>
            Syntax.Functional[A, B](f)
          case Some(fa) =>
            fa
        })
      case (Syntax.Plus(theta_1, theta_2), sigma) =>
        Syntax.Plus[A, B](Tsubst[A, B, C](theta_1, sigma),
          Tsubst[A, B, C](theta_2, sigma))
      case (Syntax.Times(theta_1, theta_2), sigma) =>
        Syntax.Times[A, B](Tsubst[A, B, C](theta_1, sigma),
          Tsubst[A, B, C](theta_2, sigma))
      case (Syntax.Differential(theta), sigma) =>
        Syntax.Differential[A, B](Tsubst[A, B, C](theta, sigma))
    }

  def SODEs[A, B, C, D](x0: subst_ext[A, B, C, D]): C => Option[Syntax.ODE[A, C]]
  =
    x0 match {
      case subst_exta(sFunctions, sFunls, sPredicates, sContexts, sPrograms, sODEs,
      more)
      => sODEs
    }

  def Osubst[A, B, C](x0: Syntax.ODE[A, B], sigma: subst_ext[A, C, B, Unit]):
  Syntax.ODE[A, B]
  =
    (x0, sigma) match {
      case (Syntax.OVar(c), sigma) =>
        ((SODEs[A, C, B, Unit](sigma)).apply(c) match {
          case None => Syntax.OVar[B, A](c)
          case Some(ca) => ca
        })
      case (Syntax.OSing(x, theta), sigma) =>
        Syntax.OSing[B, A](x, Tsubst[A, B, C](theta, sigma))
      case (Syntax.OProd(oDE1, oDE2), sigma) =>
        Syntax.oprod[A, B](Osubst[A, B, C](oDE1, sigma),
          Osubst[A, B, C](oDE2, sigma))
    }

  def Psubst[A, B, C](x0: Syntax.hp[A, B, C], sigma: subst_ext[A, B, C, Unit]):
  Syntax.hp[A, B, C]
  =
    (x0, sigma) match {
      case (Syntax.Pvar(a), sigma) =>
        ((SPrograms[A, B, C, Unit](sigma)).apply(a) match {
          case None => Syntax.Pvar[C, A, B](a)
          case Some(aa) => aa
        })
      case (Syntax.Assign(x, theta), sigma) =>
        Syntax.Assign[C, A, B](x, Tsubst[A, C, B](theta, sigma))
      case (Syntax.DiffAssign(x, theta), sigma) =>
        Syntax.DiffAssign[C, A, B](x, Tsubst[A, C, B](theta, sigma))
      case (Syntax.Test(phi), sigma) =>
        Syntax.Test[A, B, C](Fsubst[A, B, C](phi, sigma))
      case (Syntax.EvolveODE(ode, phi), sigma) =>
        Syntax.EvolveODE[A, C,
          B](Osubst[A, C, B](ode, sigma),
          Fsubst[A, B, C](phi, sigma))
      case (Syntax.Choice(alpha, beta), sigma) =>
        Syntax.Choice[A, B,
          C](Psubst[A, B, C](alpha, sigma),
          Psubst[A, B, C](beta, sigma))
      case (Syntax.Sequence(alpha, beta), sigma) =>
        Syntax.Sequence[A, B,
          C](Psubst[A, B, C](alpha, sigma),
          Psubst[A, B, C](beta, sigma))
      case (Syntax.Loop(alpha), sigma) =>
        Syntax.Loop[A, B, C](Psubst[A, B, C](alpha, sigma))
    }

  def Fsubst[A, B,
  C](x0: Syntax.formula[A, B, C], sigma: subst_ext[A, B, C, Unit]):
  Syntax.formula[A, B, C]
  =
    (x0, sigma) match {
      case (Syntax.Geq(theta_1, theta_2), sigma) =>
        Syntax.Geq[A, C,
          B](Tsubst[A, C, B](theta_1, sigma),
          Tsubst[A, C, B](theta_2, sigma))
      case (Syntax.Prop(p, args), sigma) =>
        ((SPredicates[A, B, C, Unit](sigma)).apply(p) match {
          case None =>
            Syntax.Prop[C, A, B](p, ((i: C) => Tsubst[A, C, B](args(i), sigma)))
          case Some(pa) =>
            FsubstFO[A, C, B, C](pa, ((i: C) => Tsubst[A, C, B](args(i), sigma)))
        })
      case (Syntax.Not(phi), sigma) =>
        Syntax.Not[A, B, C](Fsubst[A, B, C](phi, sigma))
      case (Syntax.And(phi, psi), sigma) =>
        Syntax.And[A, B,
          C](Fsubst[A, B, C](phi, sigma), Fsubst[A, B, C](psi, sigma))
      case (Syntax.Exists(x, phi), sigma) =>
        Syntax.Exists[C, A, B](x, Fsubst[A, B, C](phi, sigma))
      case (Syntax.Diamond(alpha, phi), sigma) =>
        Syntax.Diamond[A, B,
          C](Psubst[A, B, C](alpha, sigma),
          Fsubst[A, B, C](phi, sigma))
      case (Syntax.InContext(c, phi), sigma) =>
        ((SContexts[A, B, C, Unit](sigma)).apply(c) match {
          case None => Syntax.InContext[B, A, C](c, Fsubst[A, B, C](phi, sigma))
          case Some(ca) =>
            PFsubst[A, B, Unit, C](ca, ((_: Unit) => Fsubst[A, B, C](phi, sigma)))
        })
    }

  def Tadmit[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](x1: subst_ext[A, B, C, Unit],
                             x2: Syntax.trm[A, C]):
  Boolean
  =
    Predicate.holds(Scratch.Tadmit_i_i[A, B, C](x1, x2))

  def FUadmit[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](sigma: subst_ext[A, B, C, Unit],
                             theta: Syntax.formula[A, B, C], u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[Sum_Type.sum[A, Sum_Type.sum[B, C]],
      Set.set[Sum_Type.sum[C, C]]](((a: Sum_Type.sum[A, Sum_Type.sum[B, C]]) =>
      SFV[A, B, C](sigma, a)),
      Set.inf_set[Sum_Type.sum[A,
        Sum_Type.sum[B, C]]](SDom[A, B, C](sigma),
        Static_Semantics.SIGF[A, B, C](theta)))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def PUadmit[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](sigma: subst_ext[A, B, C, Unit],
                             theta: Syntax.hp[A, B, C], u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[Sum_Type.sum[A, Sum_Type.sum[B, C]],
      Set.set[Sum_Type.sum[C, C]]](((a: Sum_Type.sum[A, Sum_Type.sum[B, C]]) =>
      SFV[A, B, C](sigma, a)),
      Set.inf_set[Sum_Type.sum[A,
        Sum_Type.sum[B, C]]](SDom[A, B, C](sigma),
        Static_Semantics.SIGP[A, B, C](theta)))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def TUadmit[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](sigma: subst_ext[A, B, C, Unit],
                             theta: Syntax.trm[A, C], u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[A,
      Set.set[Sum_Type.sum[C, C]]](((i: A) =>
      Set.sup_set[Sum_Type.sum[C,
        C]](((SFunctions[A, B, C, Unit](sigma)).apply(i) match {
        case None => Set.bot_set[Sum_Type.sum[C, C]]
        case Some(a) =>
          Static_Semantics.FVT[Sum_Type.sum[A, C], C](a)
      }),
        ((SFunls[A, B, C, Unit](sigma)).apply(i) match {
          case None => Set.bot_set[Sum_Type.sum[C, C]]
          case Some(a) => Static_Semantics.FVT[A, C](a)
        }))),
      Static_Semantics.SIGT[A, C](theta))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def TadmitF[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](x1: subst_ext[A, B, C, Unit],
                             x2: Syntax.trm[A, C]):
  Boolean
  =
    Predicate.holds(Scratch.TadmitF_i_i[A, B, C](x1, x2))

  def NTUadmit[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](sigma: A => Syntax.trm[B, C],
                             theta: Syntax.trm[Sum_Type.sum[B, A], C], u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[A,
      Set.set[Sum_Type.sum[C, C]]](((i: A) => Static_Semantics.FVT[B, C](sigma(i))),
      Set.image[A,
        A](((i: A) => i),
        Set.vimage[A, Sum_Type.sum[B, A]](((a: A) => Sum_Type.Inr[A, B](a)),
          Static_Semantics.SIGT[Sum_Type.sum[B, A], C](theta))))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def PFUadmit[A, B, C,
  D](sigma: A => Syntax.formula[B, C, D],
     theta: Syntax.formula[B, Sum_Type.sum[C, A], D],
     u: Set.set[Sum_Type.sum[D, D]]):
  Boolean
  =
    true

  def PPUadmit[A : Enum.enum : HOL.equal, B, C,
  D : Enum.enum : HOL.equal](sigma: A => Syntax.formula[B, C, D],
                             theta: Syntax.hp[B, Sum_Type.sum[C, A], D], u: Set.set[Sum_Type.sum[D, D]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[D, D]](Set.inf_set[Sum_Type.sum[D,
      D]](Complete_Lattices.Sup_set[Sum_Type.sum[D,
      D]](Set.image[A,
      Set.set[Sum_Type.sum[D, D]]](((i: A) =>
      Static_Semantics.FVF[B, C, D](sigma(i))),
      Set.top_set[A])),
      u),
      Set.bot_set[Sum_Type.sum[D, D]])

  def TadmitFO[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x1: A => Syntax.trm[B, C],
                             x2: Syntax.trm[Sum_Type.sum[B, A], C]):
  Boolean
  =
    Predicate.holds(Scratch.TadmitFO_i_i[A, B, C](x1, x2))

  def FUadmitFO[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal,
  D : HOL.equal](sigma: A => Syntax.trm[B, C],
                 theta: Syntax.formula[Sum_Type.sum[B, A], D, C],
                 u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[A,
      Set.set[Sum_Type.sum[C, C]]](((i: A) => Static_Semantics.FVT[B, C](sigma(i))),
      Set.image[A,
        A](((i: A) => i),
        Set.vimage[A, Sum_Type.sum[Sum_Type.sum[B, A],
          Sum_Type.sum[D,
            C]]](((i: A) =>
          Sum_Type.Inl[Sum_Type.sum[B, A],
            Sum_Type.sum[D, C]](Sum_Type.Inr[A, B](i))),
          Static_Semantics.SIGF[Sum_Type.sum[B, A], D, C](theta))))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def OUadmitFO[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](sigma: A => Syntax.trm[B, C],
                             theta: Syntax.ODE[Sum_Type.sum[B, A], C], u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[A,
      Set.set[Sum_Type.sum[C, C]]](((i: A) => Static_Semantics.FVT[B, C](sigma(i))),
      Set.image[A,
        A](((i: A) => i),
        Set.vimage[A, Sum_Type.sum[Sum_Type.sum[B, A],
          C]](((i: A) =>
          Sum_Type.Inl[Sum_Type.sum[B, A], C](Sum_Type.Inr[A, B](i))),
          Static_Semantics.SIGO[Sum_Type.sum[B, A], C](theta))))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def PUadmitFO[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal,
  D : HOL.equal](sigma: A => Syntax.trm[B, C],
                 theta: Syntax.hp[Sum_Type.sum[B, A], D, C],
                 u: Set.set[Sum_Type.sum[C, C]]):
  Boolean
  =
    Set.equal_seta[Sum_Type.sum[C, C]](Set.inf_set[Sum_Type.sum[C,
      C]](Complete_Lattices.Sup_set[Sum_Type.sum[C,
      C]](Set.image[A,
      Set.set[Sum_Type.sum[C, C]]](((i: A) => Static_Semantics.FVT[B, C](sigma(i))),
      Set.image[A,
        A](((i: A) => i),
        Set.vimage[A, Sum_Type.sum[Sum_Type.sum[B, A],
          Sum_Type.sum[D,
            C]]](((i: A) =>
          Sum_Type.Inl[Sum_Type.sum[B, A],
            Sum_Type.sum[D, C]](Sum_Type.Inr[A, B](i))),
          Static_Semantics.SIGP[Sum_Type.sum[B, A], D, C](theta))))),
      u),
      Set.bot_set[Sum_Type.sum[C, C]])

  def TadmitFFO[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x1: A => Syntax.trm[B, C],
                             x2: Syntax.trm[Sum_Type.sum[B, A], C]):
  Boolean
  =
    Predicate.holds(Scratch.TadmitFFO_i_i[A, B, C](x1, x2))

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
  final case class i12() extends myvars
  final case class i13() extends myvars
  final case class i14() extends myvars
  final case class i15() extends myvars
  final case class i16() extends myvars
  final case class i17() extends myvars
  final case class i18() extends myvars
  final case class i19() extends myvars
  final case class i20() extends myvars


  def enum_all_myvars(p: myvars => Boolean): Boolean =
    Lista.list_all[myvars](p, List(i1(), i2(), i3(), i4(), i5(), i6(), i7(), i8(),
      i9(), i10(), i11(), i12(), i13(), i14(),
      i15(), i16(), i17(), i18(), i19(), i20()))

  def enum_ex_myvars(p: myvars => Boolean): Boolean =
    Lista.list_ex[myvars](p, List(i1(), i2(), i3(), i4(), i5(), i6(), i7(), i8(),
      i9(), i10(), i11(), i12(), i13(), i14(), i15(),
      i16(), i17(), i18(), i19(), i20()))

  def enum_myvarsa: List[myvars] =
    List(i1(), i2(), i3(), i4(), i5(), i6(), i7(), i8(), i9(), i10(), i11(),
      i12(), i13(), i14(), i15(), i16(), i17(), i18(), i19(), i20())


  def equal_myvarsa(x0: myvars, x1: myvars): Boolean = (x0, x1) match {
    case (i19(), i20()) => false
    case (i20(), i19()) => false
    case (i18(), i20()) => false
    case (i20(), i18()) => false
    case (i18(), i19()) => false
    case (i19(), i18()) => false
    case (i17(), i20()) => false
    case (i20(), i17()) => false
    case (i17(), i19()) => false
    case (i19(), i17()) => false
    case (i17(), i18()) => false
    case (i18(), i17()) => false
    case (i16(), i20()) => false
    case (i20(), i16()) => false
    case (i16(), i19()) => false
    case (i19(), i16()) => false
    case (i16(), i18()) => false
    case (i18(), i16()) => false
    case (i16(), i17()) => false
    case (i17(), i16()) => false
    case (i15(), i20()) => false
    case (i20(), i15()) => false
    case (i15(), i19()) => false
    case (i19(), i15()) => false
    case (i15(), i18()) => false
    case (i18(), i15()) => false
    case (i15(), i17()) => false
    case (i17(), i15()) => false
    case (i15(), i16()) => false
    case (i16(), i15()) => false
    case (i14(), i20()) => false
    case (i20(), i14()) => false
    case (i14(), i19()) => false
    case (i19(), i14()) => false
    case (i14(), i18()) => false
    case (i18(), i14()) => false
    case (i14(), i17()) => false
    case (i17(), i14()) => false
    case (i14(), i16()) => false
    case (i16(), i14()) => false
    case (i14(), i15()) => false
    case (i15(), i14()) => false
    case (i13(), i20()) => false
    case (i20(), i13()) => false
    case (i13(), i19()) => false
    case (i19(), i13()) => false
    case (i13(), i18()) => false
    case (i18(), i13()) => false
    case (i13(), i17()) => false
    case (i17(), i13()) => false
    case (i13(), i16()) => false
    case (i16(), i13()) => false
    case (i13(), i15()) => false
    case (i15(), i13()) => false
    case (i13(), i14()) => false
    case (i14(), i13()) => false
    case (i12(), i20()) => false
    case (i20(), i12()) => false
    case (i12(), i19()) => false
    case (i19(), i12()) => false
    case (i12(), i18()) => false
    case (i18(), i12()) => false
    case (i12(), i17()) => false
    case (i17(), i12()) => false
    case (i12(), i16()) => false
    case (i16(), i12()) => false
    case (i12(), i15()) => false
    case (i15(), i12()) => false
    case (i12(), i14()) => false
    case (i14(), i12()) => false
    case (i12(), i13()) => false
    case (i13(), i12()) => false
    case (i11(), i20()) => false
    case (i20(), i11()) => false
    case (i11(), i19()) => false
    case (i19(), i11()) => false
    case (i11(), i18()) => false
    case (i18(), i11()) => false
    case (i11(), i17()) => false
    case (i17(), i11()) => false
    case (i11(), i16()) => false
    case (i16(), i11()) => false
    case (i11(), i15()) => false
    case (i15(), i11()) => false
    case (i11(), i14()) => false
    case (i14(), i11()) => false
    case (i11(), i13()) => false
    case (i13(), i11()) => false
    case (i11(), i12()) => false
    case (i12(), i11()) => false
    case (i10(), i20()) => false
    case (i20(), i10()) => false
    case (i10(), i19()) => false
    case (i19(), i10()) => false
    case (i10(), i18()) => false
    case (i18(), i10()) => false
    case (i10(), i17()) => false
    case (i17(), i10()) => false
    case (i10(), i16()) => false
    case (i16(), i10()) => false
    case (i10(), i15()) => false
    case (i15(), i10()) => false
    case (i10(), i14()) => false
    case (i14(), i10()) => false
    case (i10(), i13()) => false
    case (i13(), i10()) => false
    case (i10(), i12()) => false
    case (i12(), i10()) => false
    case (i10(), i11()) => false
    case (i11(), i10()) => false
    case (i9(), i20()) => false
    case (i20(), i9()) => false
    case (i9(), i19()) => false
    case (i19(), i9()) => false
    case (i9(), i18()) => false
    case (i18(), i9()) => false
    case (i9(), i17()) => false
    case (i17(), i9()) => false
    case (i9(), i16()) => false
    case (i16(), i9()) => false
    case (i9(), i15()) => false
    case (i15(), i9()) => false
    case (i9(), i14()) => false
    case (i14(), i9()) => false
    case (i9(), i13()) => false
    case (i13(), i9()) => false
    case (i9(), i12()) => false
    case (i12(), i9()) => false
    case (i9(), i11()) => false
    case (i11(), i9()) => false
    case (i9(), i10()) => false
    case (i10(), i9()) => false
    case (i8(), i20()) => false
    case (i20(), i8()) => false
    case (i8(), i19()) => false
    case (i19(), i8()) => false
    case (i8(), i18()) => false
    case (i18(), i8()) => false
    case (i8(), i17()) => false
    case (i17(), i8()) => false
    case (i8(), i16()) => false
    case (i16(), i8()) => false
    case (i8(), i15()) => false
    case (i15(), i8()) => false
    case (i8(), i14()) => false
    case (i14(), i8()) => false
    case (i8(), i13()) => false
    case (i13(), i8()) => false
    case (i8(), i12()) => false
    case (i12(), i8()) => false
    case (i8(), i11()) => false
    case (i11(), i8()) => false
    case (i8(), i10()) => false
    case (i10(), i8()) => false
    case (i8(), i9()) => false
    case (i9(), i8()) => false
    case (i7(), i20()) => false
    case (i20(), i7()) => false
    case (i7(), i19()) => false
    case (i19(), i7()) => false
    case (i7(), i18()) => false
    case (i18(), i7()) => false
    case (i7(), i17()) => false
    case (i17(), i7()) => false
    case (i7(), i16()) => false
    case (i16(), i7()) => false
    case (i7(), i15()) => false
    case (i15(), i7()) => false
    case (i7(), i14()) => false
    case (i14(), i7()) => false
    case (i7(), i13()) => false
    case (i13(), i7()) => false
    case (i7(), i12()) => false
    case (i12(), i7()) => false
    case (i7(), i11()) => false
    case (i11(), i7()) => false
    case (i7(), i10()) => false
    case (i10(), i7()) => false
    case (i7(), i9()) => false
    case (i9(), i7()) => false
    case (i7(), i8()) => false
    case (i8(), i7()) => false
    case (i6(), i20()) => false
    case (i20(), i6()) => false
    case (i6(), i19()) => false
    case (i19(), i6()) => false
    case (i6(), i18()) => false
    case (i18(), i6()) => false
    case (i6(), i17()) => false
    case (i17(), i6()) => false
    case (i6(), i16()) => false
    case (i16(), i6()) => false
    case (i6(), i15()) => false
    case (i15(), i6()) => false
    case (i6(), i14()) => false
    case (i14(), i6()) => false
    case (i6(), i13()) => false
    case (i13(), i6()) => false
    case (i6(), i12()) => false
    case (i12(), i6()) => false
    case (i6(), i11()) => false
    case (i11(), i6()) => false
    case (i6(), i10()) => false
    case (i10(), i6()) => false
    case (i6(), i9()) => false
    case (i9(), i6()) => false
    case (i6(), i8()) => false
    case (i8(), i6()) => false
    case (i6(), i7()) => false
    case (i7(), i6()) => false
    case (i5(), i20()) => false
    case (i20(), i5()) => false
    case (i5(), i19()) => false
    case (i19(), i5()) => false
    case (i5(), i18()) => false
    case (i18(), i5()) => false
    case (i5(), i17()) => false
    case (i17(), i5()) => false
    case (i5(), i16()) => false
    case (i16(), i5()) => false
    case (i5(), i15()) => false
    case (i15(), i5()) => false
    case (i5(), i14()) => false
    case (i14(), i5()) => false
    case (i5(), i13()) => false
    case (i13(), i5()) => false
    case (i5(), i12()) => false
    case (i12(), i5()) => false
    case (i5(), i11()) => false
    case (i11(), i5()) => false
    case (i5(), i10()) => false
    case (i10(), i5()) => false
    case (i5(), i9()) => false
    case (i9(), i5()) => false
    case (i5(), i8()) => false
    case (i8(), i5()) => false
    case (i5(), i7()) => false
    case (i7(), i5()) => false
    case (i5(), i6()) => false
    case (i6(), i5()) => false
    case (i4(), i20()) => false
    case (i20(), i4()) => false
    case (i4(), i19()) => false
    case (i19(), i4()) => false
    case (i4(), i18()) => false
    case (i18(), i4()) => false
    case (i4(), i17()) => false
    case (i17(), i4()) => false
    case (i4(), i16()) => false
    case (i16(), i4()) => false
    case (i4(), i15()) => false
    case (i15(), i4()) => false
    case (i4(), i14()) => false
    case (i14(), i4()) => false
    case (i4(), i13()) => false
    case (i13(), i4()) => false
    case (i4(), i12()) => false
    case (i12(), i4()) => false
    case (i4(), i11()) => false
    case (i11(), i4()) => false
    case (i4(), i10()) => false
    case (i10(), i4()) => false
    case (i4(), i9()) => false
    case (i9(), i4()) => false
    case (i4(), i8()) => false
    case (i8(), i4()) => false
    case (i4(), i7()) => false
    case (i7(), i4()) => false
    case (i4(), i6()) => false
    case (i6(), i4()) => false
    case (i4(), i5()) => false
    case (i5(), i4()) => false
    case (i3(), i20()) => false
    case (i20(), i3()) => false
    case (i3(), i19()) => false
    case (i19(), i3()) => false
    case (i3(), i18()) => false
    case (i18(), i3()) => false
    case (i3(), i17()) => false
    case (i17(), i3()) => false
    case (i3(), i16()) => false
    case (i16(), i3()) => false
    case (i3(), i15()) => false
    case (i15(), i3()) => false
    case (i3(), i14()) => false
    case (i14(), i3()) => false
    case (i3(), i13()) => false
    case (i13(), i3()) => false
    case (i3(), i12()) => false
    case (i12(), i3()) => false
    case (i3(), i11()) => false
    case (i11(), i3()) => false
    case (i3(), i10()) => false
    case (i10(), i3()) => false
    case (i3(), i9()) => false
    case (i9(), i3()) => false
    case (i3(), i8()) => false
    case (i8(), i3()) => false
    case (i3(), i7()) => false
    case (i7(), i3()) => false
    case (i3(), i6()) => false
    case (i6(), i3()) => false
    case (i3(), i5()) => false
    case (i5(), i3()) => false
    case (i3(), i4()) => false
    case (i4(), i3()) => false
    case (i2(), i20()) => false
    case (i20(), i2()) => false
    case (i2(), i19()) => false
    case (i19(), i2()) => false
    case (i2(), i18()) => false
    case (i18(), i2()) => false
    case (i2(), i17()) => false
    case (i17(), i2()) => false
    case (i2(), i16()) => false
    case (i16(), i2()) => false
    case (i2(), i15()) => false
    case (i15(), i2()) => false
    case (i2(), i14()) => false
    case (i14(), i2()) => false
    case (i2(), i13()) => false
    case (i13(), i2()) => false
    case (i2(), i12()) => false
    case (i12(), i2()) => false
    case (i2(), i11()) => false
    case (i11(), i2()) => false
    case (i2(), i10()) => false
    case (i10(), i2()) => false
    case (i2(), i9()) => false
    case (i9(), i2()) => false
    case (i2(), i8()) => false
    case (i8(), i2()) => false
    case (i2(), i7()) => false
    case (i7(), i2()) => false
    case (i2(), i6()) => false
    case (i6(), i2()) => false
    case (i2(), i5()) => false
    case (i5(), i2()) => false
    case (i2(), i4()) => false
    case (i4(), i2()) => false
    case (i2(), i3()) => false
    case (i3(), i2()) => false
    case (i1(), i20()) => false
    case (i20(), i1()) => false
    case (i1(), i19()) => false
    case (i19(), i1()) => false
    case (i1(), i18()) => false
    case (i18(), i1()) => false
    case (i1(), i17()) => false
    case (i17(), i1()) => false
    case (i1(), i16()) => false
    case (i16(), i1()) => false
    case (i1(), i15()) => false
    case (i15(), i1()) => false
    case (i1(), i14()) => false
    case (i14(), i1()) => false
    case (i1(), i13()) => false
    case (i13(), i1()) => false
    case (i1(), i12()) => false
    case (i12(), i1()) => false
    case (i1(), i11()) => false
    case (i11(), i1()) => false
    case (i1(), i10()) => false
    case (i10(), i1()) => false
    case (i1(), i9()) => false
    case (i9(), i1()) => false
    case (i1(), i8()) => false
    case (i8(), i1()) => false
    case (i1(), i7()) => false
    case (i7(), i1()) => false
    case (i1(), i6()) => false
    case (i6(), i1()) => false
    case (i1(), i5()) => false
    case (i5(), i1()) => false
    case (i1(), i4()) => false
    case (i4(), i1()) => false
    case (i1(), i3()) => false
    case (i3(), i1()) => false
    case (i1(), i2()) => false
    case (i2(), i1()) => false
    case (i20(), i20()) => true
    case (i19(), i19()) => true
    case (i18(), i18()) => true
    case (i17(), i17()) => true
    case (i16(), i16()) => true
    case (i15(), i15()) => true
    case (i14(), i14()) => true
    case (i13(), i13()) => true
    case (i12(), i12()) => true
    case (i11(), i11()) => true
    case (i10(), i10()) => true
    case (i9(), i9()) => true
    case (i8(), i8()) => true
    case (i7(), i7()) => true
    case (i6(), i6()) => true
    case (i5(), i5()) => true
    case (i4(), i4()) => true
    case (i3(), i3()) => true
    case (i2(), i2()) => true
    case (i1(), i1()) => true
  }
  def x: myvars = i1()

  def y: myvars = i2()

  def z: myvars = i3()

  def ddl_join(s: List[String.char], x1: List[List[String.char]]):
  List[String.char]
  =
    (s, x1) match {
      case (s, Nil) => Nil
      case (sa, List(s)) => s
      case (sa, s :: v :: va) => s ++ (sa ++ ddl_join(sa, v :: va))
    }

  def ddl_hpid_to_string(vid: myvars): List[String.char] = s"${vid}".toList.map(String.Char.ofChar)
    /*(if (equal_myvarsa(vid, x))
      List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, y))
      List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, z))
      List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))),
        String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))
    else List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))),
      String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))))
*/
  def ddl_vid_to_string(vid: myvars): List[String.char] = s"${vid}".toList.map(String.Char.ofChar)
    /*(if (equal_myvarsa(vid, x))
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, y))
      List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, z))
      List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))))
    else List(String.Char(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One())))))))))))
*/
  def ddl_fid_to_string(vid: myvars): List[String.char] = s"${vid}".toList.map(String.Char.ofChar)
/*    (if (equal_myvarsa(vid, i1()))
      List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, i2()))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, i3()))
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.One()))))))))
    else List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.One())))))))))))
*/
  def ddl_trm_to_string(x0: Syntax.trm[myvars, myvars]): List[String.char] = x0
  match {
    case Syntax.Var(x) => ddl_vid_to_string(x)
    case Syntax.Const(r) =>
      val(Ratreal(Frct((int_of_integer(n),int_of_integer(d))))) = r
      s"$n/$d".toList.map(String.Char.ofChar)
      //List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.One()))))))))
    case Syntax.Function(f, args) => ddl_fid_to_string(f)
    case Syntax.Functional(f) => ddl_fid_to_string(f)++ddl_fid_to_string(f)
    case Syntax.Plus(t1, t2) =>
      ddl_trm_to_string(t1) ++
        (List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
          ddl_trm_to_string(t2))
    case Syntax.Times(t1, t2) =>
      ddl_trm_to_string(t1) ++
        (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
          ddl_trm_to_string(t2))
    case Syntax.DiffVar(x) =>
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One()))))))),
        String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))) ++
        (ddl_vid_to_string(x) ++
          List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))))
    case Syntax.Differential(t) =>
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
        String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))) ++
        (ddl_trm_to_string(t) ++
          List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))))
  }

  def ddl_oid_to_string(vid: myvars): List[String.char] =
    (if (equal_myvarsa(vid, x))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))))
    else (if (equal_myvarsa(vid, y))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))),
        String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))
    else (if (equal_myvarsa(vid, z))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))),
        String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))
    else List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.One()))))))),
      String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.One()))))))))))

  val PRINT_ASSOC = true

  def ddl_ode_to_string(x0: Syntax.ODE[myvars, myvars]): List[String.char] = x0
  match {
    case Syntax.OVar(x) => ddl_oid_to_string(x)
    case Syntax.OSing(x, t) =>
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))) ++
        (ddl_vid_to_string(x) ++
          (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
            ddl_trm_to_string(t)))
    case Syntax.OProd(oDE1, oDE2) =>
      (if(PRINT_ASSOC) "{" else "").toList.map(String.Char.ofChar) ++
      ddl_ode_to_string(oDE1) ++
        (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
          String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
          ddl_ode_to_string(oDE2)) ++
      (if(PRINT_ASSOC) "}" else "").toList.map(String.Char.ofChar)
  }

  def ddl_ppid_to_string(vid: myvars): List[String.char] =
    (if (equal_myvarsa(vid, i1()))
      List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))))
    else (if (equal_myvarsa(vid, i2()))
      List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))))
    else (if (equal_myvarsa(vid, i3()))
      List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))))
    else List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.One())))))))))))

  def ddl_cid_to_string(vid: myvars): List[String.char] =
    (if (equal_myvarsa(vid, i1()))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))))
    else (if (equal_myvarsa(vid, i2()))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
        String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))
    else (if (equal_myvarsa(vid, i3()))
      List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
        String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.One())))))))
    else List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
      String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.One()))))))))))

  def ddl_fml_to_string(x0: Syntax.formula[myvars, myvars, myvars]):
  List[String.char]
  =
    x0 match {
      case Syntax.Geq(t1, t2) =>
        ddl_trm_to_string(t1) ++
          (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))),
            String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
            ddl_trm_to_string(t2))
      case Syntax.Prop(p, args) => s"Prop(${p})".toList.map(String.Char.ofChar)
      case Syntax.Not(p) =>
        (p match {
          case Syntax.Geq(_, _) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Prop(_, _) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Not(_) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.And(formula1, formula2) =>
            (formula1 match {
              case Syntax.Geq(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
              case Syntax.Prop(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
              case Syntax.Not(Syntax.Geq(trm1, trm2)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.Geq[myvars, myvars,
                          myvars](trm1, trm2)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.Prop(c, fun)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.Prop[myvars, myvars,
                          myvars](c, fun)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.Not(formula)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.Not[myvars, myvars,
                          myvars](formula)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.And(formula1a, formula2a)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.And[myvars, myvars,
                          myvars](formula1a, formula2a)))
                  case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _)))
                  => List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                    ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(pa), Syntax.Not(q))) =>
                    (if (Syntax.equal_formulaa[myvars, myvars,
                      myvars](formula1a, pa) &&
                      Syntax.equal_formulaa[myvars, myvars,
                        myvars](formula2a, q))
                      ddl_fml_to_string(formula1a) ++
                        (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))),
                          String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                          String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                          ddl_fml_to_string(formula2a))
                    else List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(Syntax.And[myvars, myvars,
                        myvars](Syntax.Not[myvars, myvars,
                        myvars](Syntax.And[myvars, myvars,
                        myvars](formula1a, formula2a)),
                        Syntax.Not[myvars, myvars,
                          myvars](Syntax.And[myvars, myvars,
                          myvars](Syntax.Not[myvars, myvars, myvars](pa),
                          Syntax.Not[myvars, myvars, myvars](q))))))
                  case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _)))
                  => List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                    ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(_),
                  Syntax.Diamond(_, _)))
                  => List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                    ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Not(_),
                  Syntax.InContext(_, _)))
                  => List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                    ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.Exists(c, formula)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.Exists[myvars, myvars,
                          myvars](c, formula)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.Diamond(hp, formula)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.Diamond[myvars, myvars,
                          myvars](hp, formula)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.Not(Syntax.InContext(b, formula)) =>
                (formula2 match {
                  case Syntax.Geq(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Prop(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Geq(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Prop(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Not(pa)) =>
                    ddl_fml_to_string(pa) ++
                      (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
                        String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
                        ddl_fml_to_string(Syntax.InContext[myvars, myvars,
                          myvars](b, formula)))
                  case Syntax.Not(Syntax.And(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Exists(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.Diamond(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Not(Syntax.InContext(_, _)) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.And(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Exists(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.Diamond(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                  case Syntax.InContext(_, _) =>
                    List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                      ddl_fml_to_string(p)
                })
              case Syntax.And(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
              case Syntax.Exists(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
              case Syntax.Diamond(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
              case Syntax.InContext(_, _) =>
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(p)
            })
          case Syntax.Exists(_, Syntax.Geq(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Exists(_, Syntax.Prop(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Exists(x, Syntax.Not(pa)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))))) ++
              (ddl_vid_to_string(x) ++
                (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                  ddl_fml_to_string(pa)))
          case Syntax.Exists(_, Syntax.And(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Exists(_, Syntax.Exists(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Exists(_, Syntax.Diamond(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Exists(_, Syntax.InContext(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(_, Syntax.Geq(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(_, Syntax.Prop(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(a, Syntax.Not(pa)) =>
            List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))))) ++
              (ddl_hp_to_string(a) ++
                (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))))) ++
                  ddl_fml_to_string(pa)))
          case Syntax.Diamond(_, Syntax.And(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(_, Syntax.Exists(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(_, Syntax.Diamond(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.Diamond(_, Syntax.InContext(_, _)) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
          case Syntax.InContext(_, _) =>
            List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)
        })
      case Syntax.And(p, q) =>
        ddl_fml_to_string(p) ++
          (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.One()))))))) ++
            ddl_fml_to_string(q))
      case Syntax.Exists(x, p) =>
        List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))))) ++
          (ddl_vid_to_string(x) ++
            (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
              String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
              String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              ddl_fml_to_string(p)))
      case Syntax.Diamond(a, p) =>
        List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
          (ddl_hp_to_string(a) ++
            (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
              ddl_fml_to_string(p)))
      case Syntax.InContext(c, p) =>
        (p match {
          case Syntax.Geq(_, _) => ddl_ppid_to_string(c)
          case Syntax.Prop(_, _) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
          case Syntax.Not(_) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
          case Syntax.And(_, _) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
          case Syntax.Exists(_, _) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
          case Syntax.Diamond(_, _) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
          case Syntax.InContext(_, _) =>
            ddl_cid_to_string(c) ++
              (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One()))))))) ++
                (ddl_fml_to_string(p) ++
                  List(String.Char(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
        })
    }

  def ddl_hp_to_string(x0: Syntax.hp[myvars, myvars, myvars]): List[String.char] =
    x0 match {
      case Syntax.Pvar(a) => ddl_hpid_to_string(a)
      case Syntax.Assign(x, e) =>
        ddl_vid_to_string(x) ++
          (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One())))))),
            String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
            ddl_trm_to_string(e))
      case Syntax.DiffAssign(x, e) =>
        List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
          String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))) ++
          (ddl_vid_to_string(x) ++
            (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))),
              String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One())))))),
              String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
              ddl_trm_to_string(e)))
      case Syntax.Test(p) =>
        List(String.Char(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))) ++
          ddl_fml_to_string(p)
      case Syntax.EvolveODE(ode, p) =>
        List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))) ++
          (ddl_ode_to_string(ode) ++
            (List(String.Char(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit0(Num.One()))))))) ++
              (ddl_fml_to_string(p) ++
                List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One())))))))))))
      case Syntax.Choice(a, b) =>
        ddl_hp_to_string(a) ++
          (List(String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))) ++
            ddl_hp_to_string(b))
      case Syntax.Sequence(a, b) =>
        ddl_hp_to_string(a) ++
          (List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One()))))))) ++
            ddl_hp_to_string(b))
      case Syntax.Loop(a) =>
        ddl_hp_to_string(a) ++
          List(String.Char(Num.Bit0(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))
    }

  def ddl_seq_to_string(x0: (List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])):
  List[String.char]
  =
    x0 match {
      case (a, s) =>
        ddl_join(List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
          String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
          Lista.map[Syntax.formula[myvars, myvars, myvars],
            List[String.char]](((aa:
                                 Syntax.formula[myvars, myvars, myvars])
          =>
            ddl_fml_to_string(aa)),
            a)) ++
          (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit1(Num.Bit1(Num.One()))))))),
            String.Char(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
            ddl_join(List(String.Char(Num.Bit0(Num.Bit0(Num.Bit1(Num.Bit1(Num.Bit0(Num.One())))))),
              String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
              Lista.map[Syntax.formula[myvars, myvars, myvars],
                List[String.char]](((aa:
                                     Syntax.formula[myvars, myvars, myvars])
              =>
                ddl_fml_to_string(aa)),
                s)))
    }

  def ddl_rule_to_string(x0: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars,
      myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))):
  List[String.char]
  =
    x0 match {
      case (sg, c) =>
        ddl_join(List(String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One())))))),
          String.Char(Num.Bit1(Num.Bit1(Num.Bit0(Num.Bit1(Num.Bit1(Num.One())))))),
          String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
          String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
          String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))),
          Lista.map[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]]),
            List[String.char]](((a:
                                 (List[Syntax.formula[myvars, myvars, myvars]],
                                   List[Syntax.formula[myvars, myvars, myvars]]))
          =>
            ddl_seq_to_string(a)),
            sg)) ++
          (List(String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One())))))),
            String.Char(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.Bit0(Num.One()))))))) ++
            ddl_seq_to_string(c))
    }



  def ddl_P(p: myvars): Syntax.formula[myvars, myvars, myvars] =
    Syntax.Predicational[myvars, myvars, myvars](p)

  def ddl_f0(f: myvars): Syntax.trm[myvars, myvars] =
    Syntax.Function[myvars, myvars](f, Syntax.empty[myvars, myvars])

  def ddl_singleton[A](t: Syntax.trm[A, myvars], i: myvars): Syntax.trm[A, myvars]
  =
    (if (equal_myvarsa(i, x)) t else Syntax.Const[A, myvars](Real.zero_real))

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

  def eq_i_i[A : HOL.equal](xa: A, xb: A): Predicate.pred[Unit] =
    Predicate.bind[(A, A),
      Unit](Predicate.single[(A, A)]((xa, xb)),
      ((a: (A, A)) =>
      {
        val (x, xaa): (A, A) = a;
        (if (HOL.eq[A](x, xaa)) Predicate.single[Unit](())
        else Predicate.bot_pred[Unit])
      }))

  def eq_i_o[A](xa: A): Predicate.pred[A] =
    Predicate.bind[A, A](Predicate.single[A](xa),
      ((a: A) => Predicate.single[A](a)))

  def ddl_start_proof(s: (List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])):
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (List(s), s)


  def ddl_TRadmit_i(x: Syntax.trm[myvars, myvars]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars, myvars],
      Unit](Predicate.single[Syntax.trm[myvars, myvars]](x),
      ((a: Syntax.trm[myvars, myvars]) =>
        (a match {
          case Syntax.Var(_) => Predicate.single[Unit](())
          case Syntax.Const(_) => Predicate.bot_pred[Unit]
          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars,
        myvars],
        Unit](Predicate.single[Syntax.trm[myvars,
        myvars]](x),
        ((a: Syntax.trm[myvars, myvars]) =>
          (a match {
            case Syntax.Var(_) => Predicate.bot_pred[Unit]
            case Syntax.Const(_) => Predicate.bot_pred[Unit]
            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
            case Syntax.DiffVar(_) => Predicate.single[Unit](())
            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars,
          myvars],
          Unit](Predicate.single[Syntax.trm[myvars, myvars]](x),
          ((a: Syntax.trm[myvars, myvars]) =>
            (a match {
              case Syntax.Var(_) => Predicate.bot_pred[Unit]
              case Syntax.Const(_) => Predicate.single[Unit](())
              case Syntax.Function(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Functional(_) => Predicate.bot_pred[Unit]
              case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
              case Syntax.Differential(_) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars, myvars],
            Unit](Predicate.single[Syntax.trm[myvars, myvars]](x),
            ((a: Syntax.trm[myvars, myvars]) =>
              (a match {
                case Syntax.Var(_) => Predicate.bot_pred[Unit]
                case Syntax.Const(_) => Predicate.bot_pred[Unit]
                case Syntax.Function(_, args) =>
                  Predicate.bind[Unit,
                    Unit](Predicate.if_pred(HOL.All[myvars](((i:
                                                              myvars)
                  =>
                    ddl_TRadmit(args(i))))),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.single[Unit](())
                    }))
                case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                case Syntax.Differential(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars,
              myvars],
              Unit](Predicate.single[Syntax.trm[myvars,
              myvars]](x),
              ((a: Syntax.trm[myvars, myvars]) =>
                (a match {
                  case Syntax.Var(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Const(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Function(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Functional(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Plus(t1, t2) =>
                    Predicate.bind[Unit,
                      Unit](ddl_TRadmit_i(t1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](ddl_TRadmit_i(t2), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.Times(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.DiffVar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Differential(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[myvars, myvars],
                Unit](Predicate.single[Syntax.trm[myvars, myvars]](x),
                ((a: Syntax.trm[myvars, myvars]) =>
                  (a match {
                    case Syntax.Var(_) => Predicate.bot_pred[Unit]
                    case Syntax.Const(_) => Predicate.bot_pred[Unit]
                    case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                    case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Times(t1, t2) =>
                      Predicate.bind[Unit,
                        Unit](ddl_TRadmit_i(t1),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](ddl_TRadmit_i(t2),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.bind[Syntax.trm[myvars, myvars],
                  Unit](Predicate.single[Syntax.trm[myvars, myvars]](x),
                  ((a: Syntax.trm[myvars, myvars]) =>
                    (a match {
                      case Syntax.Var(_) => Predicate.bot_pred[Unit]
                      case Syntax.Const(_) => Predicate.bot_pred[Unit]
                      case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                      case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Differential(t) =>
                        Predicate.bind[Unit,
                          Unit](ddl_TRadmit_i(t),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.bind[Unit,
                              Unit](dfree_i[myvars, myvars](t),
                              ((ab: Unit) =>
                              {
                                val (): Unit = ab;
                                Predicate.single[Unit](())
                              }))
                          }))
                    })))))))))

  def ddl_TRadmit(x1: Syntax.trm[myvars, myvars]): Boolean =
    Predicate.holds(ddl_TRadmit_i(x1))

  def ORadmit_i(xa: Syntax.ODE[myvars, myvars]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[myvars, myvars],
      Unit](Predicate.single[Syntax.ODE[myvars, myvars]](xa),
      ((a: Syntax.ODE[myvars, myvars]) =>
        (a match {
          case Syntax.OVar(_) => Predicate.bot_pred[Unit]
          case Syntax.OSing(_, theta) =>
            Predicate.bind[Unit,
              Unit](ddl_TRadmit_i(theta),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](dfree_i[myvars, myvars](theta),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
          case Syntax.OProd(_, _) => Predicate.bot_pred[Unit]
        }))),
      Predicate.bind[Syntax.ODE[myvars, myvars],
        Unit](Predicate.single[Syntax.ODE[myvars, myvars]](xa),
        ((a: Syntax.ODE[myvars, myvars]) =>
          (a match {
            case Syntax.OVar(_) => Predicate.bot_pred[Unit]
            case Syntax.OSing(_, _) => Predicate.bot_pred[Unit]
            case Syntax.OProd(oDE1, oDE2) =>
              Predicate.bind[Unit,
                Unit](ORadmit_i(oDE1),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](ORadmit_i(oDE2),
                    ((ab: Unit) => {
                      val (): Unit = ab;
                      Predicate.single[Unit](())
                    }))
                }))
          }))))

  def PRadmit_i(xa: Syntax.hp[myvars, myvars, myvars]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars, myvars, myvars],
      Unit](Predicate.single[Syntax.hp[myvars, myvars, myvars]](xa),
      ((a: Syntax.hp[myvars, myvars, myvars]) =>
        (a match {
          case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
          case Syntax.Assign(_, theta) =>
            Predicate.bind[Unit,
              Unit](ddl_TRadmit_i(theta),
              ((aa: Unit) => {
                val (): Unit = aa;
                Predicate.single[Unit](())
              }))
          case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Test(_) => Predicate.bot_pred[Unit]
          case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Loop(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars,
        myvars, myvars],
        Unit](Predicate.single[Syntax.hp[myvars, myvars,
        myvars]](xa),
        ((a: Syntax.hp[myvars, myvars, myvars]) =>
          (a match {
            case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
            case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
            case Syntax.DiffAssign(_, theta) =>
              Predicate.bind[Unit,
                Unit](ddl_TRadmit_i(theta),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case Syntax.Test(_) => Predicate.bot_pred[Unit]
            case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Loop(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars, myvars,
          myvars],
          Unit](Predicate.single[Syntax.hp[myvars, myvars, myvars]](xa),
          ((a: Syntax.hp[myvars, myvars, myvars]) =>
            (a match {
              case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
              case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffAssign(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Test(phi) =>
                Predicate.bind[Unit,
                  Unit](ddl_FRadmit_i(phi), ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
              case Syntax.EvolveODE(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Sequence(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Loop(_) => Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars, myvars, myvars],
            Unit](Predicate.single[Syntax.hp[myvars, myvars, myvars]](xa),
            ((a: Syntax.hp[myvars, myvars, myvars]) =>
              (a match {
                case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Test(_) => Predicate.bot_pred[Unit]
                case Syntax.EvolveODE(ode, phi) =>
                  Predicate.bind[Unit,
                    Unit](ORadmit_i(ode),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](ddl_FRadmit_i(phi),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Loop(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars,
              myvars, myvars],
              Unit](Predicate.single[Syntax.hp[myvars, myvars,
              myvars]](xa),
              ((a: Syntax.hp[myvars, myvars, myvars]) =>
                (a match {
                  case Syntax.Pvar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Assign(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.DiffAssign(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Test(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.EvolveODE(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Choice(aa, b) =>
                    Predicate.bind[Unit,
                      Unit](PRadmit_i(aa),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](PRadmit_i(b), ((ac: Unit) => {
                          val (): Unit = ac;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.Sequence(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Loop(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[myvars, myvars,
                myvars],
                Unit](Predicate.single[Syntax.hp[myvars, myvars, myvars]](xa),
                ((a: Syntax.hp[myvars, myvars, myvars]) =>
                  (a match {
                    case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.DiffAssign(_, _) =>
                      Predicate.bot_pred[Unit]
                    case Syntax.Test(_) => Predicate.bot_pred[Unit]
                    case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Sequence(aa, b) =>
                      Predicate.bind[Unit,
                        Unit](PRadmit_i(aa),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](PRadmit_i(b),
                            ((ac: Unit) =>
                            {
                              val (): Unit = ac;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.bind[Syntax.hp[myvars, myvars,
                  myvars],
                  Unit](Predicate.single[Syntax.hp[myvars, myvars, myvars]](xa),
                  ((a: Syntax.hp[myvars, myvars, myvars]) =>
                    (a match {
                      case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffAssign(_, _) =>
                        Predicate.bot_pred[Unit]
                      case Syntax.Test(_) => Predicate.bot_pred[Unit]
                      case Syntax.EvolveODE(_, _) =>
                        Predicate.bot_pred[Unit]
                      case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Loop(aa) =>
                        Predicate.bind[Unit,
                          Unit](PRadmit_i(aa), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    })))))))))

  def ddl_FRadmit_i(xa: Syntax.formula[myvars, myvars, myvars]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[myvars, myvars,
      myvars],
      Unit](Predicate.single[Syntax.formula[myvars, myvars, myvars]](xa),
      ((a: Syntax.formula[myvars, myvars, myvars]) =>
        (a match {
          case Syntax.Geq(theta_1, theta_2) =>
            Predicate.bind[Unit,
              Unit](ddl_TRadmit_i(theta_1),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](ddl_TRadmit_i(theta_2),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
          case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Not(_) => Predicate.bot_pred[Unit]
          case Syntax.And(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
          case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[myvars,
        myvars, myvars],
        Unit](Predicate.single[Syntax.formula[myvars,
        myvars, myvars]](xa),
        ((a: Syntax.formula[myvars, myvars, myvars])
        =>
          (a match {
            case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Prop(_, args) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[myvars](((i: myvars) =>
                ddl_TRadmit(args(i))))),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case Syntax.Not(_) => Predicate.bot_pred[Unit]
            case Syntax.And(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
            case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[myvars,
          myvars, myvars],
          Unit](Predicate.single[Syntax.formula[myvars, myvars,
          myvars]](xa),
          ((a: Syntax.formula[myvars, myvars, myvars]) =>
            (a match {
              case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Not(phi) =>
                Predicate.bind[Unit,
                  Unit](ddl_FRadmit_i(phi), ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
              case Syntax.And(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
              case Syntax.InContext(_, _) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[myvars, myvars, myvars],
            Unit](Predicate.single[Syntax.formula[myvars, myvars, myvars]](xa),
            ((a: Syntax.formula[myvars, myvars, myvars]) =>
              (a match {
                case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Not(_) => Predicate.bot_pred[Unit]
                case Syntax.And(phi, psi) =>
                  Predicate.bind[Unit,
                    Unit](ddl_FRadmit_i(phi),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](ddl_FRadmit_i(psi),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[myvars,
              myvars, myvars],
              Unit](Predicate.single[Syntax.formula[myvars, myvars,
              myvars]](xa),
              ((a: Syntax.formula[myvars, myvars, myvars])
              =>
                (a match {
                  case Syntax.Geq(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Prop(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Not(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.And(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Exists(_, phi) =>
                    Predicate.bind[Unit,
                      Unit](ddl_FRadmit_i(phi),
                      ((aa: Unit) => {
                        val (): Unit = aa;
                        Predicate.single[Unit](())
                      }))
                  case Syntax.Diamond(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.InContext(_, _) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.bind[Syntax.formula[myvars, myvars, myvars],
                Unit](Predicate.single[Syntax.formula[myvars,
                myvars, myvars]](xa),
                ((a: Syntax.formula[myvars, myvars, myvars])
                =>
                  (a match {
                    case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Not(_) => Predicate.bot_pred[Unit]
                    case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Diamond(alpha, phi) =>
                      Predicate.bind[Unit,
                        Unit](ddl_FRadmit_i(phi),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](PRadmit_i(alpha), ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                        }))
                    case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                  }))))))))

  def ddl_FRadmit(x1: Syntax.formula[myvars, myvars, myvars]): Boolean =
    Predicate.holds(ddl_FRadmit_i(x1))


  import Failure._

  def ddl_Rrule_result(x0: Proof_Checker.rrule[myvars, myvars, myvars],
                       j: Nat.nat,
                       x2: (List[Syntax.formula[myvars, myvars, myvars]],
                         List[Syntax.formula[myvars, myvars, myvars]])):
  Option[List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])]]
  =
    (x0, j, x2) match {
      case (Proof_Checker.AndR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(_) => fail()
          case Syntax.And(p, q) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j, p)),
              (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](s, j, q))))
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.ImplyR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a ++ List(p),
              Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](s, j) ++
                List(q))))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.EquivR(), j, (a, s)) => {
        val (Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
        Syntax.Not(Syntax.And(Syntax.Not(pa),
        Syntax.Not(qa)))))):
          Syntax.formula[myvars, myvars, myvars]
        = Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j);
        (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
          Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
          Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])]](List((a ++ List(p),
            Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](s, j) ++
              List(q)),
            (a ++ List(q),
              Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](s, j) ++
                List(p))))
        else fail())
      }
      case (Proof_Checker.CohideR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          List(Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j)))))
      case (Proof_Checker.CohideRR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((Nil,
          List(Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j)))))
      case (Proof_Checker.TrueR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(x, y) =>
            (if (Syntax.equal_trma[myvars, myvars](x, y) &&
              Syntax.equal_trma[myvars,
                myvars](x,
                Syntax.Const[myvars, myvars](Real.zero_real)))
              Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])]](Nil)
            else fail())
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(_) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.Skolem(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(_, _)) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.Geq(_, _))) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.Prop(_, _))) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.Not(p))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j, p))))
          case Syntax.Not(Syntax.Exists(_, Syntax.And(_, _))) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.Exists(_, _))) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.Diamond(_, _))) => fail()
          case Syntax.Not(Syntax.Exists(_, Syntax.InContext(_, _))) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.HideR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.closeI[Syntax.formula[myvars, myvars,
            myvars]](s, j))))
      case (Proof_Checker.CutRight(v), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j, v)),
          (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j,
            Syntax.Implies[myvars, myvars,
              myvars](v, Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
      case (Proof_Checker.EquivifyR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars, myvars](p, q)))))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.CommuteEquivR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
              myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars,
                myvars](q, p)))))
          else fail())
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        }
          )
      case (Proof_Checker.BRenameR(x, y), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(_, _)) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Geq(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Prop(_, _))) => None
          case Syntax.Not(Syntax.Exists(xvar, Syntax.Not(phi))) =>
            (if (equal_myvarsa(x, xvar) &&
              (ddl_FRadmit(Syntax.Forall[myvars, myvars,
                myvars](xvar, phi)) &&
                (ddl_FRadmit(phi) &&
                  (Syntax.fsafe[myvars, myvars,
                    myvars](Syntax.Forall[myvars, myvars,
                    myvars](xvar, phi)) &&
                    Set.equal_seta[Sum_Type.sum[myvars,
                      myvars]](Set.inf_set[Sum_Type.sum[myvars,
                      myvars]](Set.insert[Sum_Type.sum[myvars,
                      myvars]](Sum_Type.Inl[myvars, myvars](y),
                      Set.insert[Sum_Type.sum[myvars,
                        myvars]](Sum_Type.Inr[myvars, myvars](y),
                        Set.insert[Sum_Type.sum[myvars,
                          myvars]](Sum_Type.Inr[myvars, myvars](x),
                          Set.bot_set[Sum_Type.sum[myvars, myvars]]))),
                      Static_Semantics.FVF[myvars, myvars,
                        myvars](Syntax.Forall[myvars, myvars,
                        myvars](xvar, phi))),
                      Set.bot_set[Sum_Type.sum[myvars, myvars]])))))
              Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](s, j,
                ddl_FBrename(x, y,
                  Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
            else None)
          case Syntax.Not(Syntax.Exists(_, Syntax.And(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Exists(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Diamond(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.InContext(_, _))) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Pvar(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Geq(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Prop(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(xvar, theta),
          Syntax.Not(phi)))
          => (if (equal_myvarsa(x, xvar) &&
            (ddl_TRadmit(theta) &&
              (ddl_FRadmit(Syntax.Box[myvars, myvars,
                myvars](Syntax.Assign[myvars, myvars, myvars](xvar, theta), phi)) &&
                (ddl_FRadmit(phi) &&
                  (Syntax.fsafe[myvars, myvars,
                    myvars](Syntax.Box[myvars, myvars,
                    myvars](Syntax.Assign[myvars, myvars, myvars](xvar, theta),
                    phi)) &&
                    Set.equal_seta[Sum_Type.sum[myvars,
                      myvars]](Set.inf_set[Sum_Type.sum[myvars,
                      myvars]](Set.insert[Sum_Type.sum[myvars,
                      myvars]](Sum_Type.Inl[myvars, myvars](y),
                      Set.insert[Sum_Type.sum[myvars,
                        myvars]](Sum_Type.Inr[myvars, myvars](y),
                        Set.insert[Sum_Type.sum[myvars,
                          myvars]](Sum_Type.Inr[myvars, myvars](x),
                          Set.bot_set[Sum_Type.sum[myvars, myvars]]))),
                      Static_Semantics.FVF[myvars, myvars,
                        myvars](Syntax.Box[myvars, myvars,
                        myvars](Syntax.Assign[myvars, myvars,
                        myvars](xvar, theta),
                        phi))),
                      Set.bot_set[Sum_Type.sum[myvars, myvars]]))))))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
              myvars,
              myvars]](s, j,
              ddl_FBrename(x, y,
                Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
          else None)
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.And(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Exists(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Diamond(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.InContext(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.DiffAssign(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Test(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.EvolveODE(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Choice(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Sequence(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Loop(_), _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      /*case (Proof_Checker.HideR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.closeI[Syntax.formula[myvars, myvars,
            myvars]](s, j))))*/
      case (Proof_Checker.CutRight(v), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j, v)),
          (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j,
            Syntax.Implies[myvars, myvars,
              myvars](v, Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
      case (Proof_Checker.EquivifyR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars, myvars](p, q)))))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            None
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.CommuteEquivR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
              myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars,
                myvars](q, p)))))
          else None)
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            None
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })

  /*case (Proof_Checker.HideR(), j, (a, s)) =>
  Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars,
      myvars]])]](List((a,
    Proof_Checker.closeI[Syntax.formula[myvars, myvars,
      myvars]](s, j))))*/
/*  case (Proof_Checker.CutRight(v), j, (a, s)) =>
  Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars,
      myvars]])]](List((a,
    Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
      myvars]](s, j, v)),
    (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
      myvars]](s, j,
      Syntax.Implies[myvars, myvars,
        myvars](v, Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))*/
  /*case (Proof_Checker.EquivifyR(), j, (a, s)) =>
  (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
    case Syntax.Geq(_, _) => None
    case Syntax.Prop(_, _) => None
    case Syntax.Not(Syntax.Geq(_, _)) => None
    case Syntax.Not(Syntax.Prop(_, _)) => None
    case Syntax.Not(Syntax.Not(_)) => None
    case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
      Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
        List[Syntax.formula[myvars, myvars,
          myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
        myvars]](s, j,
        Syntax.Equiv[myvars, myvars, myvars](p, q)))))
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Not(Syntax.Exists(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Not(Syntax.Diamond(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Not(Syntax.InContext(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => None
    case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
      None
    case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
    case Syntax.Not(Syntax.Exists(_, _)) => None
    case Syntax.Not(Syntax.Diamond(_, _)) => None
    case Syntax.Not(Syntax.InContext(_, _)) => None
    case Syntax.And(_, _) => None
    case Syntax.Exists(_, _) => None
    case Syntax.Diamond(_, _) => None
    case Syntax.InContext(_, _) => None*/

  case (Proof_Checker.CommuteEquivR(), j, (a, s)) =>
  (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
    case Syntax.Geq(_, _) => None
    case Syntax.Prop(_, _) => None
    case Syntax.Not(Syntax.Geq(_, _)) => None
    case Syntax.Not(Syntax.Prop(_, _)) => None
    case Syntax.Not(Syntax.Not(_)) => None
    case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Geq(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Prop(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.Geq(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.Prop(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.Not(_))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Prop(_, _),
    _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Geq(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Prop(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
    Syntax.Not(Syntax.And(Syntax.Not(pa),
    Syntax.Not(qa)))))
    => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
      Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
      Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
        List[Syntax.formula[myvars, myvars,
          myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
        myvars,
        myvars]](s, j,
        Syntax.Equiv[myvars, myvars,
          myvars](q, p)))))
    else None)
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.And(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Exists(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.Diamond(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Not(_),
    Syntax.InContext(_, _)))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Exists(_, _),
    _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
    _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.And(Syntax.InContext(_, _),
    _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.Exists(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.Diamond(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Not(Syntax.InContext(_, _))))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.And(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Exists(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.Diamond(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
    Syntax.InContext(_, _)))
    => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
      None
    case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
    case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
    case Syntax.Not(Syntax.Exists(_, _)) => None
    case Syntax.Not(Syntax.Diamond(_, _)) => None
    case Syntax.Not(Syntax.InContext(_, _)) => None
    case Syntax.And(_, _) => None
    case Syntax.Exists(_, _) => None
    case Syntax.Diamond(_, _) => None
    case Syntax.InContext(_, _) => None
  })}


  val PRINT_ALL_RESULTS = true


  def ddl_FBrename(x: myvars, y: myvars,
                   xa2: Syntax.formula[myvars, myvars, myvars]):
  Syntax.formula[myvars, myvars, myvars]
  =
    (x, y, xa2) match {
      case (x, y,
      Syntax.Not(Syntax.Diamond(Syntax.Assign(z, theta), Syntax.Not(phi))))
      => (if (equal_myvarsa(x, z))
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Assign[myvars, myvars, myvars](y, theta),
          ddl_FUrename(x, y, phi))
      else (if (equal_myvarsa(y, z))
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Assign[myvars, myvars,
          myvars](x, theta),
          ddl_FUrename(x, y, phi))
      else Syntax.Box[myvars, myvars,
        myvars](Syntax.Assign[myvars, myvars,
        myvars](z, theta),
        phi)))
      case (x, y, Syntax.Not(Syntax.Exists(z, Syntax.Not(phi)))) =>
        (if (equal_myvarsa(x, z))
          Syntax.Forall[myvars, myvars, myvars](y, ddl_FUrename(x, y, phi))
        else (if (equal_myvarsa(y, z))
          Syntax.Forall[myvars, myvars, myvars](x, ddl_FUrename(x, y, phi))
        else Syntax.Forall[myvars, myvars, myvars](z, phi)))
      case (x, y, Syntax.Geq(v, va)) => Syntax.Geq[myvars, myvars, myvars](v, va)
      case (x, y, Syntax.Prop(v, va)) => Syntax.Prop[myvars, myvars, myvars](v, va)
      case (x, y, Syntax.Not(Syntax.Geq(va, vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Geq[myvars, myvars, myvars](va, vb))
      case (x, y, Syntax.Not(Syntax.Prop(va, vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Prop[myvars, myvars, myvars](va, vb))
      case (x, y, Syntax.Not(Syntax.Not(va))) =>
        Syntax.Not[myvars, myvars, myvars](Syntax.Not[myvars, myvars, myvars](va))
      case (x, y, Syntax.Not(Syntax.And(va, vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.And[myvars, myvars, myvars](va, vb))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.Geq(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.Geq[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.Prop(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.Prop[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.And(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.And[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.Exists(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.Exists[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.Diamond(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.Diamond[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Exists(va, Syntax.InContext(v, vc)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Exists[myvars, myvars,
          myvars](va,
          Syntax.InContext[myvars, myvars, myvars](v, vc)))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.Pvar(vc), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](vc), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.DiffAssign(vc, vd), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.DiffAssign[myvars, myvars, myvars](vc, vd), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.Test(vc), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.Test[myvars, myvars, myvars](vc), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.EvolveODE(vc, vd), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.EvolveODE[myvars, myvars, myvars](vc, vd), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.Choice(vc, vd), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.Choice[myvars, myvars, myvars](vc, vd), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.Sequence(vc, vd), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.Sequence[myvars, myvars, myvars](vc, vd), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(Syntax.Loop(vc), vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](Syntax.Loop[myvars, myvars, myvars](vc), vb))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.Geq(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.Geq[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.Prop(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.Prop[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.And(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.And[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.Exists(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.Exists[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.Diamond(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.Diamond[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.Diamond(va, Syntax.InContext(vc, vd)))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Diamond[myvars, myvars,
          myvars](va, Syntax.InContext[myvars, myvars, myvars](vc, vd)))
      case (x, y, Syntax.Not(Syntax.InContext(va, vb))) =>
        Syntax.Not[myvars, myvars,
          myvars](Syntax.InContext[myvars, myvars, myvars](va, vb))
      case (x, y, Syntax.And(v, va)) => Syntax.And[myvars, myvars, myvars](v, va)
      case (x, y, Syntax.Exists(v, va)) =>
        Syntax.Exists[myvars, myvars, myvars](v, va)
      case (x, y, Syntax.Diamond(v, va)) =>
        Syntax.Diamond[myvars, myvars, myvars](v, va)
      case (x, y, Syntax.InContext(v, va)) =>
        Syntax.InContext[myvars, myvars, myvars](v, va)
    }
    def ddl_SBrename(x: myvars, y: myvars,
                     xa2: (List[Syntax.formula[myvars, myvars, myvars]],
                       List[Syntax.formula[myvars, myvars, myvars]])):
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])
    =
      (x, y, xa2) match {
        case (x, y, (a, s)) =>
          (Lista.map[Syntax.formula[myvars, myvars, myvars],
            Syntax.formula[myvars, myvars,
              myvars]](((aa:
                         Syntax.formula[myvars, myvars, myvars])
          =>
            ddl_FBrename(x, y, aa)),
            a),
            Lista.map[Syntax.formula[myvars, myvars, myvars],
              Syntax.formula[myvars, myvars,
                myvars]](((aa:
                           Syntax.formula[myvars, myvars, myvars])
            =>
              ddl_FBrename(x, y, aa)),
              s))
      }

/*    def ddl_Rrule_result(x0: Proof_Checker.rrule[myvars, myvars, myvars],
                       j: Nat.nat,
                       x2: (List[Syntax.formula[myvars, myvars, myvars]],
                         List[Syntax.formula[myvars, myvars, myvars]])):
  Option[List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])]]
  =
    (x0, j, x2) match {
      case (Proof_Checker.AndR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(_) => None
          case Syntax.And(p, q) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j, p)),
              (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](s, j, q))))
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.ImplyR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a ++ List(p),
              Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](s, j) ++
                List(q))))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            None
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.EquivR(), j, (a, s)) =>
      {
        val (Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
        Syntax.Not(Syntax.And(Syntax.Not(pa),
        Syntax.Not(qa)))))):
          Syntax.formula[myvars, myvars, myvars]
        = Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j);
        (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
          Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
          Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])]](List((a ++ List(p),
            Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](s, j) ++
              List(q)),
            (a ++ List(q),
              Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](s, j) ++
                List(p))))
        else None)
      }
      case (Proof_Checker.CohideR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          List(Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j)))))
      case (Proof_Checker.CohideRR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((Nil,
          List(Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j)))))
      case (Proof_Checker.TrueR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(x, y) =>
            (if (Syntax.equal_trma[myvars, myvars](x, y) &&
              Syntax.equal_trma[myvars,
                myvars](x,
                Syntax.Const[myvars, myvars](Real.zero_real)))
              Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])]](Nil)
            else None)
          case Syntax.Prop(_, _) => None
          case Syntax.Not(_) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.Skolem(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(_, _)) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Geq(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Prop(_, _))) => None
          case Syntax.Not(Syntax.Exists(x, Syntax.Not(p))) =>
            (if (! (Set.member[Sum_Type.sum[myvars,
              myvars]](Sum_Type.Inl[myvars, myvars](x),
              Static_Semantics.FVSeq[myvars, myvars, myvars]((a, s)))))
              Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](s, j, p))))
            else None)
          case Syntax.Not(Syntax.Exists(_, Syntax.And(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Exists(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.Diamond(_, _))) => None
          case Syntax.Not(Syntax.Exists(_, Syntax.InContext(_, _))) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.BRenameR(x, y), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(_, _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Pvar(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Geq(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Prop(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(xa, theta),
          Syntax.Not(phi)))
          => (if (ddl_TRadmit(theta) &&
            (ddl_FRadmit(Syntax.Box[myvars, myvars,
              myvars](Syntax.Assign[myvars, myvars, myvars](xa, theta), phi)) &&
              (ddl_FRadmit(phi) &&
                (Syntax.fsafe[myvars, myvars,
                  myvars](Syntax.Box[myvars, myvars,
                  myvars](Syntax.Assign[myvars, myvars, myvars](xa, theta),
                  phi)) &&
                  Set.equal_seta[Sum_Type.sum[myvars,
                    myvars]](Set.inf_set[Sum_Type.sum[myvars,
                    myvars]](Set.insert[Sum_Type.sum[myvars,
                    myvars]](Sum_Type.Inl[myvars, myvars](y),
                    Set.insert[Sum_Type.sum[myvars,
                      myvars]](Sum_Type.Inr[myvars, myvars](y),
                      Set.insert[Sum_Type.sum[myvars,
                        myvars]](Sum_Type.Inr[myvars, myvars](xa),
                        Set.bot_set[Sum_Type.sum[myvars, myvars]]))),
                    Static_Semantics.FVF[myvars, myvars, myvars](phi)),
                    Set.bot_set[Sum_Type.sum[myvars, myvars]])))))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
              myvars,
              myvars]](s, j,
              ddl_FBrename(xa, y,
                Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
          else None)
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.And(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Exists(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Diamond(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.InContext(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.DiffAssign(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Test(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.EvolveODE(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Choice(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Sequence(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Loop(_), _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => Nonedef ddl_Rrule_result(
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.HideR(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.closeI[Syntax.formula[myvars, myvars,
            myvars]](s, j))))
      case (Proof_Checker.CutRight(v), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((a,
          Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j, v)),
          (a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
            myvars]](s, j,
            Syntax.Implies[myvars, myvars,
              myvars](v, Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j))))))
      case (Proof_Checker.EquivifyR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars, myvars](p, q)))))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => None
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            None
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
      case (Proof_Checker.CommuteEquivR(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](s, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((a, Proof_Checker.replaceI[Syntax.formula[myvars,
              myvars,
              myvars]](s, j,
              Syntax.Equiv[myvars, myvars,
                myvars](q, p)))))
          else None)
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            None
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => None
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(_, _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
    }
*/
  def ddl_Lrule_result(x0: Proof_Checker.lrule[myvars, myvars, myvars],
                       j: Nat.nat,
                       x2: (List[Syntax.formula[myvars, myvars, myvars]],
                         List[Syntax.formula[myvars, myvars, myvars]])):
  Option[List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])]]
  =
    (x0, j, x2) match {
      case (Proof_Checker.NotL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(p) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](a, j),
              s ++ List(p))))
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })

      case (Proof_Checker.AndL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(_) => fail()
          case Syntax.And(p, q) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](a, j) ++
              List(p, q),
              s)))
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.ImplyL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Geq(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Prop(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(q), Syntax.Not(Syntax.Not(p)))) =>
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](a, j),
              s ++ List(p)),
              (Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](a, j, q),
                s)))
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Not(Syntax.And(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.And(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Exists(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.Diamond(_, _))) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(_), Syntax.InContext(_, _))) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.EquivForwardL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](a, j) ++
              List(q),
              s),
              (Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](a, j),
                s ++ List(p))))
          else fail())
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.EquivBackwardL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars, myvars,
              myvars]](a, j) ++
              List(p),
              s),
              (Proof_Checker.closeI[Syntax.formula[myvars, myvars,
                myvars]](a, j),
                s ++ List(q))))
          else fail())
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.HideL(), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((Proof_Checker.closeI[Syntax.formula[myvars,
          myvars, myvars]](a, j),
          s)))
      case (Proof_Checker.CutLeft(f), j, (a, s)) =>
        Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])]](List((Proof_Checker.replaceI[Syntax.formula[myvars,
          myvars, myvars]](a, j, f),
          s),
          (Proof_Checker.closeI[Syntax.formula[myvars, myvars,
            myvars]](a, j),
            s ++ List(Syntax.Implies[myvars, myvars,
              myvars](Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j), f)))))
      case (Proof_Checker.EquivL(), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => fail()
          case Syntax.Prop(_, _) => fail()
          case Syntax.Not(Syntax.Geq(_, _)) => fail()
          case Syntax.Not(Syntax.Prop(_, _)) => fail()
          case Syntax.Not(Syntax.Not(_)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Geq(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Prop(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Geq(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Prop(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Not(_)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Geq(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Prop(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Geq(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Prop(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Not(_))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Geq(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Prop(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Geq(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Prop(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(p, q)),
          Syntax.Not(Syntax.And(Syntax.Not(pa),
          Syntax.Not(qa)))))
          => (if (Syntax.equal_formulaa[myvars, myvars, myvars](p, pa) &&
            Syntax.equal_formulaa[myvars, myvars, myvars](q, qa))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](a, j,
              Syntax.And[myvars, myvars, myvars](p, q)),
              s),
              (Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
                myvars]](a, j,
                Syntax.And[myvars, myvars,
                  myvars](Syntax.Not[myvars, myvars, myvars](p),
                  Syntax.Not[myvars, myvars, myvars](q))),
                s)))
          else fail())
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.And(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Exists(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.Diamond(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Not(_),
          Syntax.InContext(_, _)))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.And(_, _), _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Exists(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.Diamond(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.And(Syntax.InContext(_, _),
          _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Exists(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.Diamond(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Not(Syntax.InContext(_, _))))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.And(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Exists(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.Diamond(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.And(_, _)),
          Syntax.InContext(_, _)))
          => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Exists(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.Diamond(_, _)), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Not(Syntax.InContext(_, _)), _)) =>
            fail()
          case Syntax.Not(Syntax.And(Syntax.And(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Exists(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.Diamond(_, _), _)) => fail()
          case Syntax.Not(Syntax.And(Syntax.InContext(_, _), _)) => fail()
          case Syntax.Not(Syntax.Exists(_, _)) => fail()
          case Syntax.Not(Syntax.Diamond(_, _)) => fail()
          case Syntax.Not(Syntax.InContext(_, _)) => fail()
          case Syntax.And(_, _) => fail()
          case Syntax.Exists(_, _) => fail()
          case Syntax.Diamond(_, _) => fail()
          case Syntax.InContext(_, _) => fail()
        })
      case (Proof_Checker.BRenameL(x, y), j, (a, s)) =>
        (Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j) match {
          case Syntax.Geq(_, _) => None
          case Syntax.Prop(_, _) => None
          case Syntax.Not(Syntax.Geq(_, _)) => None
          case Syntax.Not(Syntax.Prop(_, _)) => None
          case Syntax.Not(Syntax.Not(_)) => None
          case Syntax.Not(Syntax.And(_, _)) => None
          case Syntax.Not(Syntax.Exists(_, _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Pvar(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Geq(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Prop(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(xa, theta),
          Syntax.Not(phi)))
          => (if (ddl_TRadmit(theta) &&
            (ddl_FRadmit(Syntax.Box[myvars, myvars,
              myvars](Syntax.Assign[myvars, myvars, myvars](xa, theta), phi)) &&
              (ddl_FRadmit(phi) &&
                (Syntax.fsafe[myvars, myvars,
                  myvars](Syntax.Box[myvars, myvars,
                  myvars](Syntax.Assign[myvars, myvars, myvars](xa, theta),
                  phi)) &&
                  Set.equal_seta[Sum_Type.sum[myvars,
                    myvars]](Set.inf_set[Sum_Type.sum[myvars,
                    myvars]](Set.insert[Sum_Type.sum[myvars,
                    myvars]](Sum_Type.Inl[myvars, myvars](y),
                    Set.insert[Sum_Type.sum[myvars,
                      myvars]](Sum_Type.Inr[myvars, myvars](y),
                      Set.insert[Sum_Type.sum[myvars,
                        myvars]](Sum_Type.Inr[myvars, myvars](xa),
                        Set.bot_set[Sum_Type.sum[myvars, myvars]]))),
                    Static_Semantics.FVF[myvars, myvars, myvars](phi)),
                    Set.bot_set[Sum_Type.sum[myvars, myvars]])))))
            Some[List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])]](List((Proof_Checker.replaceI[Syntax.formula[myvars, myvars,
              myvars]](a, j,
              ddl_FBrename(xa, y,
                Lista.nth[Syntax.formula[myvars, myvars, myvars]](a, j))),
              s)))
          else None)
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.And(_, _))) =>
            None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _), Syntax.Exists(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Diamond(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.InContext(_, _)))
          => None
          case Syntax.Not(Syntax.Diamond(Syntax.DiffAssign(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Test(_), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.EvolveODE(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Choice(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Sequence(_, _), _)) => None
          case Syntax.Not(Syntax.Diamond(Syntax.Loop(_), _)) => None
          case Syntax.Not(Syntax.InContext(_, _)) => None
          case Syntax.And(_, _) => None
          case Syntax.Exists(_, _) => None
          case Syntax.Diamond(_, _) => None
          case Syntax.InContext(_, _) => None
        })
    }
  def ddl_merge_seqs(ss: List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
                     x1: List[(List[Syntax.formula[myvars, myvars, myvars]],
                       List[Syntax.formula[myvars, myvars, myvars]])],
                     i: Nat.nat):
  List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])]
  =
    (ss, x1, i) match {
      case (ss, Nil, i) =>
        Proof_Checker.closeI[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](ss, i)
      case (ss, s :: sss, i) =>
        Proof_Checker.replaceI[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])](ss, i, s) ++
          sss
    }

  def ddl_swap(x: myvars, y: myvars, z: myvars): myvars =
    (if (equal_myvarsa(z, x)) y else (if (equal_myvarsa(z, y)) x else z))

  def ddl_TUrename(x: myvars, y: myvars, xa2: Syntax.trm[myvars, myvars]):
  Syntax.trm[myvars, myvars]
  =
    (x, y, xa2) match {
      case (x, y, Syntax.Var(z)) => Syntax.Var[myvars, myvars](ddl_swap(x, y, z))
      case (x, y, Syntax.DiffVar(z)) =>
        Syntax.DiffVar[myvars, myvars](ddl_swap(x, y, z))
      case (x, y, Syntax.Const(r)) => Syntax.Const[myvars, myvars](r)
      case (x, y, Syntax.Function(f, args)) =>
        Syntax.Function[myvars,
          myvars](f, ((i: myvars) => ddl_TUrename(x, y, args(i))))
      case (x, y, Syntax.Functional(f)) => sys.error("undefined")
      case (x, y, Syntax.Plus(theta_1, theta_2)) =>
        Syntax.Plus[myvars,
          myvars](ddl_TUrename(x, y, theta_1),
          ddl_TUrename(x, y, theta_2))
      case (x, y, Syntax.Times(theta_1, theta_2)) =>
        Syntax.Times[myvars,
          myvars](ddl_TUrename(x, y, theta_1),
          ddl_TUrename(x, y, theta_2))
      case (x, y, Syntax.Differential(theta)) =>
        Syntax.Differential[myvars, myvars](ddl_TUrename(x, y, theta))
    }

  def ddl_OUrename(x: myvars, y: myvars, xa2: Syntax.ODE[myvars, myvars]):
  Syntax.ODE[myvars, myvars]
  =
    (x, y, xa2) match {
      case (x, y, Syntax.OVar(c)) => sys.error("undefined")
      case (x, y, Syntax.OSing(z, theta)) =>
        Syntax.OSing[myvars, myvars](ddl_swap(x, y, z), ddl_TUrename(x, y, theta))
      case (x, y, Syntax.OProd(oDE1, oDE2)) =>
        Syntax.oprod[myvars,
          myvars](ddl_OUrename(x, y, oDE1), ddl_OUrename(x, y, oDE2))
    }

  def ddl_PUrename(x: myvars, y: myvars, xa2: Syntax.hp[myvars, myvars, myvars]):
  Syntax.hp[myvars, myvars, myvars]
  =
    (x, y, xa2) match {
      case (x, y, Syntax.Pvar(a)) => sys.error("undefined")
      case (x, y, Syntax.Assign(z, theta)) =>
        Syntax.Assign[myvars, myvars,
          myvars](ddl_swap(x, y, z), ddl_TUrename(x, y, theta))
      case (x, y, Syntax.DiffAssign(z, theta)) =>
        Syntax.DiffAssign[myvars, myvars,
          myvars](ddl_swap(x, y, z), ddl_TUrename(x, y, theta))
      case (x, y, Syntax.Test(phi)) =>
        Syntax.Test[myvars, myvars, myvars](ddl_FUrename(x, y, phi))
      case (x, y, Syntax.EvolveODE(ode, phi)) =>
        Syntax.EvolveODE[myvars, myvars,
          myvars](ddl_OUrename(x, y, ode), ddl_FUrename(x, y, phi))
      case (x, y, Syntax.Choice(a, b)) =>
        Syntax.Choice[myvars, myvars,
          myvars](ddl_PUrename(x, y, a), ddl_PUrename(x, y, b))
      case (x, y, Syntax.Sequence(a, b)) =>
        Syntax.Sequence[myvars, myvars,
          myvars](ddl_PUrename(x, y, a), ddl_PUrename(x, y, b))
      case (x, y, Syntax.Loop(a)) =>
        Syntax.Loop[myvars, myvars, myvars](ddl_PUrename(x, y, a))
    }

  def ddl_FUrename(x: myvars, y: myvars,
                   xa2: Syntax.formula[myvars, myvars, myvars]):
  Syntax.formula[myvars, myvars, myvars]
  =
    (x, y, xa2) match {
      case (x, y, Syntax.Geq(theta_1, theta_2)) =>
        Syntax.Geq[myvars, myvars,
          myvars](ddl_TUrename(x, y, theta_1),
          ddl_TUrename(x, y, theta_2))
      case (x, y, Syntax.Prop(p, args)) =>
        Syntax.Prop[myvars, myvars,
          myvars](p, ((i: myvars) => ddl_TUrename(x, y, args(i))))
      case (x, y, Syntax.Not(phi)) =>
        Syntax.Not[myvars, myvars, myvars](ddl_FUrename(x, y, phi))
      case (x, y, Syntax.And(phi, psi)) =>
        Syntax.And[myvars, myvars,
          myvars](ddl_FUrename(x, y, phi), ddl_FUrename(x, y, psi))
      case (x, y, Syntax.Exists(z, phi)) =>
        Syntax.Exists[myvars, myvars,
          myvars](ddl_swap(x, y, z), ddl_FUrename(x, y, phi))
      case (x, y, Syntax.Diamond(alpha, phi)) =>
        Syntax.Diamond[myvars, myvars,
          myvars](ddl_PUrename(x, y, alpha), ddl_FUrename(x, y, phi))
      case (x, y, Syntax.InContext(c, phi)) => sys.error("undefined")
    }

  def ddl_SUrename(x: myvars, y: myvars,
                   xa2: (List[Syntax.formula[myvars, myvars, myvars]],
                     List[Syntax.formula[myvars, myvars, myvars]])):
  (List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])
  =
    (x, y, xa2) match {
      case (x, y, (a, s)) =>
        (Lista.map[Syntax.formula[myvars, myvars, myvars],
          Syntax.formula[myvars, myvars,
            myvars]](((aa:
                       Syntax.formula[myvars, myvars, myvars])
        =>
          ddl_FUrename(x, y, aa)),
          a),
          Lista.map[Syntax.formula[myvars, myvars, myvars],
            Syntax.formula[myvars, myvars,
              myvars]](((aa:
                         Syntax.formula[myvars, myvars, myvars])
          =>
            ddl_FUrename(x, y, aa)),
            s))
    }


  def ddl_rule_result(x0: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])),
                      x1: (Nat.nat,
                        Proof_Checker.ruleApp[myvars, myvars, myvars])):
  Option[(List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))]
  =
    (x0, x1) match {
      case ((sg, c), (i, Proof_Checker.Lrule(l, j))) =>
        (if (Nat.less_eq_nat(Lista.size_list[Syntax.formula[myvars, myvars,
          myvars]].apply(Product_Type.fst[List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]]](Lista.nth[(List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
          j))
          fail()
        else (ddl_Lrule_result(l, j,
          Lista.nth[(List[Syntax.formula[myvars, myvars,
            myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i))
        match {
          case None =>
            fail()
          case Some(a) =>
            Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])],
              (List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]]))]((ddl_merge_seqs(sg, a, i), c))
        }))
      case ((sg, c), (i, Proof_Checker.Rrule(r, j))) =>
        (if (Nat.less_eq_nat(Lista.size_list[Syntax.formula[myvars, myvars,
          myvars]].apply(Product_Type.snd[List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]]](Lista.nth[(List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
          j))
          fail()
        else (ddl_Rrule_result(r, j,
          Lista.nth[(List[Syntax.formula[myvars, myvars,
            myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i))
        match {
          case None => fail()
          case Some(a) =>
            Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])],
              (List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]]))]((ddl_merge_seqs(sg, a, i), c))
        }))
      case ((sg, c), (i, Proof_Checker.Cut(phi))) =>
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]))]({
          val a: (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])
          = Lista.nth[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i)
          val (aa, s):
            (List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])
          = a;
          (ddl_merge_seqs(sg, List((aa ++ List(phi), s), (aa, s ++ List(phi))), i), c)
        })
      case ((sg, c), (i, Proof_Checker.CloseId(j, k))) =>
        (if (Nat.less_nat(j, Lista.size_list[Syntax.formula[myvars, myvars,
          myvars]].apply(Product_Type.fst[List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]]](Lista.nth[(List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i)))) &&
          (Nat.less_nat(k, Lista.size_list[Syntax.formula[myvars, myvars,
            myvars]].apply(Product_Type.snd[List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]](Lista.nth[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i)))) &&
            Syntax.equal_formulaa[myvars, myvars,
              myvars](Lista.nth[Syntax.formula[myvars,
              myvars,
              myvars]](Product_Type.fst[List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]]](Lista.nth[(List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])](sg, i)),
              j),
              Lista.nth[Syntax.formula[myvars, myvars,
                myvars]](Product_Type.snd[List[Syntax.formula[myvars,
                myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]]](Lista.nth[(List[Syntax.formula[myvars,
                myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])](sg, i)),
                k))))
          Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])],
            (List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]]))]((Proof_Checker.closeI[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](sg, i),
            c))
        else fail())
      case ((sg, c), (i, Proof_Checker.URename(x, y))) =>
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]))]((ddl_merge_seqs(sg,
          List(ddl_SUrename(x, y,
            Lista.nth[(List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
          i),
          c))
/*      case ((sg, c), (i, Proof_Checker.BRename(x, y))) =>
        (if ((Lista.nth[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i)
        match {
          case (Nil, Nil) => false
          case (Nil, Syntax.Geq(_, _) :: _) => false
          case (Nil, Syntax.Prop(_, _) :: _) => false
          case (Nil, Syntax.Not(Syntax.Geq(_, _)) :: _) => false
          case (Nil, Syntax.Not(Syntax.Prop(_, _)) :: _) => false
          case (Nil, Syntax.Not(Syntax.Not(_)) :: _) => false
          case (Nil, Syntax.Not(Syntax.And(_, _)) :: _) => false
          case (Nil, Syntax.Not(Syntax.Exists(_, _)) :: _) => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Pvar(_), _)) :: _) =>
            false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Geq(_, _))) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Prop(_, _))) ::
            _)
          => false
          case (Nil, List(Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Not(_)))))
          => true
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Not(_))) ::
            _ :: _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.And(_, _))) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Exists(_, _))) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.Diamond(_, _))) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Assign(_, _),
          Syntax.InContext(_, _))) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.DiffAssign(_, _), _)) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Test(_), _)) :: _) =>
            false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.EvolveODE(_, _), _)) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Choice(_, _), _)) :: _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Sequence(_, _), _)) ::
            _)
          => false
          case (Nil, Syntax.Not(Syntax.Diamond(Syntax.Loop(_), _)) :: _) =>
            false
          case (Nil, Syntax.Not(Syntax.InContext(_, _)) :: _) => false
          case (Nil, Syntax.And(_, _) :: _) => false
          case (Nil, Syntax.Exists(_, _) :: _) => false
          case (Nil, Syntax.Diamond(_, _) :: _) => false
          case (Nil, Syntax.InContext(_, _) :: _) => false
          case (_ :: _, _) => false
        }))
          Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])],
            (List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]]))]((ddl_merge_seqs(sg,
            List(ddl_SBrename(x, y,
              Lista.nth[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
            i),
            c))
        else {
          println("Bound rename not applicable at:" + ddl_seq_to_string(Lista.nth(sg, i)).mkString)
          fail()})*/
      case ((sg, c), (i, Proof_Checker.Cohide2(j, k))) =>
        (if (Nat.less_eq_nat(Lista.size_list[Syntax.formula[myvars, myvars,
          myvars]].apply(Product_Type.fst[List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]]](Lista.nth[(List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
          j) ||
          Nat.less_eq_nat(Lista.size_list[Syntax.formula[myvars, myvars,
            myvars]].apply(Product_Type.snd[List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]](Lista.nth[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i))),
            k))
          fail()
        else Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]))]((ddl_merge_seqs(sg, List((List(Lista.nth[Syntax.formula[myvars,
          myvars,
          myvars]](Product_Type.fst[List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]]](Lista.nth[(List[Syntax.formula[myvars,
          myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])](sg, i)),
          j)),
          List(Lista.nth[Syntax.formula[myvars, myvars,
            myvars]](Product_Type.snd[List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]](Lista.nth[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])](sg, i)),
            k)))),
          i),
          c)))
    }

  def ddl_merge_rules(x0: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])),
                      x1: (List[(List[Syntax.formula[myvars, myvars, myvars]],
                        List[Syntax.formula[myvars, myvars, myvars]])],
                        (List[Syntax.formula[myvars, myvars, myvars]],
                          List[Syntax.formula[myvars, myvars, myvars]])),
                      i: Nat.nat):
  Option[(List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))]
  =
    (x0, x1, i) match {
      case ((p1, c1), (Nil, c2), i) =>
        (if (Nat.less_nat(i, Lista.size_list[(List[Syntax.formula[myvars, myvars,
          myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])].apply(p1)) &&
          Product_Type.equal_prod[List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]](Lista.nth[(List[Syntax.formula[myvars, myvars,
            myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](p1, i),
            c2))
          Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])],
            (List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]]))]((Proof_Checker.closeI[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](p1, i),
            c1))
        else{
          println("Merge failure, first provable: " + ddl_rule_to_string((p1,c1)).mkString + "\nsecond provable:" + ddl_rule_to_string((Nil,c2)).mkString)
            fail()}
          )
      case ((p1, c1), (s :: ss, c2), i) =>
        (if (Nat.less_nat(i, Lista.size_list[(List[Syntax.formula[myvars, myvars,
          myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])].apply(p1)) &&
          Product_Type.equal_prod[List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]](Lista.nth[(List[Syntax.formula[myvars, myvars,
            myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](p1, i),
            c2))
          Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]])],
            (List[Syntax.formula[myvars, myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]]))]((Proof_Checker.replaceI[(List[Syntax.formula[myvars,
            myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](p1, i, s) ++
            ss,
            c1))
        else {
          println("Merge failure, first provable: " + ddl_rule_to_string((p1,c1)).mkString + "\nsecond provable:" + ddl_rule_to_string((s::ss,c2)).mkString)
          fail()
        })
    }

  def ddl_fnc(r: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])),
              seq: (List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]]),
              ra: Proof_Checker.ruleApp[myvars, myvars, myvars]):
  Option[(List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))]
  =
    (ddl_rule_result(ddl_start_proof(seq), (Nat.zero_nat, ra)) match {
      case None => fail()
      case Some(rule) => ddl_merge_rules(rule, r, Nat.zero_nat)
    })

  def ddl_pro(r1: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])),
              r2: (List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])],
                (List[Syntax.formula[myvars, myvars, myvars]],
                  List[Syntax.formula[myvars, myvars, myvars]]))):
  Option[(List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))]
  =
    ddl_merge_rules(r2, r1, Nat.zero_nat)

  def dfree_i[A, B : Enum.enum](x: Syntax.trm[A, B]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
      Unit](Predicate.single[Syntax.trm[A, B]](x),
      ((a: Syntax.trm[A, B]) =>
        (a match {
          case Syntax.Var(_) => Predicate.single[Unit](())
          case Syntax.Const(_) => Predicate.bot_pred[Unit]
          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
        B],
        Unit](Predicate.single[Syntax.trm[A, B]](x),
        ((a: Syntax.trm[A, B]) =>
          (a match {
            case Syntax.Var(_) => Predicate.bot_pred[Unit]
            case Syntax.Const(_) => Predicate.single[Unit](())
            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
          Unit](Predicate.single[Syntax.trm[A, B]](x),
          ((a: Syntax.trm[A, B]) =>
            (a match {
              case Syntax.Var(_) => Predicate.bot_pred[Unit]
              case Syntax.Const(_) => Predicate.bot_pred[Unit]
              case Syntax.Function(_, args) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[B](((i: B) =>
                  Syntax.dfree[A, B](args(i))))),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    Predicate.single[Unit](())
                  }))
              case Syntax.Functional(_) => Predicate.bot_pred[Unit]
              case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
              case Syntax.Differential(_) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
            Unit](Predicate.single[Syntax.trm[A, B]](x),
            ((a: Syntax.trm[A, B]) =>
              (a match {
                case Syntax.Var(_) => Predicate.bot_pred[Unit]
                case Syntax.Const(_) => Predicate.bot_pred[Unit]
                case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                case Syntax.Plus(theta_1, theta_2) =>
                  Predicate.bind[Unit,
                    Unit](dfree_i[A, B](theta_1),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](dfree_i[A, B](theta_2),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                case Syntax.Differential(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
              B],
              Unit](Predicate.single[Syntax.trm[A, B]](x),
              ((a: Syntax.trm[A, B]) =>
                (a match {
                  case Syntax.Var(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Const(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Function(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Functional(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Plus(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Times(theta_1, theta_2) =>
                    Predicate.bind[Unit,
                      Unit](dfree_i[A, B](theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](dfree_i[A, B](theta_2), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.DiffVar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Differential(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                Unit](Predicate.single[Syntax.trm[A, B]](x),
                ((a: Syntax.trm[A, B]) =>
                  (a match {
                    case Syntax.Var(_) => Predicate.bot_pred[Unit]
                    case Syntax.Const(_) => Predicate.bot_pred[Unit]
                    case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Functional(_) => Predicate.single[Unit](())
                    case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                  B],
                  Unit](Predicate.single[Syntax.trm[A,
                  B]](x),
                  ((a: Syntax.trm[A, B]) =>
                    (a match {
                      case Syntax.Var(_) => Predicate.single[Unit](())
                      case Syntax.Const(_) => Predicate.bot_pred[Unit]
                      case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                      case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                    B],
                    Unit](Predicate.single[Syntax.trm[A, B]](x),
                    ((a: Syntax.trm[A, B]) =>
                      (a match {
                        case Syntax.Var(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Const(_) =>
                          Predicate.single[Unit](())
                        case Syntax.Function(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Functional(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Plus(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Times(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.DiffVar(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Differential(_) =>
                          Predicate.bot_pred[Unit]
                      }))),
                    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                      Unit](Predicate.single[Syntax.trm[A, B]](x),
                      ((a: Syntax.trm[A, B]) =>
                        (a match {
                          case Syntax.Var(_) => Predicate.bot_pred[Unit]
                          case Syntax.Const(_) => Predicate.bot_pred[Unit]
                          case Syntax.Function(_, args) =>
                            Predicate.bind[Unit,
                              Unit](Predicate.if_pred(HOL.All[B](((i: B) => Syntax.dfree[A, B](args(i))))),
                              ((aa: Unit) => {
                                val (): Unit = aa;
                                Predicate.single[Unit](())
                              }))
                          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                        }))),
                      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                        B],
                        Unit](Predicate.single[Syntax.trm[A,
                        B]](x),
                        ((a: Syntax.trm[A, B]) =>
                          (a match {
                            case Syntax.Var(_) => Predicate.bot_pred[Unit]
                            case Syntax.Const(_) => Predicate.bot_pred[Unit]
                            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                            case Syntax.Plus(theta_1, theta_2) =>
                              Predicate.bind[Unit,
                                Unit](dfree_i[A, B](theta_1),
                                ((aa: Unit) =>
                                {
                                  val (): Unit = aa;
                                  Predicate.bind[Unit,
                                    Unit](dfree_i[A, B](theta_2),
                                    ((ab: Unit) => {
                                      val (): Unit = ab;
                                      Predicate.single[Unit](())
                                    }))
                                }))
                            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                          }))),
                        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                          Unit](Predicate.single[Syntax.trm[A, B]](x),
                          ((a: Syntax.trm[A, B]) =>
                            (a match {
                              case Syntax.Var(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Const(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Function(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Functional(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Plus(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Times(theta_1, theta_2) =>
                                Predicate.bind[Unit,
                                  Unit](dfree_i[A, B](theta_1),
                                  ((aa: Unit) =>
                                  {
                                    val (): Unit = aa;
                                    Predicate.bind[Unit,
                                      Unit](dfree_i[A, B](theta_2), ((ab: Unit) => {
                                      val (): Unit = ab;
                                      Predicate.single[Unit](())
                                    }))
                                  }))
                              case Syntax.DiffVar(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Differential(_) =>
                                Predicate.bot_pred[Unit]
                            }))),
                          Predicate.bind[Syntax.trm[A, B],
                            Unit](Predicate.single[Syntax.trm[A, B]](x),
                            ((a: Syntax.trm[A, B]) =>
                              (a match {
                                case Syntax.Var(_) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.Const(_) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.Function(_, _) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.Functional(_) =>
                                  Predicate.single[Unit](())
                                case Syntax.Plus(_, _) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.Times(_, _) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.DiffVar(_) =>
                                  Predicate.bot_pred[Unit]
                                case Syntax.Differential(_) =>
                                  Predicate.bot_pred[Unit]
                              }))))))))))))))
/*
  def dfree_i[A, B : Enum.enum](x: Syntax.trm[A, B]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
      Unit](Predicate.single[Syntax.trm[A, B]](x),
      ((a: Syntax.trm[A, B]) =>
        (a match {
          case Syntax.Var(_) => Predicate.single[Unit](())
          case Syntax.Const(_) => Predicate.bot_pred[Unit]
          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
        B],
        Unit](Predicate.single[Syntax.trm[A, B]](x),
        ((a: Syntax.trm[A, B]) =>
          (a match {
            case Syntax.Var(_) => Predicate.bot_pred[Unit]
            case Syntax.Const(_) => Predicate.single[Unit](())
            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
          Unit](Predicate.single[Syntax.trm[A, B]](x),
          ((a: Syntax.trm[A, B]) =>
            (a match {
              case Syntax.Var(_) => Predicate.bot_pred[Unit]
              case Syntax.Const(_) => Predicate.bot_pred[Unit]
              case Syntax.Function(_, args) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[B](((i: B) =>
                  Syntax.dfree[A, B](args(i))))),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    Predicate.single[Unit](())
                  }))
              case Syntax.Functional(_) => Predicate.bot_pred[Unit]
              case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
              case Syntax.Differential(_) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
            Unit](Predicate.single[Syntax.trm[A, B]](x),
            ((a: Syntax.trm[A, B]) =>
              (a match {
                case Syntax.Var(_) => Predicate.bot_pred[Unit]
                case Syntax.Const(_) => Predicate.bot_pred[Unit]
                case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                case Syntax.Plus(theta_1, theta_2) =>
                  Predicate.bind[Unit,
                    Unit](dfree_i[A, B](theta_1),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](dfree_i[A, B](theta_2),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                case Syntax.Differential(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
              B],
              Unit](Predicate.single[Syntax.trm[A, B]](x),
              ((a: Syntax.trm[A, B]) =>
                (a match {
                  case Syntax.Var(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Const(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Function(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Functional(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Plus(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Times(theta_1, theta_2) =>
                    Predicate.bind[Unit,
                      Unit](dfree_i[A, B](theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](dfree_i[A, B](theta_2), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.DiffVar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Differential(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                Unit](Predicate.single[Syntax.trm[A, B]](x),
                ((a: Syntax.trm[A, B]) =>
                  (a match {
                    case Syntax.Var(_) => Predicate.single[Unit](())
                    case Syntax.Const(_) => Predicate.bot_pred[Unit]
                    case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                    case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                  B],
                  Unit](Predicate.single[Syntax.trm[A,
                  B]](x),
                  ((a: Syntax.trm[A, B]) =>
                    (a match {
                      case Syntax.Var(_) => Predicate.bot_pred[Unit]
                      case Syntax.Const(_) => Predicate.single[Unit](())
                      case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                      case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                    B],
                    Unit](Predicate.single[Syntax.trm[A, B]](x),
                    ((a: Syntax.trm[A, B]) =>
                      (a match {
                        case Syntax.Var(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Const(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Function(_, args) =>
                          Predicate.bind[Unit,
                            Unit](Predicate.if_pred(HOL.All[B](((i: B) =>
                            Syntax.dfree[A, B](args(i))))),
                            ((aa: Unit) => {
                              val (): Unit = aa;
                              Predicate.single[Unit](())
                            }))
                        case Syntax.Functional(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Plus(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Times(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.DiffVar(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Differential(_) =>
                          Predicate.bot_pred[Unit]
                      }))),
                    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                      Unit](Predicate.single[Syntax.trm[A, B]](x),
                      ((a: Syntax.trm[A, B]) =>
                        (a match {
                          case Syntax.Var(_) => Predicate.bot_pred[Unit]
                          case Syntax.Const(_) => Predicate.bot_pred[Unit]
                          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                          case Syntax.Plus(theta_1, theta_2) =>
                            Predicate.bind[Unit,
                              Unit](dfree_i[A, B](theta_1),
                              ((aa: Unit) =>
                              {
                                val (): Unit = aa;
                                Predicate.bind[Unit,
                                  Unit](dfree_i[A, B](theta_2),
                                  ((ab: Unit) => {
                                    val (): Unit = ab;
                                    Predicate.single[Unit](())
                                  }))
                              }))
                          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                        }))),
                      Predicate.bind[Syntax.trm[A, B],
                        Unit](Predicate.single[Syntax.trm[A, B]](x),
                        ((a: Syntax.trm[A, B]) =>
                          (a match {
                            case Syntax.Var(_) => Predicate.bot_pred[Unit]
                            case Syntax.Const(_) => Predicate.bot_pred[Unit]
                            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Times(theta_1, theta_2) =>
                              Predicate.bind[Unit,
                                Unit](dfree_i[A, B](theta_1),
                                ((aa: Unit) =>
                                {
                                  val (): Unit = aa;
                                  Predicate.bind[Unit,
                                    Unit](dfree_i[A, B](theta_2),
                                    ((ab: Unit) =>
                                    {
                                      val (): Unit = ab;
                                      Predicate.single[Unit](())
                                    }))
                                }))
                            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                          }))))))))))))
*/
  def dsafe_i[A, B : Enum.enum](x: Syntax.trm[A, B]): Predicate.pred[Unit] =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
      Unit](Predicate.single[Syntax.trm[A, B]](x),
      ((a: Syntax.trm[A, B]) =>
        (a match {
          case Syntax.Var(_) => Predicate.single[Unit](())
          case Syntax.Const(_) => Predicate.bot_pred[Unit]
          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
        B],
        Unit](Predicate.single[Syntax.trm[A, B]](x),
        ((a: Syntax.trm[A, B]) =>
          (a match {
            case Syntax.Var(_) => Predicate.bot_pred[Unit]
            case Syntax.Const(_) => Predicate.single[Unit](())
            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
          Unit](Predicate.single[Syntax.trm[A, B]](x),
          ((a: Syntax.trm[A, B]) =>
            (a match {
              case Syntax.Var(_) => Predicate.bot_pred[Unit]
              case Syntax.Const(_) => Predicate.bot_pred[Unit]
              case Syntax.Function(_, args) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[B](((i: B) =>
                  Syntax.dsafe[A, B](args(i))))),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    Predicate.single[Unit](())
                  }))
              case Syntax.Functional(_) => Predicate.bot_pred[Unit]
              case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
              case Syntax.Differential(_) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
            Unit](Predicate.single[Syntax.trm[A, B]](x),
            ((a: Syntax.trm[A, B]) =>
              (a match {
                case Syntax.Var(_) => Predicate.bot_pred[Unit]
                case Syntax.Const(_) => Predicate.bot_pred[Unit]
                case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Functional(_) => Predicate.single[Unit](())
                case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                case Syntax.Differential(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
              B],
              Unit](Predicate.single[Syntax.trm[A, B]](x),
              ((a: Syntax.trm[A, B]) =>
                (a match {
                  case Syntax.Var(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Const(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Function(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Functional(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Plus(theta_1, theta_2) =>
                    Predicate.bind[Unit,
                      Unit](dsafe_i[A, B](theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](dsafe_i[A, B](theta_2), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.Times(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.DiffVar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Differential(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                Unit](Predicate.single[Syntax.trm[A, B]](x),
                ((a: Syntax.trm[A, B]) =>
                  (a match {
                    case Syntax.Var(_) => Predicate.bot_pred[Unit]
                    case Syntax.Const(_) => Predicate.bot_pred[Unit]
                    case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                    case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Times(theta_1, theta_2) =>
                      Predicate.bind[Unit,
                        Unit](dsafe_i[A, B](theta_1),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](dsafe_i[A, B](theta_2),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                  B],
                  Unit](Predicate.single[Syntax.trm[A,
                  B]](x),
                  ((a: Syntax.trm[A, B]) =>
                    (a match {
                      case Syntax.Var(_) => Predicate.bot_pred[Unit]
                      case Syntax.Const(_) => Predicate.bot_pred[Unit]
                      case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                      case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Differential(theta) =>
                        Predicate.bind[Unit,
                          Unit](dfree_i[A, B](theta),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.single[Unit](())
                          }))
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                    B],
                    Unit](Predicate.single[Syntax.trm[A, B]](x),
                    ((a: Syntax.trm[A, B]) =>
                      (a match {
                        case Syntax.Var(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Const(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Function(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Functional(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Plus(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Times(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.DiffVar(_) =>
                          Predicate.single[Unit](())
                        case Syntax.Differential(_) =>
                          Predicate.bot_pred[Unit]
                      }))),
                    Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                      Unit](Predicate.single[Syntax.trm[A, B]](x),
                      ((a: Syntax.trm[A, B]) =>
                        (a match {
                          case Syntax.Var(_) => Predicate.single[Unit](())
                          case Syntax.Const(_) => Predicate.bot_pred[Unit]
                          case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                          case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                          case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                        }))),
                      Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                        B],
                        Unit](Predicate.single[Syntax.trm[A,
                        B]](x),
                        ((a: Syntax.trm[A, B]) =>
                          (a match {
                            case Syntax.Var(_) => Predicate.bot_pred[Unit]
                            case Syntax.Const(_) => Predicate.single[Unit](())
                            case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                            case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                            case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                          }))),
                        Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                          Unit](Predicate.single[Syntax.trm[A, B]](x),
                          ((a: Syntax.trm[A, B]) =>
                            (a match {
                              case Syntax.Var(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Const(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Function(_, args) =>
                                Predicate.bind[Unit,
                                  Unit](Predicate.if_pred(HOL.All[B](((i: B) =>
                                  Syntax.dsafe[A, B](args(i))))),
                                  ((aa: Unit) => {
                                    val (): Unit = aa;
                                    Predicate.single[Unit](())
                                  }))
                              case Syntax.Functional(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Plus(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Times(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.DiffVar(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Differential(_) =>
                                Predicate.bot_pred[Unit]
                            }))),
                          Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                            Unit](Predicate.single[Syntax.trm[A, B]](x),
                            ((a: Syntax.trm[A, B]) =>
                              (a match {
                                case Syntax.Var(_) => Predicate.bot_pred[Unit]
                                case Syntax.Const(_) => Predicate.bot_pred[Unit]
                                case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Functional(_) => Predicate.single[Unit](())
                                case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                                case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                              }))),
                            Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A,
                              B],
                              Unit](Predicate.single[Syntax.trm[A, B]](x),
                              ((a: Syntax.trm[A, B]) =>
                                (a match {
                                  case Syntax.Var(_) => Predicate.bot_pred[Unit]
                                  case Syntax.Const(_) => Predicate.bot_pred[Unit]
                                  case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                                  case Syntax.Plus(theta_1, theta_2) =>
                                    Predicate.bind[Unit,
                                      Unit](dsafe_i[A, B](theta_1),
                                      ((aa: Unit) =>
                                      {
                                        val (): Unit = aa;
                                        Predicate.bind[Unit,
                                          Unit](dsafe_i[A, B](theta_2),
                                          ((ab: Unit) => {
                                            val (): Unit = ab;
                                            Predicate.single[Unit](())
                                          }))
                                      }))
                                  case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                                  case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                                }))),
                              Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                                Unit](Predicate.single[Syntax.trm[A, B]](x),
                                ((a: Syntax.trm[A, B]) =>
                                  (a match {
                                    case Syntax.Var(_) => Predicate.bot_pred[Unit]
                                    case Syntax.Const(_) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Function(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Functional(_) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Plus(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Times(theta_1, theta_2) =>
                                      Predicate.bind[Unit,
                                        Unit](dsafe_i[A, B](theta_1),
                                        ((aa: Unit) =>
                                        {
                                          val (): Unit = aa;
                                          Predicate.bind[Unit,
                                            Unit](dsafe_i[A, B](theta_2),
                                            ((ab: Unit) => {
                                              val (): Unit = ab;
                                              Predicate.single[Unit](())
                                            }))
                                        }))
                                    case Syntax.DiffVar(_) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Differential(_) =>
                                      Predicate.bot_pred[Unit]
                                  }))),
                                Predicate.sup_pred[Unit](Predicate.bind[Syntax.trm[A, B],
                                  Unit](Predicate.single[Syntax.trm[A, B]](x),
                                  ((a: Syntax.trm[A, B]) =>
                                    (a match {
                                      case Syntax.Var(_) => Predicate.bot_pred[Unit]
                                      case Syntax.Const(_) => Predicate.bot_pred[Unit]
                                      case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                                      case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.DiffVar(_) => Predicate.bot_pred[Unit]
                                      case Syntax.Differential(theta) =>
                                        Predicate.bind[Unit,
                                          Unit](dfree_i[A, B](theta),
                                          ((aa: Unit) => {
                                            val (): Unit = aa;
                                            Predicate.single[Unit](())
                                          }))
                                    }))),
                                  Predicate.bind[Syntax.trm[A, B],
                                    Unit](Predicate.single[Syntax.trm[A, B]](x),
                                    ((a: Syntax.trm[A, B]) =>
                                      (a match {
                                        case Syntax.Var(_) => Predicate.bot_pred[Unit]
                                        case Syntax.Const(_) => Predicate.bot_pred[Unit]
                                        case Syntax.Function(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Functional(_) => Predicate.bot_pred[Unit]
                                        case Syntax.Plus(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Times(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.DiffVar(_) => Predicate.single[Unit](())
                                        case Syntax.Differential(_) => Predicate.bot_pred[Unit]
                                      }))))))))))))))))))

  def osafe_i[A, B : Enum.enum : HOL.equal](xa: Syntax.ODE[A, B]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[A, B],
      Unit](Predicate.single[Syntax.ODE[A, B]](xa),
      ((a: Syntax.ODE[A, B]) =>
        (a match {
          case Syntax.OVar(_) => Predicate.single[Unit](())
          case Syntax.OSing(_, _) => Predicate.bot_pred[Unit]
          case Syntax.OProd(_, _) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[A,
        B],
        Unit](Predicate.single[Syntax.ODE[A, B]](xa),
        ((a: Syntax.ODE[A, B]) =>
          (a match {
            case Syntax.OVar(_) => Predicate.bot_pred[Unit]
            case Syntax.OSing(_, theta) =>
              Predicate.bind[Unit,
                Unit](dfree_i[A, B](theta),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case Syntax.OProd(_, _) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[A, B],
          Unit](Predicate.single[Syntax.ODE[A, B]](xa),
          ((a: Syntax.ODE[A, B]) =>
            (a match {
              case Syntax.OVar(_) => Predicate.bot_pred[Unit]
              case Syntax.OSing(_, _) => Predicate.bot_pred[Unit]
              case Syntax.OProd(oDE1, oDE2) =>
                Predicate.bind[Unit,
                  Unit](osafe_i[A, B](oDE1),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](osafe_i[A, B](oDE2),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](eq_i_i[Set.set[B]](Set.inf_set[B](Syntax.ODE_dom[A,
                          B](oDE1),
                          Syntax.ODE_dom[A, B](oDE2)),
                          Set.bot_set[B]),
                          ((ac: Unit) => {
                            val (): Unit = ac;
                            Predicate.single[Unit](())
                          }))
                      }))
                  }))
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[A, B],
            Unit](Predicate.single[Syntax.ODE[A, B]](xa),
            ((a: Syntax.ODE[A, B]) =>
              (a match {
                case Syntax.OVar(_) => Predicate.single[Unit](())
                case Syntax.OSing(_, _) => Predicate.bot_pred[Unit]
                case Syntax.OProd(_, _) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.ODE[A,
              B],
              Unit](Predicate.single[Syntax.ODE[A, B]](xa),
              ((a: Syntax.ODE[A, B]) =>
                (a match {
                  case Syntax.OVar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.OSing(_, theta) =>
                    Predicate.bind[Unit,
                      Unit](dfree_i[A, B](theta),
                      ((aa: Unit) => {
                        val (): Unit = aa;
                        Predicate.single[Unit](())
                      }))
                  case Syntax.OProd(_, _) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.bind[Syntax.ODE[A, B],
                Unit](Predicate.single[Syntax.ODE[A, B]](xa),
                ((a: Syntax.ODE[A, B]) =>
                  (a match {
                    case Syntax.OVar(_) => Predicate.bot_pred[Unit]
                    case Syntax.OSing(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.OProd(oDE1, oDE2) =>
                      Predicate.bind[Unit,
                        Unit](osafe_i[A, B](oDE1),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](osafe_i[A, B](oDE2),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.bind[Unit,
                                Unit](eq_i_i[Set.set[B]](Set.inf_set[B](Syntax.ODE_dom[A,
                                B](oDE1),
                                Syntax.ODE_dom[A, B](oDE2)),
                                Set.bot_set[B]),
                                ((ac: Unit) =>
                                {
                                  val (): Unit = ac;
                                  Predicate.single[Unit](())
                                }))
                            }))
                        }))
                  }))))))))

  def hpsafe_i[A, B, C : Enum.enum : HOL.equal](xa: Syntax.hp[A, B, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
      Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
      ((a: Syntax.hp[A, B, C]) =>
        (a match {
          case Syntax.Pvar(_) => Predicate.single[Unit](())
          case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
          case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Test(_) => Predicate.bot_pred[Unit]
          case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Loop(_) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A,
        B, C],
        Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
        ((a: Syntax.hp[A, B, C]) =>
          (a match {
            case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
            case Syntax.Assign(_, e) =>
              Predicate.bind[Unit,
                Unit](dsafe_i[A, C](e),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Test(_) => Predicate.bot_pred[Unit]
            case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Loop(_) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
          Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
          ((a: Syntax.hp[A, B, C]) =>
            (a match {
              case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
              case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
              case Syntax.DiffAssign(_, e) =>
                Predicate.bind[Unit,
                  Unit](dsafe_i[A, C](e), ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
              case Syntax.Test(_) => Predicate.bot_pred[Unit]
              case Syntax.EvolveODE(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Sequence(_, _) =>
                Predicate.bot_pred[Unit]
              case Syntax.Loop(_) => Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
            Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
            ((a: Syntax.hp[A, B, C]) =>
              (a match {
                case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Test(p) =>
                  Predicate.bind[Unit,
                    Unit](fsafe_i[A, B, C](p),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.single[Unit](())
                    }))
                case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Loop(_) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A,
              B, C],
              Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
              ((a: Syntax.hp[A, B, C]) =>
                (a match {
                  case Syntax.Pvar(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Assign(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.DiffAssign(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Test(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.EvolveODE(ode, p) =>
                    Predicate.bind[Unit,
                      Unit](osafe_i[A, C](ode),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](fsafe_i[A, B, C](p), ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                      }))
                  case Syntax.Choice(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Sequence(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Loop(_) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
                Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                ((a: Syntax.hp[A, B, C]) =>
                  (a match {
                    case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                    case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.DiffAssign(_, _) =>
                      Predicate.bot_pred[Unit]
                    case Syntax.Test(_) => Predicate.bot_pred[Unit]
                    case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Choice(aa, b) =>
                      Predicate.bind[Unit,
                        Unit](hpsafe_i[A, B, C](aa),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[A, B, C](b),
                            ((ac: Unit) =>
                            {
                              val (): Unit = ac;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A,
                  B, C],
                  Unit](Predicate.single[Syntax.hp[A, B,
                  C]](xa),
                  ((a: Syntax.hp[A, B, C]) =>
                    (a match {
                      case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                      case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Test(_) => Predicate.bot_pred[Unit]
                      case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Sequence(aa, b) =>
                        Predicate.bind[Unit,
                          Unit](hpsafe_i[A, B, C](aa),
                          ((ab: Unit) =>
                          {
                            val (): Unit = ab;
                            Predicate.bind[Unit,
                              Unit](hpsafe_i[A, B, C](b),
                              ((ac: Unit) => {
                                val (): Unit = ac;
                                Predicate.single[Unit](())
                              }))
                          }))
                      case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B,
                    C],
                    Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                    ((a: Syntax.hp[A, B, C]) =>
                      (a match {
                        case Syntax.Pvar(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Assign(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.DiffAssign(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Test(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.EvolveODE(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Choice(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Sequence(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Loop(aa) =>
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[A, B, C](aa),
                            ((ab: Unit) => {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                      }))),
                    Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
                      Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                      ((a: Syntax.hp[A, B, C]) =>
                        (a match {
                          case Syntax.Pvar(_) => Predicate.single[Unit](())
                          case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Test(_) => Predicate.bot_pred[Unit]
                          case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                        }))),
                      Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A,
                        B, C],
                        Unit](Predicate.single[Syntax.hp[A, B,
                        C]](xa),
                        ((a: Syntax.hp[A, B, C]) =>
                          (a match {
                            case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                            case Syntax.Assign(_, e) =>
                              Predicate.bind[Unit,
                                Unit](dsafe_i[A, C](e),
                                ((aa: Unit) => {
                                  val (): Unit = aa;
                                  Predicate.single[Unit](())
                                }))
                            case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Test(_) => Predicate.bot_pred[Unit]
                            case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                          }))),
                        Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B,
                          C],
                          Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                          ((a: Syntax.hp[A, B, C]) =>
                            (a match {
                              case Syntax.Pvar(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Assign(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.DiffAssign(_, e) =>
                                Predicate.bind[Unit,
                                  Unit](dsafe_i[A, C](e),
                                  ((aa: Unit) => {
                                    val (): Unit = aa;
                                    Predicate.single[Unit](())
                                  }))
                              case Syntax.Test(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.EvolveODE(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Choice(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Sequence(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Loop(_) =>
                                Predicate.bot_pred[Unit]
                            }))),
                          Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
                            Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                            ((a: Syntax.hp[A, B, C]) =>
                              (a match {
                                case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                                case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Test(p) =>
                                  Predicate.bind[Unit,
                                    Unit](fsafe_i[A, B, C](p),
                                    ((aa: Unit) => {
                                      val (): Unit = aa;
                                      Predicate.single[Unit](())
                                    }))
                                case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                              }))),
                            Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A,
                              B, C],
                              Unit](Predicate.single[Syntax.hp[A, B,
                              C]](xa),
                              ((a: Syntax.hp[A, B, C]) =>
                                (a match {
                                  case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                                  case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Test(_) => Predicate.bot_pred[Unit]
                                  case Syntax.EvolveODE(ode, p) =>
                                    Predicate.bind[Unit,
                                      Unit](osafe_i[A, C](ode),
                                      ((aa: Unit) =>
                                      {
                                        val (): Unit = aa;
                                        Predicate.bind[Unit,
                                          Unit](fsafe_i[A, B, C](p),
                                          ((ab: Unit) => {
                                            val (): Unit = ab;
                                            Predicate.single[Unit](())
                                          }))
                                      }))
                                  case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                                }))),
                              Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
                                Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                                ((a: Syntax.hp[A, B, C]) =>
                                  (a match {
                                    case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                                    case Syntax.Assign(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.DiffAssign(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Test(_) => Predicate.bot_pred[Unit]
                                    case Syntax.EvolveODE(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Choice(aa, b) =>
                                      Predicate.bind[Unit,
                                        Unit](hpsafe_i[A, B, C](aa),
                                        ((ab: Unit) =>
                                        {
                                          val (): Unit = ab;
                                          Predicate.bind[Unit,
                                            Unit](hpsafe_i[A, B, C](b),
                                            ((ac: Unit) => {
                                              val (): Unit = ac;
                                              Predicate.single[Unit](())
                                            }))
                                        }))
                                    case Syntax.Sequence(_, _) =>
                                      Predicate.bot_pred[Unit]
                                    case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                                  }))),
                                Predicate.sup_pred[Unit](Predicate.bind[Syntax.hp[A, B, C],
                                  Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                                  ((a: Syntax.hp[A, B, C]) =>
                                    (a match {
                                      case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                                      case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.Test(_) => Predicate.bot_pred[Unit]
                                      case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                                      case Syntax.Sequence(aa, b) =>
                                        Predicate.bind[Unit,
                                          Unit](hpsafe_i[A, B, C](aa),
                                          ((ab: Unit) =>
                                          {
                                            val (): Unit = ab;
                                            Predicate.bind[Unit,
                                              Unit](hpsafe_i[A, B, C](b),
                                              ((ac: Unit) => {
                                                val (): Unit = ac;
                                                Predicate.single[Unit](())
                                              }))
                                          }))
                                      case Syntax.Loop(_) => Predicate.bot_pred[Unit]
                                    }))),
                                  Predicate.bind[Syntax.hp[A, B, C],
                                    Unit](Predicate.single[Syntax.hp[A, B, C]](xa),
                                    ((a: Syntax.hp[A, B, C]) =>
                                      (a match {
                                        case Syntax.Pvar(_) => Predicate.bot_pred[Unit]
                                        case Syntax.Assign(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.DiffAssign(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Test(_) => Predicate.bot_pred[Unit]
                                        case Syntax.EvolveODE(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Choice(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Sequence(_, _) => Predicate.bot_pred[Unit]
                                        case Syntax.Loop(aa) =>
                                          Predicate.bind[Unit,
                                            Unit](hpsafe_i[A, B, C](aa),
                                            ((ab: Unit) => {
                                              val (): Unit = ab;
                                              Predicate.single[Unit](())
                                            }))
                                      }))))))))))))))))))

  def fsafe_i[A, B, C : Enum.enum : HOL.equal](xa: Syntax.formula[A, B, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
      Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
      ((a: Syntax.formula[A, B, C]) =>
        (a match {
          case Syntax.Geq(t1, t2) =>
            Predicate.bind[Unit,
              Unit](dsafe_i[A, C](t1),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](dsafe_i[A, C](t2),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
          case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Not(_) => Predicate.bot_pred[Unit]
          case Syntax.And(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
          case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
          case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
        B, C],
        Unit](Predicate.single[Syntax.formula[A, B,
        C]](xa),
        ((a: Syntax.formula[A, B, C]) =>
          (a match {
            case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Prop(_, args) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                Syntax.dsafe[A, C](args(i))))),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case Syntax.Not(_) => Predicate.bot_pred[Unit]
            case Syntax.And(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
            case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
            case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
          Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
          ((a: Syntax.formula[A, B, C]) =>
            (a match {
              case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Not(pa) =>
                Predicate.bind[Unit,
                  Unit](fsafe_i[A, B, C](pa), ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
              case Syntax.And(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
              case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
              case Syntax.InContext(_, _) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
            Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
            ((a: Syntax.formula[A, B, C]) =>
              (a match {
                case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Not(_) => Predicate.bot_pred[Unit]
                case Syntax.And(pa, q) =>
                  Predicate.bind[Unit,
                    Unit](fsafe_i[A, B, C](pa),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](fsafe_i[A, B, C](q),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
              B, C],
              Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
              ((a: Syntax.formula[A, B, C]) =>
                (a match {
                  case Syntax.Geq(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Prop(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Not(_) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.And(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.Exists(_, pa) =>
                    Predicate.bind[Unit,
                      Unit](fsafe_i[A, B, C](pa),
                      ((aa: Unit) => {
                        val (): Unit = aa;
                        Predicate.single[Unit](())
                      }))
                  case Syntax.Diamond(_, _) =>
                    Predicate.bot_pred[Unit]
                  case Syntax.InContext(_, _) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
                Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
                ((a: Syntax.formula[A, B, C]) =>
                  (a match {
                    case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Not(_) => Predicate.bot_pred[Unit]
                    case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                    case Syntax.Diamond(aa, pa) =>
                      Predicate.bind[Unit,
                        Unit](fsafe_i[A, B, C](pa),
                        ((b: Unit) =>
                        {
                          val (): Unit = b;
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[A, B, C](aa),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
                  B, C],
                  Unit](Predicate.single[Syntax.formula[A,
                  B, C]](xa),
                  ((a: Syntax.formula[A, B, C]) =>
                    (a match {
                      case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Not(_) => Predicate.bot_pred[Unit]
                      case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                      case Syntax.InContext(_, f) =>
                        Predicate.bind[Unit,
                          Unit](fsafe_i[A, B, C](f),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.single[Unit](())
                          }))
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
                    B, C],
                    Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
                    ((a: Syntax.formula[A, B, C]) =>
                      (a match {
                        case Syntax.Geq(t1, t2) =>
                          Predicate.bind[Unit,
                            Unit](dsafe_i[A, C](t1),
                            ((aa: Unit) =>
                            {
                              val (): Unit = aa;
                              Predicate.bind[Unit,
                                Unit](dsafe_i[A, C](t2), ((ab: Unit) => {
                                val (): Unit = ab;
                                Predicate.single[Unit](())
                              }))
                            }))
                        case Syntax.Prop(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Not(_) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.And(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Exists(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.Diamond(_, _) =>
                          Predicate.bot_pred[Unit]
                        case Syntax.InContext(_, _) =>
                          Predicate.bot_pred[Unit]
                      }))),
                    Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
                      Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
                      ((a: Syntax.formula[A, B, C]) =>
                        (a match {
                          case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Prop(_, args) =>
                            Predicate.bind[Unit,
                              Unit](Predicate.if_pred(HOL.All[C](((i: C) => Syntax.dsafe[A, C](args(i))))),
                              ((aa: Unit) => {
                                val (): Unit = aa;
                                Predicate.single[Unit](())
                              }))
                          case Syntax.Not(_) => Predicate.bot_pred[Unit]
                          case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                          case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                        }))),
                      Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
                        B, C],
                        Unit](Predicate.single[Syntax.formula[A, B,
                        C]](xa),
                        ((a: Syntax.formula[A, B, C]) =>
                          (a match {
                            case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Not(pa) =>
                              Predicate.bind[Unit,
                                Unit](fsafe_i[A, B, C](pa),
                                ((aa: Unit) => {
                                  val (): Unit = aa;
                                  Predicate.single[Unit](())
                                }))
                            case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                            case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                          }))),
                        Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
                          B, C],
                          Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
                          ((a: Syntax.formula[A, B, C]) =>
                            (a match {
                              case Syntax.Geq(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Prop(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Not(_) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.And(pa, q) =>
                                Predicate.bind[Unit,
                                  Unit](fsafe_i[A, B, C](pa),
                                  ((aa: Unit) =>
                                  {
                                    val (): Unit = aa;
                                    Predicate.bind[Unit,
                                      Unit](fsafe_i[A, B, C](q), ((ab: Unit) => {
                                      val (): Unit = ab;
                                      Predicate.single[Unit](())
                                    }))
                                  }))
                              case Syntax.Exists(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.Diamond(_, _) =>
                                Predicate.bot_pred[Unit]
                              case Syntax.InContext(_, _) =>
                                Predicate.bot_pred[Unit]
                            }))),
                          Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A, B, C],
                            Unit](Predicate.single[Syntax.formula[A, B, C]](xa),
                            ((a: Syntax.formula[A, B, C]) =>
                              (a match {
                                case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Not(_) => Predicate.bot_pred[Unit]
                                case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.Exists(_, pa) =>
                                  Predicate.bind[Unit,
                                    Unit](fsafe_i[A, B, C](pa),
                                    ((aa: Unit) => {
                                      val (): Unit = aa;
                                      Predicate.single[Unit](())
                                    }))
                                case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                                case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                              }))),
                            Predicate.sup_pred[Unit](Predicate.bind[Syntax.formula[A,
                              B, C],
                              Unit](Predicate.single[Syntax.formula[A, B,
                              C]](xa),
                              ((a: Syntax.formula[A, B, C]) =>
                                (a match {
                                  case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Not(_) => Predicate.bot_pred[Unit]
                                  case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                                  case Syntax.Diamond(aa, pa) =>
                                    Predicate.bind[Unit,
                                      Unit](fsafe_i[A, B, C](pa),
                                      ((b: Unit) =>
                                      {
                                        val (): Unit = b;
                                        Predicate.bind[Unit,
                                          Unit](hpsafe_i[A, B, C](aa),
                                          ((ab: Unit) => {
                                            val (): Unit = ab;
                                            Predicate.single[Unit](())
                                          }))
                                      }))
                                  case Syntax.InContext(_, _) => Predicate.bot_pred[Unit]
                                }))),
                              Predicate.bind[Syntax.formula[A, B, C],
                                Unit](Predicate.single[Syntax.formula[A, B,
                                C]](xa),
                                ((a: Syntax.formula[A, B, C]) =>
                                  (a match {
                                    case Syntax.Geq(_, _) => Predicate.bot_pred[Unit]
                                    case Syntax.Prop(_, _) => Predicate.bot_pred[Unit]
                                    case Syntax.Not(_) => Predicate.bot_pred[Unit]
                                    case Syntax.And(_, _) => Predicate.bot_pred[Unit]
                                    case Syntax.Exists(_, _) => Predicate.bot_pred[Unit]
                                    case Syntax.Diamond(_, _) => Predicate.bot_pred[Unit]
                                    case Syntax.InContext(_, f) =>
                                      Predicate.bind[Unit,
                                        Unit](fsafe_i[A, B, C](f),
                                        ((aa: Unit) => {
                                          val (): Unit = aa;
                                          Predicate.single[Unit](())
                                        }))
                                  }))))))))))))))))

  def PPadmit_i_i[A : Enum.enum : HOL.equal, B, C,
  D : Enum.enum : HOL.equal](xa: A => Syntax.formula[B, C, D],
                             xb: Syntax.hp[B, Sum_Type.sum[C, A], D]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.formula[B, C, D],
      Syntax.hp[B, Sum_Type.sum[C, A], D]),
      Unit](Predicate.single[(A => Syntax.formula[B, C, D],
      Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
      ((a: (A => Syntax.formula[B, C, D],
        Syntax.hp[B, Sum_Type.sum[C, A], D]))
      =>
        (a match {
          case (_, Syntax.Pvar(_)) => Predicate.single[Unit](())
          case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.formula[B, C, D],
        Syntax.hp[B, Sum_Type.sum[C, A], D]),
        Unit](Predicate.single[(A =>
        Syntax.formula[B, C, D],
        Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
        ((a:
          (A => Syntax.formula[B, C, D], Syntax.hp[B, Sum_Type.sum[C, A], D]))
        =>
          (a match {
            case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Sequence(aa, b)) =>
              Predicate.bind[Unit,
                Unit](PPadmit_i_i[A, B, C, D](sigma, aa),
                ((ab: Unit) =>
                {
                  val (): Unit = ab;
                  Predicate.bind[Unit,
                    Unit](PPadmit_i_i[A, B, C, D](sigma, b),
                    ((ac: Unit) =>
                    {
                      val (): Unit = ac;
                      Predicate.bind[Unit,
                        Unit](Predicate.if_pred(USubst.PPUadmit[A, B,
                        C, D](sigma, b,
                        Static_Semantics.BVP[B, C, D](USubst.PPsubst[B, C, A, D](aa, sigma)))),
                        ((ad: Unit) =>
                        {
                          val (): Unit = ad;
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[B, C,
                            D](USubst.PPsubst[B, C, A, D](aa, sigma)),
                            ((ae: Unit) => {
                              val (): Unit = ae;
                              Predicate.single[Unit](())
                            }))
                        }))
                    }))
                }))
            case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A =>
          Syntax.formula[B, C, D],
          Syntax.hp[B, Sum_Type.sum[C, A], D]),
          Unit](Predicate.single[(A => Syntax.formula[B, C, D],
          Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
          ((a: (A => Syntax.formula[B, C, D],
            Syntax.hp[B, Sum_Type.sum[C, A], D]))
          =>
            (a match {
              case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Assign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffAssign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.EvolveODE(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Choice(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Sequence(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Loop(aa)) =>
                Predicate.bind[Unit,
                  Unit](PPadmit_i_i[A, B, C, D](sigma, aa),
                  ((ab: Unit) =>
                  {
                    val (): Unit = ab;
                    Predicate.bind[Unit,
                      Unit](Predicate.if_pred(USubst.PPUadmit[A, B, C,
                      D](sigma, aa,
                      Static_Semantics.BVP[B, C,
                        D](USubst.PPsubst[B, C, A, D](aa, sigma)))),
                      ((ac: Unit) =>
                      {
                        val (): Unit = ac;
                        Predicate.bind[Unit,
                          Unit](hpsafe_i[B, C,
                          D](USubst.PPsubst[B, C, A, D](aa, sigma)),
                          ((ad: Unit) => {
                            val (): Unit = ad;
                            Predicate.single[Unit](())
                          }))
                      }))
                  }))
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.formula[B, C, D],
            Syntax.hp[B, Sum_Type.sum[C, A], D]),
            Unit](Predicate.single[(A => Syntax.formula[B, C, D],
            Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
            ((a: (A => Syntax.formula[B, C, D],
              Syntax.hp[B, Sum_Type.sum[C, A], D]))
            =>
              (a match {
                case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.EvolveODE(ode, phi)) =>
                  Predicate.bind[Unit,
                    Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](Predicate.if_pred(USubst.PFUadmit[A, B, C,
                        D](sigma, phi, Static_Semantics.BVO[B, D](ode))),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.formula[B, C, D],
              Syntax.hp[B, Sum_Type.sum[C, A], D]),
              Unit](Predicate.single[(A => Syntax.formula[B, C, D],
              Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
              ((a: (A => Syntax.formula[B, C, D],
                Syntax.hp[B, Sum_Type.sum[C, A], D]))
              =>
                (a match {
                  case (_, Syntax.Pvar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Assign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.DiffAssign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Test(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.EvolveODE(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.Choice(aa, b)) =>
                    Predicate.bind[Unit,
                      Unit](PPadmit_i_i[A, B, C, D](sigma, aa),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](PPadmit_i_i[A, B, C, D](sigma, b),
                          ((ac: Unit) => {
                            val (): Unit = ac;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Sequence(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Loop(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A =>
                Syntax.formula[B, C, D],
                Syntax.hp[B, Sum_Type.sum[C, A], D]),
                Unit](Predicate.single[(A => Syntax.formula[B, C, D],
                Syntax.hp[B, Sum_Type.sum[C, A],
                  D])]((xa, xb)),
                ((a: (A => Syntax.formula[B, C, D],
                  Syntax.hp[B, Sum_Type.sum[C, A], D]))
                =>
                  (a match {
                    case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Assign(_, _)) =>
                      Predicate.single[Unit](())
                    case (_, Syntax.DiffAssign(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.EvolveODE(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Choice(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Sequence(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(A =>
                  Syntax.formula[B, C, D],
                  Syntax.hp[B, Sum_Type.sum[C, A], D]),
                  Unit](Predicate.single[(A =>
                  Syntax.formula[B, C, D],
                  Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
                  ((a: (A => Syntax.formula[B, C, D], Syntax.hp[B, Sum_Type.sum[C, A], D]))
                  =>
                    (a match {
                      case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.DiffAssign(_, _)) => Predicate.single[Unit](())
                      case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.bind[(A => Syntax.formula[B, C, D],
                    Syntax.hp[B, Sum_Type.sum[C, A], D]),
                    Unit](Predicate.single[(A => Syntax.formula[B, C, D],
                    Syntax.hp[B, Sum_Type.sum[C, A], D])]((xa, xb)),
                    ((a: (A => Syntax.formula[B, C, D], Syntax.hp[B, Sum_Type.sum[C, A], D]))
                    =>
                      (a match {
                        case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                        case (sigma, Syntax.Test(phi)) =>
                          Predicate.bind[Unit,
                            Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                            ((aa: Unit) =>
                            {
                              val (): Unit = aa;
                              Predicate.single[Unit](())
                            }))
                        case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                      }))))))))))

  def PFadmit_i_i[A : Enum.enum : HOL.equal, B, C,
  D : Enum.enum : HOL.equal](xa: A => Syntax.formula[B, C, D],
                             xb: Syntax.formula[B, Sum_Type.sum[C, A], D]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.formula[B, C, D],
      Syntax.formula[B, Sum_Type.sum[C, A], D]),
      Unit](Predicate.single[(A => Syntax.formula[B, C, D],
      Syntax.formula[B, Sum_Type.sum[C, A],
        D])]((xa, xb)),
      ((a: (A => Syntax.formula[B, C, D],
        Syntax.formula[B, Sum_Type.sum[C, A], D]))
      =>
        (a match {
          case (_, Syntax.Geq(_, _)) => Predicate.single[Unit](())
          case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.formula[B, C, D],
        Syntax.formula[B, Sum_Type.sum[C, A], D]),
        Unit](Predicate.single[(A =>
        Syntax.formula[B, C, D],
        Syntax.formula[B, Sum_Type.sum[C, A], D])]((xa, xb)),
        ((a:
          (A => Syntax.formula[B, C, D], Syntax.formula[B, Sum_Type.sum[C, A], D]))
        =>
          (a match {
            case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Prop(_, _)) => Predicate.single[Unit](())
            case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A =>
          Syntax.formula[B, C, D],
          Syntax.formula[B, Sum_Type.sum[C, A], D]),
          Unit](Predicate.single[(A => Syntax.formula[B, C, D],
          Syntax.formula[B, Sum_Type.sum[C, A], D])]((xa, xb)),
          ((a: (A => Syntax.formula[B, C, D],
            Syntax.formula[B, Sum_Type.sum[C, A], D]))
          =>
            (a match {
              case (_, Syntax.Geq(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Prop(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Not(phi)) =>
                Predicate.bind[Unit,
                  Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    Predicate.single[Unit](())
                  }))
              case (_, Syntax.And(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Exists(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Diamond(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.InContext(_, _)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.formula[B, C, D],
            Syntax.formula[B, Sum_Type.sum[C, A], D]),
            Unit](Predicate.single[(A => Syntax.formula[B, C, D],
            Syntax.formula[B, Sum_Type.sum[C, A], D])]((xa, xb)),
            ((a: (A => Syntax.formula[B, C, D],
              Syntax.formula[B, Sum_Type.sum[C, A], D]))
            =>
              (a match {
                case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.And(phi, psi)) =>
                  Predicate.bind[Unit,
                    Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](PFadmit_i_i[A, B, C, D](sigma, psi),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.formula[B, C, D],
              Syntax.formula[B, Sum_Type.sum[C, A], D]),
              Unit](Predicate.single[(A => Syntax.formula[B, C, D],
              Syntax.formula[B, Sum_Type.sum[C, A], D])]((xa, xb)),
              ((a: (A => Syntax.formula[B, C, D],
                Syntax.formula[B, Sum_Type.sum[C, A], D]))
              =>
                (a match {
                  case (_, Syntax.Geq(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Prop(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Not(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.And(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.Exists(x, phi)) =>
                    Predicate.bind[Unit,
                      Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](Predicate.if_pred(USubst.PFUadmit[A, B, C,
                          D](sigma, phi,
                          Set.insert[Sum_Type.sum[D, D]](Sum_Type.Inl[D, D](x),
                            Set.bot_set[Sum_Type.sum[D, D]]))),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Diamond(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.InContext(_, _)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A =>
                Syntax.formula[B, C, D],
                Syntax.formula[B, Sum_Type.sum[C, A], D]),
                Unit](Predicate.single[(A => Syntax.formula[B, C, D],
                Syntax.formula[B, Sum_Type.sum[C, A],
                  D])]((xa, xb)),
                ((a: (A => Syntax.formula[B, C, D],
                  Syntax.formula[B, Sum_Type.sum[C, A], D]))
                =>
                  (a match {
                    case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Exists(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Diamond(aa, phi)) =>
                      Predicate.bind[Unit,
                        Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](PPadmit_i_i[A, B, C, D](sigma, aa),
                            ((ac: Unit) =>
                            {
                              val (): Unit = ac;
                              Predicate.bind[Unit,
                                Unit](Predicate.if_pred(USubst.PFUadmit[A, B, C,
                                D](sigma, phi,
                                Static_Semantics.BVP[B, C,
                                  D](USubst.PPsubst[B, C, A, D](aa, sigma)))),
                                ((ad: Unit) => {
                                  val (): Unit = ad;
                                  Predicate.single[Unit](())
                                }))
                            }))
                        }))
                    case (_, Syntax.InContext(_, _)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.bind[(A =>
                  Syntax.formula[B, C, D],
                  Syntax.formula[B, Sum_Type.sum[C, A], D]),
                  Unit](Predicate.single[(A => Syntax.formula[B, C, D],
                  Syntax.formula[B, Sum_Type.sum[C, A],
                    D])]((xa, xb)),
                  ((a: (A => Syntax.formula[B, C, D],
                    Syntax.formula[B, Sum_Type.sum[C, A], D]))
                  =>
                    (a match {
                      case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Prop(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Exists(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Diamond(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (sigma, Syntax.InContext(_, phi)) =>
                        Predicate.bind[Unit,
                          Unit](PFadmit_i_i[A, B, C, D](sigma, phi),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.bind[Unit,
                              Unit](Predicate.if_pred(USubst.PFUadmit[A, B, C,
                              D](sigma, phi,
                              Set.top_set[Sum_Type.sum[D, D]])),
                              ((ab: Unit) =>
                              {
                                val (): Unit = ab;
                                Predicate.single[Unit](())
                              }))
                          }))
                    })))))))))

  def TadmitFFO_i_i[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](xa: A => Syntax.trm[B, C],
                             xb: Syntax.trm[Sum_Type.sum[B, A], C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
      Syntax.trm[Sum_Type.sum[B, A], C]),
      Unit](Predicate.single[(A => Syntax.trm[B, C],
      Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
      ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
        (a match {
          case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
          case (sigma, Syntax.Differential(theta)) =>
            Predicate.bind[Unit,
              Unit](TadmitFFO_i_i[A, B, C](sigma, theta),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(USubst.NTUadmit[A, B,
                  C](sigma, theta, Set.top_set[Sum_Type.sum[C, C]])),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.trm[B, C],
        Syntax.trm[Sum_Type.sum[B, A], C]),
        Unit](Predicate.single[(A => Syntax.trm[B, C],
        Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
        ((a:
          (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C]))
        =>
          (a match {
            case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Function(Sum_Type.Inl(_), args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.TadmitFFO[A, B, C](sigma, args(i))))),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case (_, Syntax.Function(Sum_Type.Inr(_), _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
          Syntax.trm[Sum_Type.sum[B, A], C]),
          Unit](Predicate.single[(A => Syntax.trm[B, C],
          Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
          ((a: (A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C]))
          =>
            (a match {
              case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Function(Sum_Type.Inl(_), _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Function(Sum_Type.Inr(fa), args))
              => Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.TadmitFFO[A, B, C](sigma, args(i))))),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](dfree_i[B, C](sigma(fa)),
                    ((ab: Unit) => {
                      val (): Unit = ab;
                      Predicate.single[Unit](())
                    }))
                }))
              case (_, Syntax.Functional(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Plus(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Times(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffVar(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Differential(_)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C]),
            Unit](Predicate.single[(A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
            ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
              (a match {
                case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.Plus(theta_1, theta_2)) =>
                  Predicate.bind[Unit,
                    Unit](TadmitFFO_i_i[A, B, C](sigma, theta_1),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](TadmitFFO_i_i[A, B, C](sigma, theta_2),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.trm[B, C],
              Syntax.trm[Sum_Type.sum[B, A], C]),
              Unit](Predicate.single[(A => Syntax.trm[B, C],
              Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
              ((a: (A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A], C]))
              =>
                (a match {
                  case (_, Syntax.Var(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Const(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Function(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Functional(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Plus(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case
                    (sigma, Syntax.Times(theta_1, theta_2)) =>
                    Predicate.bind[Unit,
                      Unit](TadmitFFO_i_i[A, B, C](sigma, theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](TadmitFFO_i_i[A, B, C](sigma, theta_2),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.DiffVar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Differential(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A], C]),
                Unit](Predicate.single[(A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A],
                  C])]((xa, xb)),
                ((a: (A => Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A], C]))
                =>
                  (a match {
                    case (_, Syntax.Var(_)) => Predicate.single[Unit](())
                    case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Function(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Functional(_)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Times(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Differential(_)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.bind[(A => Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A], C]),
                  Unit](Predicate.single[(A => Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A],
                    C])]((xa, xb)),
                  ((a: (A => Syntax.trm[B, C],
                    Syntax.trm[Sum_Type.sum[B, A], C]))
                  =>
                    (a match {
                      case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Const(_)) =>
                        Predicate.single[Unit](())
                      case (_, Syntax.Function(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Functional(_)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Plus(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Times(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.DiffVar(_)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Differential(_)) =>
                        Predicate.bot_pred[Unit]
                    })))))))))

  def TadmitFO_i_i[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](xa: A => Syntax.trm[B, C],
                             xb: Syntax.trm[Sum_Type.sum[B, A], C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
      Syntax.trm[Sum_Type.sum[B, A], C]),
      Unit](Predicate.single[(A => Syntax.trm[B, C],
      Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
      ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
        (a match {
          case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
          case (sigma, Syntax.Differential(theta)) =>
            Predicate.bind[Unit,
              Unit](TadmitFFO_i_i[A, B, C](sigma, theta),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(USubst.NTUadmit[A, B,
                  C](sigma, theta, Set.top_set[Sum_Type.sum[C, C]])),
                  ((ab: Unit) =>
                  {
                    val (): Unit = ab;
                    Predicate.bind[Unit,
                      Unit](dfree_i[B, C](USubst.TsubstFO[B, A, C](theta, sigma)),
                      ((ac: Unit) => {
                        val (): Unit = ac;
                        Predicate.single[Unit](())
                      }))
                  }))
              }))
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.trm[B, C],
        Syntax.trm[Sum_Type.sum[B, A], C]),
        Unit](Predicate.single[(A => Syntax.trm[B, C],
        Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
        ((a:
          (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C]))
        =>
          (a match {
            case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Function(_, args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.TadmitFO[A, B, C](sigma, args(i))))),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
          Syntax.trm[Sum_Type.sum[B, A], C]),
          Unit](Predicate.single[(A => Syntax.trm[B, C],
          Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
          ((a: (A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C]))
          =>
            (a match {
              case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Function(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Functional(Sum_Type.Inl(_))) =>
                Predicate.single[Unit](())
              case (_, Syntax.Functional(Sum_Type.Inr(_))) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Plus(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Times(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffVar(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Differential(_)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C]),
            Unit](Predicate.single[(A => Syntax.trm[B, C],
            Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
            ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
              (a match {
                case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.Plus(theta_1, theta_2)) =>
                  Predicate.bind[Unit,
                    Unit](TadmitFO_i_i[A, B, C](sigma, theta_1),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](TadmitFO_i_i[A, B, C](sigma, theta_2),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.trm[B, C],
              Syntax.trm[Sum_Type.sum[B, A], C]),
              Unit](Predicate.single[(A => Syntax.trm[B, C],
              Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
              ((a: (A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A], C]))
              =>
                (a match {
                  case (_, Syntax.Var(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Const(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Function(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Functional(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Plus(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case
                    (sigma, Syntax.Times(theta_1, theta_2)) =>
                    Predicate.bind[Unit,
                      Unit](TadmitFO_i_i[A, B, C](sigma, theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](TadmitFO_i_i[A, B, C](sigma, theta_2),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.DiffVar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Differential(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A], C]),
                Unit](Predicate.single[(A => Syntax.trm[B, C],
                Syntax.trm[Sum_Type.sum[B, A],
                  C])]((xa, xb)),
                ((a: (A => Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A], C]))
                =>
                  (a match {
                    case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Function(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Functional(_)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Times(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.DiffVar(_)) =>
                      Predicate.single[Unit](())
                    case (_, Syntax.Differential(_)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(A =>
                  Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A], C]),
                  Unit](Predicate.single[(A =>
                  Syntax.trm[B, C],
                  Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
                  ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
                    (a match {
                      case (_, Syntax.Var(_)) => Predicate.single[Unit](())
                      case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.bind[(A => Syntax.trm[B, C],
                    Syntax.trm[Sum_Type.sum[B, A], C]),
                    Unit](Predicate.single[(A => Syntax.trm[B, C],
                    Syntax.trm[Sum_Type.sum[B, A], C])]((xa, xb)),
                    ((a: (A => Syntax.trm[B, C], Syntax.trm[Sum_Type.sum[B, A], C])) =>
                      (a match {
                        case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Const(_)) => Predicate.single[Unit](())
                        case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
                      }))))))))))

  def OadmitFO_i_i_i[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](xa: A => Syntax.trm[B, C],
                             xb: Syntax.ODE[Sum_Type.sum[B, A], C], xc: Set.set[Sum_Type.sum[C, C]]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
      (Syntax.ODE[Sum_Type.sum[B, A], C], Set.set[Sum_Type.sum[C, C]])),
      Unit](Predicate.single[(A => Syntax.trm[B, C],
      (Syntax.ODE[Sum_Type.sum[B, A], C],
        Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
      ((a: (A => Syntax.trm[B, C],
        (Syntax.ODE[Sum_Type.sum[B, A], C],
          Set.set[Sum_Type.sum[C, C]])))
      =>
        (a match {
          case (sigma, (Syntax.OVar(c), u)) =>
            Predicate.bind[Unit,
              Unit](Predicate.if_pred(USubst.OUadmitFO[A, B,
              C](sigma,
              Syntax.OVar[C, Sum_Type.sum[B, A]](c),
              u)),
              ((aa: Unit) => {
                val (): Unit = aa;
                Predicate.single[Unit](())
              }))
          case (_, (Syntax.OSing(_, _), _)) => Predicate.bot_pred[Unit]
          case (_, (Syntax.OProd(_, _), _)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.trm[B, C],
        (Syntax.ODE[Sum_Type.sum[B, A], C],
          Set.set[Sum_Type.sum[C, C]])),
        Unit](Predicate.single[(A => Syntax.trm[B, C],
        (Syntax.ODE[Sum_Type.sum[B, A], C],
          Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
        ((a:
          (A => Syntax.trm[B, C],
            (Syntax.ODE[Sum_Type.sum[B, A], C], Set.set[Sum_Type.sum[C, C]])))
        =>
          (a match {
            case (_, (Syntax.OVar(_), _)) => Predicate.bot_pred[Unit]
            case (sigma, (Syntax.OSing(x, theta), u)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(USubst.OUadmitFO[A, B,
                C](sigma, Syntax.OSing[C, Sum_Type.sum[B, A]](x, theta),
                u)),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](TadmitFFO_i_i[A, B, C](sigma, theta),
                    ((ab: Unit) => {
                      val (): Unit = ab;
                      Predicate.single[Unit](())
                    }))
                }))
            case (_, (Syntax.OProd(_, _), _)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.bind[(A => Syntax.trm[B, C],
          (Syntax.ODE[Sum_Type.sum[B, A], C],
            Set.set[Sum_Type.sum[C, C]])),
          Unit](Predicate.single[(A => Syntax.trm[B, C],
          (Syntax.ODE[Sum_Type.sum[B, A], C],
            Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
          ((a:
            (A => Syntax.trm[B, C],
              (Syntax.ODE[Sum_Type.sum[B, A], C], Set.set[Sum_Type.sum[C, C]])))
          =>
            (a match {
              case (_, (Syntax.OVar(_), _)) => Predicate.bot_pred[Unit]
              case (_, (Syntax.OSing(_, _), _)) => Predicate.bot_pred[Unit]
              case (sigma, (Syntax.OProd(oDE1, oDE2), u)) =>
                Predicate.bind[Unit,
                  Unit](OadmitFO_i_i_i[A, B, C](sigma, oDE1, u),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](OadmitFO_i_i_i[A, B, C](sigma, oDE2, u),
                      ((ab: Unit) => {
                        val (): Unit = ab;
                        Predicate.single[Unit](())
                      }))
                  }))
            })))))

  def NPadmit_i_i[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal,
  D : HOL.equal](xa: A => Syntax.trm[B, C],
                 xb: Syntax.hp[Sum_Type.sum[B, A], D, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
      Syntax.hp[Sum_Type.sum[B, A], D, C]),
      Unit](Predicate.single[(A => Syntax.trm[B, C],
      Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
      ((a: (A => Syntax.trm[B, C], Syntax.hp[Sum_Type.sum[B, A], D, C])) =>
        (a match {
          case (_, Syntax.Pvar(_)) => Predicate.single[Unit](())
          case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.trm[B, C],
        Syntax.hp[Sum_Type.sum[B, A], D, C]),
        Unit](Predicate.single[(A => Syntax.trm[B, C],
        Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
        ((a:
          (A => Syntax.trm[B, C], Syntax.hp[Sum_Type.sum[B, A], D, C]))
        =>
          (a match {
            case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Sequence(aa, b)) =>
              Predicate.bind[Unit,
                Unit](NPadmit_i_i[A, B, C, D](sigma, aa),
                ((ab: Unit) =>
                {
                  val (): Unit = ab;
                  Predicate.bind[Unit,
                    Unit](NPadmit_i_i[A, B, C, D](sigma, b),
                    ((ac: Unit) =>
                    {
                      val (): Unit = ac;
                      Predicate.bind[Unit,
                        Unit](Predicate.if_pred(USubst.PUadmitFO[A, B,
                        C, D](sigma, b,
                        Static_Semantics.BVP[B, D, C](USubst.PsubstFO[B, A, D, C](aa, sigma)))),
                        ((ad: Unit) =>
                        {
                          val (): Unit = ad;
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[B, D,
                            C](USubst.PsubstFO[B, A, D, C](aa, sigma)),
                            ((ae: Unit) => {
                              val (): Unit = ae;
                              Predicate.single[Unit](())
                            }))
                        }))
                    }))
                }))
            case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
          Syntax.hp[Sum_Type.sum[B, A], D, C]),
          Unit](Predicate.single[(A => Syntax.trm[B, C],
          Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
          ((a: (A => Syntax.trm[B, C],
            Syntax.hp[Sum_Type.sum[B, A], D, C]))
          =>
            (a match {
              case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Assign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffAssign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.EvolveODE(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Choice(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Sequence(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Loop(aa)) =>
                Predicate.bind[Unit,
                  Unit](NPadmit_i_i[A, B, C, D](sigma, aa),
                  ((ab: Unit) =>
                  {
                    val (): Unit = ab;
                    Predicate.bind[Unit,
                      Unit](Predicate.if_pred(USubst.PUadmitFO[A, B,
                      C, D](sigma, aa,
                      Static_Semantics.BVP[B, D, C](USubst.PsubstFO[B, A, D, C](aa, sigma)))),
                      ((ac: Unit) =>
                      {
                        val (): Unit = ac;
                        Predicate.bind[Unit,
                          Unit](hpsafe_i[B, D,
                          C](USubst.PsubstFO[B, A, D, C](aa, sigma)),
                          ((ad: Unit) => {
                            val (): Unit = ad;
                            Predicate.single[Unit](())
                          }))
                      }))
                  }))
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
            Syntax.hp[Sum_Type.sum[B, A], D, C]),
            Unit](Predicate.single[(A => Syntax.trm[B, C],
            Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
            ((a: (A => Syntax.trm[B, C], Syntax.hp[Sum_Type.sum[B, A], D, C])) =>
              (a match {
                case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.EvolveODE(ode, phi)) =>
                  Predicate.bind[Unit,
                    Unit](OadmitFO_i_i_i[A, B,
                    C](sigma, ode, Static_Semantics.BVO[Sum_Type.sum[B, A], C](ode)),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](Predicate.if_pred(USubst.FUadmitFO[A, B, C,
                            D](sigma, phi, Static_Semantics.BVO[Sum_Type.sum[B, A], C](ode))),
                            ((ac: Unit) =>
                            {
                              val (): Unit = ac;
                              Predicate.bind[Unit,
                                Unit](fsafe_i[B, D,
                                C](USubst.FsubstFO[B, A, D, C](phi, sigma)),
                                ((ad: Unit) =>
                                {
                                  val (): Unit = ad;
                                  Predicate.bind[Unit,
                                    Unit](osafe_i[B, C](USubst.OsubstFO[B, A, C](ode, sigma)),
                                    ((ae: Unit) => {
                                      val (): Unit = ae;
                                      Predicate.single[Unit](())
                                    }))
                                }))
                            }))
                        }))
                    }))
                case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.trm[B, C],
              Syntax.hp[Sum_Type.sum[B, A], D, C]),
              Unit](Predicate.single[(A => Syntax.trm[B, C],
              Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
              ((a: (A => Syntax.trm[B, C],
                Syntax.hp[Sum_Type.sum[B, A], D, C]))
              =>
                (a match {
                  case (_, Syntax.Pvar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Assign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.DiffAssign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Test(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.EvolveODE(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.Choice(aa, b)) =>
                    Predicate.bind[Unit,
                      Unit](NPadmit_i_i[A, B, C, D](sigma, aa),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](NPadmit_i_i[A, B, C, D](sigma, b),
                          ((ac: Unit) => {
                            val (): Unit = ac;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Sequence(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Loop(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
                Syntax.hp[Sum_Type.sum[B, A], D, C]),
                Unit](Predicate.single[(A => Syntax.trm[B, C],
                Syntax.hp[Sum_Type.sum[B, A], D,
                  C])]((xa, xb)),
                ((a: (A => Syntax.trm[B, C],
                  Syntax.hp[Sum_Type.sum[B, A], D, C]))
                =>
                  (a match {
                    case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Assign(_, theta)) =>
                      Predicate.bind[Unit,
                        Unit](TadmitFO_i_i[A, B, C](sigma, theta),
                        ((aa: Unit) => {
                          val (): Unit = aa;
                          Predicate.single[Unit](())
                        }))
                    case (_, Syntax.DiffAssign(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.EvolveODE(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Choice(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Sequence(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(A =>
                  Syntax.trm[B, C],
                  Syntax.hp[Sum_Type.sum[B, A], D, C]),
                  Unit](Predicate.single[(A =>
                  Syntax.trm[B, C],
                  Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
                  ((a: (A => Syntax.trm[B, C], Syntax.hp[Sum_Type.sum[B, A], D, C])) =>
                    (a match {
                      case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                      case (sigma, Syntax.DiffAssign(_, theta)) =>
                        Predicate.bind[Unit,
                          Unit](TadmitFO_i_i[A, B, C](sigma, theta),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.single[Unit](())
                          }))
                      case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.bind[(A => Syntax.trm[B, C],
                    Syntax.hp[Sum_Type.sum[B, A], D, C]),
                    Unit](Predicate.single[(A => Syntax.trm[B, C],
                    Syntax.hp[Sum_Type.sum[B, A], D, C])]((xa, xb)),
                    ((a: (A => Syntax.trm[B, C], Syntax.hp[Sum_Type.sum[B, A], D, C])) =>
                      (a match {
                        case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                        case (sigma, Syntax.Test(phi)) =>
                          Predicate.bind[Unit,
                            Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                            ((aa: Unit) =>
                            {
                              val (): Unit = aa;
                              Predicate.single[Unit](())
                            }))
                        case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                      }))))))))))

  def NFadmit_i_i[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal,
  D : HOL.equal](xa: A => Syntax.trm[B, C],
                 xb: Syntax.formula[Sum_Type.sum[B, A], D, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
      Syntax.formula[Sum_Type.sum[B, A], D, C]),
      Unit](Predicate.single[(A => Syntax.trm[B, C],
      Syntax.formula[Sum_Type.sum[B, A], D,
        C])]((xa, xb)),
      ((a: (A => Syntax.trm[B, C],
        Syntax.formula[Sum_Type.sum[B, A], D, C]))
      =>
        (a match {
          case (sigma, Syntax.Geq(theta_1, theta_2)) =>
            Predicate.bind[Unit,
              Unit](TadmitFO_i_i[A, B, C](sigma, theta_1),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](TadmitFO_i_i[A, B, C](sigma, theta_2),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
          case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(A =>
        Syntax.trm[B, C],
        Syntax.formula[Sum_Type.sum[B, A], D, C]),
        Unit](Predicate.single[(A => Syntax.trm[B, C],
        Syntax.formula[Sum_Type.sum[B, A], D, C])]((xa, xb)),
        ((a:
          (A => Syntax.trm[B, C], Syntax.formula[Sum_Type.sum[B, A], D, C]))
        =>
          (a match {
            case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Prop(_, args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.TadmitFO[A, B, C](sigma, args(i))))),
                ((aa: Unit) => {
                  val (): Unit = aa;
                  Predicate.single[Unit](())
                }))
            case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
          Syntax.formula[Sum_Type.sum[B, A], D, C]),
          Unit](Predicate.single[(A => Syntax.trm[B, C],
          Syntax.formula[Sum_Type.sum[B, A], D, C])]((xa, xb)),
          ((a: (A => Syntax.trm[B, C],
            Syntax.formula[Sum_Type.sum[B, A], D, C]))
          =>
            (a match {
              case (_, Syntax.Geq(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Prop(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Not(phi)) =>
                Predicate.bind[Unit,
                  Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    Predicate.single[Unit](())
                  }))
              case (_, Syntax.And(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Exists(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Diamond(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.InContext(_, _)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
            Syntax.formula[Sum_Type.sum[B, A], D, C]),
            Unit](Predicate.single[(A => Syntax.trm[B, C],
            Syntax.formula[Sum_Type.sum[B, A], D, C])]((xa, xb)),
            ((a: (A => Syntax.trm[B, C], Syntax.formula[Sum_Type.sum[B, A], D, C]))
            =>
              (a match {
                case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.And(phi, psi)) =>
                  Predicate.bind[Unit,
                    Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](NFadmit_i_i[A, B, C, D](sigma, psi),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(A =>
              Syntax.trm[B, C],
              Syntax.formula[Sum_Type.sum[B, A], D, C]),
              Unit](Predicate.single[(A => Syntax.trm[B, C],
              Syntax.formula[Sum_Type.sum[B, A], D, C])]((xa, xb)),
              ((a: (A => Syntax.trm[B, C],
                Syntax.formula[Sum_Type.sum[B, A], D, C]))
              =>
                (a match {
                  case (_, Syntax.Geq(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Prop(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Not(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.And(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.Exists(x, phi)) =>
                    Predicate.bind[Unit,
                      Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](Predicate.if_pred(USubst.FUadmitFO[A, B, C,
                          D](sigma, phi,
                          Set.insert[Sum_Type.sum[C, C]](Sum_Type.Inl[C, C](x),
                            Set.bot_set[Sum_Type.sum[C, C]]))),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Diamond(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.InContext(_, _)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(A => Syntax.trm[B, C],
                Syntax.formula[Sum_Type.sum[B, A], D, C]),
                Unit](Predicate.single[(A => Syntax.trm[B, C],
                Syntax.formula[Sum_Type.sum[B, A], D,
                  C])]((xa, xb)),
                ((a: (A => Syntax.trm[B, C],
                  Syntax.formula[Sum_Type.sum[B, A], D, C]))
                =>
                  (a match {
                    case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Exists(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Diamond(aa, phi)) =>
                      Predicate.bind[Unit,
                        Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](NPadmit_i_i[A, B, C, D](sigma, aa),
                            ((ac: Unit) =>
                            {
                              val (): Unit = ac;
                              Predicate.bind[Unit,
                                Unit](Predicate.if_pred(USubst.FUadmitFO[A, B, C,
                                D](sigma, phi,
                                Static_Semantics.BVP[B, D,
                                  C](USubst.PsubstFO[B, A, D, C](aa, sigma)))),
                                ((ad: Unit) =>
                                {
                                  val (): Unit = ad;
                                  Predicate.bind[Unit,
                                    Unit](hpsafe_i[B, D, C](USubst.PsubstFO[B, A, D, C](aa, sigma)),
                                    ((ae: Unit) => {
                                      val (): Unit = ae;
                                      Predicate.single[Unit](())
                                    }))
                                }))
                            }))
                        }))
                    case (_, Syntax.InContext(_, _)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.bind[(A => Syntax.trm[B, C],
                  Syntax.formula[Sum_Type.sum[B, A], D, C]),
                  Unit](Predicate.single[(A => Syntax.trm[B, C],
                  Syntax.formula[Sum_Type.sum[B, A], D,
                    C])]((xa, xb)),
                  ((a: (A => Syntax.trm[B, C],
                    Syntax.formula[Sum_Type.sum[B, A], D, C]))
                  =>
                    (a match {
                      case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Prop(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Exists(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (_, Syntax.Diamond(_, _)) =>
                        Predicate.bot_pred[Unit]
                      case (sigma, Syntax.InContext(_, phi)) =>
                        Predicate.bind[Unit,
                          Unit](NFadmit_i_i[A, B, C, D](sigma, phi),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.bind[Unit,
                              Unit](Predicate.if_pred(USubst.FUadmitFO[A, B, C,
                              D](sigma, phi,
                              Set.top_set[Sum_Type.sum[C, C]])),
                              ((ab: Unit) =>
                              {
                                val (): Unit = ab;
                                Predicate.single[Unit](())
                              }))
                          }))
                    })))))))))

  def Tadmit_i_i[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](xa: USubst.subst_ext[A, B, C, Unit],
                             xb: Syntax.trm[A, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
      Syntax.trm[A, C]),
      Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
      Syntax.trm[A, C])]((xa, xb)),
      ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
        (a match {
          case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
          case (sigma, Syntax.Differential(theta)) =>
            Predicate.bind[Unit,
              Unit](Tadmit_i_i[A, B, C](sigma, theta),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(USubst.TUadmit[A, B,
                  C](sigma, theta, Set.top_set[Sum_Type.sum[C, C]])),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
        B, C, Unit],
        Syntax.trm[A, C]),
        Unit](Predicate.single[(USubst.subst_ext[A, B, C,
        Unit],
        Syntax.trm[A, C])]((xa, xb)),
        ((a:
          (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C]))
        =>
          (a match {
            case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Function(f, args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.Tadmit[A, B, C](sigma, args(i))))),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Option[Syntax.trm[Sum_Type.sum[A,
                    C],
                    C]],
                    Unit](eq_i_o[Option[Syntax.trm[Sum_Type.sum[A, C],
                    C]]]((USubst.SFunctions[A, B, C,
                    Unit](sigma)).apply(f)),
                    ((ab: Option[Syntax.trm[Sum_Type.sum[A, C], C]]) =>
                      (ab match {
                        case None => Predicate.bot_pred[Unit]
                        case Some(f_a) =>
                          Predicate.bind[Unit,
                            Unit](TadmitFO_i_i[C, A,
                            C](((i: C) => USubst.Tsubst[A, C, B](args(i), sigma)), f_a),
                            ((ac: Unit) => {
                              val (): Unit = ac;
                              Predicate.single[Unit](())
                            }))
                      })))
                }))
            case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
          Unit],
          Syntax.trm[A, C]),
          Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
          Syntax.trm[A, C])]((xa, xb)),
          ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C]))
          =>
            (a match {
              case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
              case (sigma, Syntax.Function(f, args)) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                  USubst.Tadmit[A, B, C](sigma, args(i))))),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](eq_i_i[Option[Syntax.trm[Sum_Type.sum[A,
                      C],
                      C]]]((USubst.SFunctions[A, B, C, Unit](sigma)).apply(f),
                      None),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.single[Unit](())
                      }))
                  }))
              case (_, Syntax.Functional(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Plus(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Times(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffVar(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Differential(_)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
            Syntax.trm[A, C]),
            Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
            Syntax.trm[A, C])]((xa, xb)),
            ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
              (a match {
                case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.Functional(f)) =>
                  Predicate.bind[Option[Syntax.trm[A, C]],
                    Unit](eq_i_o[Option[Syntax.trm[A,
                    C]]]((USubst.SFunls[A, B, C, Unit](sigma)).apply(f)),
                    ((aa: Option[Syntax.trm[A, C]]) =>
                      (aa match {
                        case None => Predicate.bot_pred[Unit]
                        case Some(fa) =>
                          Predicate.bind[Unit,
                            Unit](Tadmit_i_i[A, B, C](sigma, fa),
                            ((ab: Unit) => {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                      })))
                case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
              B, C, Unit],
              Syntax.trm[A, C]),
              Unit](Predicate.single[(USubst.subst_ext[A, B, C,
              Unit],
              Syntax.trm[A, C])]((xa, xb)),
              ((a: (USubst.subst_ext[A, B, C, Unit],
                Syntax.trm[A, C]))
              =>
                (a match {
                  case (_, Syntax.Var(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Const(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Function(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Functional(_)) =>
                    Predicate.bot_pred[Unit]
                  case
                    (sigma, Syntax.Plus(theta_1, theta_2)) =>
                    Predicate.bind[Unit,
                      Unit](Tadmit_i_i[A, B, C](sigma, theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](Tadmit_i_i[A, B, C](sigma, theta_2),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Times(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.DiffVar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Differential(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
                Unit],
                Syntax.trm[A, C]),
                Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                Syntax.trm[A, C])]((xa, xb)),
                ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
                  (a match {
                    case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Function(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Functional(_)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Times(theta_1, theta_2)) =>
                      Predicate.bind[Unit,
                        Unit](Tadmit_i_i[A, B, C](sigma, theta_1),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](Tadmit_i_i[A, B, C](sigma, theta_2),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Differential(_)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.trm[A, C]),
                  Unit](Predicate.single[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.trm[A, C])]((xa, xb)),
                  ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
                    (a match {
                      case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.DiffVar(_)) => Predicate.single[Unit](())
                      case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                    B, C, Unit],
                    Syntax.trm[A, C]),
                    Unit](Predicate.single[(USubst.subst_ext[A, B, C,
                    Unit],
                    Syntax.trm[A, C])]((xa, xb)),
                    ((a: (USubst.subst_ext[A, B, C, Unit],
                      Syntax.trm[A, C]))
                    =>
                      (a match {
                        case (_, Syntax.Var(_)) =>
                          Predicate.single[Unit](())
                        case (_, Syntax.Const(_)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Function(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Functional(_)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Plus(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Times(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffVar(_)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Differential(_)) =>
                          Predicate.bot_pred[Unit]
                      }))),
                    Predicate.bind[(USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C]),
                      Unit](Predicate.single[(USubst.subst_ext[A, B, C,
                      Unit],
                      Syntax.trm[A, C])]((xa, xb)),
                      ((a: (USubst.subst_ext[A, B, C, Unit],
                        Syntax.trm[A, C]))
                      =>
                        (a match {
                          case (_, Syntax.Var(_)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Const(_)) =>
                            Predicate.single[Unit](())
                          case (_, Syntax.Function(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Functional(_)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Plus(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Times(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.DiffVar(_)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Differential(_)) =>
                            Predicate.bot_pred[Unit]
                        })))))))))))

  def TadmitF_i_i[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](xa: USubst.subst_ext[A, B, C, Unit],
                             xb: Syntax.trm[A, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
      Syntax.trm[A, C]),
      Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
      Syntax.trm[A, C])]((xa, xb)),
      ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
        (a match {
          case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
          case (sigma, Syntax.Differential(theta)) =>
            Predicate.bind[Unit,
              Unit](TadmitF_i_i[A, B, C](sigma, theta),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(USubst.TUadmit[A, B,
                  C](sigma, theta, Set.top_set[Sum_Type.sum[C, C]])),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
        B, C, Unit],
        Syntax.trm[A, C]),
        Unit](Predicate.single[(USubst.subst_ext[A, B, C,
        Unit],
        Syntax.trm[A, C])]((xa, xb)),
        ((a:
          (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C]))
        =>
          (a match {
            case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Function(f, args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.TadmitF[A, B, C](sigma, args(i))))),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                    Syntax.dfree[A, C](USubst.Tsubst[A, C, B](args(i), sigma))))),
                    ((ab: Unit) =>
                    {
                      val (): Unit = ab;
                      Predicate.bind[Option[Syntax.trm[Sum_Type.sum[A, C], C]],
                        Unit](eq_i_o[Option[Syntax.trm[Sum_Type.sum[A,
                        C],
                        C]]]((USubst.SFunctions[A, B, C,
                        Unit](sigma)).apply(f)),
                        ((ac: Option[Syntax.trm[Sum_Type.sum[A, C], C]]) =>
                          (ac match {
                            case None => Predicate.bot_pred[Unit]
                            case Some(fa) =>
                              Predicate.bind[Unit,
                                Unit](TadmitFFO_i_i[C, A,
                                C](((i: C) => USubst.Tsubst[A, C, B](args(i), sigma)), fa),
                                ((ad: Unit) => {
                                  val (): Unit = ad;
                                  Predicate.single[Unit](())
                                }))
                          })))
                    }))
                }))
            case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
          Unit],
          Syntax.trm[A, C]),
          Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
          Syntax.trm[A, C])]((xa, xb)),
          ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C]))
          =>
            (a match {
              case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
              case (sigma, Syntax.Function(f, args)) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                  USubst.TadmitF[A, B, C](sigma, args(i))))),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](eq_i_i[Option[Syntax.trm[Sum_Type.sum[A,
                      C],
                      C]]]((USubst.SFunctions[A, B, C, Unit](sigma)).apply(f),
                      None),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.single[Unit](())
                      }))
                  }))
              case (_, Syntax.Functional(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Plus(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Times(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffVar(_)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Differential(_)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
            Syntax.trm[A, C]),
            Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
            Syntax.trm[A, C])]((xa, xb)),
            ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
              (a match {
                case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.Plus(theta_1, theta_2)) =>
                  Predicate.bind[Unit,
                    Unit](TadmitF_i_i[A, B, C](sigma, theta_1),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](TadmitF_i_i[A, B, C](sigma, theta_2),
                        ((ab: Unit) => {
                          val (): Unit = ab;
                          Predicate.single[Unit](())
                        }))
                    }))
                case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
              B, C, Unit],
              Syntax.trm[A, C]),
              Unit](Predicate.single[(USubst.subst_ext[A, B, C,
              Unit],
              Syntax.trm[A, C])]((xa, xb)),
              ((a: (USubst.subst_ext[A, B, C, Unit],
                Syntax.trm[A, C]))
              =>
                (a match {
                  case (_, Syntax.Var(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Const(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Function(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Functional(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Plus(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case
                    (sigma, Syntax.Times(theta_1, theta_2)) =>
                    Predicate.bind[Unit,
                      Unit](TadmitF_i_i[A, B, C](sigma, theta_1),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](TadmitF_i_i[A, B, C](sigma, theta_2),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.DiffVar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Differential(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
                Unit],
                Syntax.trm[A, C]),
                Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                Syntax.trm[A, C])]((xa, xb)),
                ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
                  (a match {
                    case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Function(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Functional(_)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Times(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.DiffVar(_)) =>
                      Predicate.single[Unit](())
                    case (_, Syntax.Differential(_)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.trm[A, C]),
                  Unit](Predicate.single[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.trm[A, C])]((xa, xb)),
                  ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
                    (a match {
                      case (_, Syntax.Var(_)) => Predicate.single[Unit](())
                      case (_, Syntax.Const(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
                    Syntax.trm[A, C]),
                    Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                    Syntax.trm[A, C])]((xa, xb)),
                    ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.trm[A, C])) =>
                      (a match {
                        case (_, Syntax.Var(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Const(_)) => Predicate.single[Unit](())
                        case (_, Syntax.Function(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Functional(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Plus(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Times(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffVar(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Differential(_)) => Predicate.bot_pred[Unit]
                      }))))))))))

  def Oadmit_i_i_i[A : Enum.enum : HOL.equal, B,
  C : Enum.enum : HOL.equal](xa:
                             USubst.subst_ext[A, B, C, Unit],
                             xb: Syntax.ODE[A, C], xc: Set.set[Sum_Type.sum[C, C]]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
      (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])),
      Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
      (Syntax.ODE[A, C],
        Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
      ((a: (USubst.subst_ext[A, B, C, Unit],
        (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])))
      =>
        (a match {
          case (_, (Syntax.OVar(_), _)) => Predicate.single[Unit](())
          case (_, (Syntax.OSing(_, _), _)) => Predicate.bot_pred[Unit]
          case (_, (Syntax.OProd(_, _), _)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
        B, C, Unit],
        (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])),
        Unit](Predicate.single[(USubst.subst_ext[A, B, C,
        Unit],
        (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
        ((a:
          (USubst.subst_ext[A, B, C, Unit],
            (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])))
        =>
          (a match {
            case (_, (Syntax.OVar(_), _)) => Predicate.bot_pred[Unit]
            case (sigma, (Syntax.OSing(_, theta), u)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(USubst.TUadmit[A, B,
                C](sigma, theta, u)),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](TadmitF_i_i[A, B, C](sigma, theta),
                    ((ab: Unit) => {
                      val (): Unit = ab;
                      Predicate.single[Unit](())
                    }))
                }))
            case (_, (Syntax.OProd(_, _), _)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
          (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])),
          Unit](Predicate.single[(USubst.subst_ext[A, B, C,
          Unit],
          (Syntax.ODE[A, C],
            Set.set[Sum_Type.sum[C, C]]))]((xa, (xb, xc))),
          ((a:
            (USubst.subst_ext[A, B, C, Unit],
              (Syntax.ODE[A, C], Set.set[Sum_Type.sum[C, C]])))
          =>
            (a match {
              case (_, (Syntax.OVar(_), _)) => Predicate.bot_pred[Unit]
              case (_, (Syntax.OSing(_, _), _)) => Predicate.bot_pred[Unit]
              case (sigma, (Syntax.OProd(oDE1, oDE2), u)) =>
                Predicate.bind[Unit,
                  Unit](Oadmit_i_i_i[A, B, C](sigma, oDE1, u),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](Oadmit_i_i_i[A, B, C](sigma, oDE2, u),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](eq_i_i[Set.set[C]](Set.inf_set[C](Syntax.ODE_dom[A,
                          C](USubst.Osubst[A, C, B](oDE1, sigma)),
                          Syntax.ODE_dom[A,
                            C](USubst.Osubst[A, C, B](oDE2, sigma))),
                          Set.bot_set[C]),
                          ((ac: Unit) => {
                            val (): Unit = ac;
                            Predicate.single[Unit](())
                          }))
                      }))
                  }))
            })))))

  def Padmit_i_i[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](xa: USubst.subst_ext[A, B, C, Unit],
                             xb: Syntax.hp[A, B, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
      Syntax.hp[A, B, C]),
      Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
      Syntax.hp[A, B, C])]((xa, xb)),
      ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C])) =>
        (a match {
          case (_, Syntax.Pvar(_)) => Predicate.single[Unit](())
          case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
        B, C, Unit],
        Syntax.hp[A, B, C]),
        Unit](Predicate.single[(USubst.subst_ext[A, B, C,
        Unit],
        Syntax.hp[A, B, C])]((xa, xb)),
        ((a:
          (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C]))
        =>
          (a match {
            case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Sequence(aa, b)) =>
              Predicate.bind[Unit,
                Unit](Padmit_i_i[A, B, C](sigma, aa),
                ((ab: Unit) =>
                {
                  val (): Unit = ab;
                  Predicate.bind[Unit,
                    Unit](Padmit_i_i[A, B, C](sigma, b),
                    ((ac: Unit) =>
                    {
                      val (): Unit = ac;
                      Predicate.bind[Unit,
                        Unit](Predicate.if_pred(USubst.PUadmit[A, B,
                        C](sigma, b,
                        Static_Semantics.BVP[A, B,
                          C](USubst.Psubst[A, B, C](aa, sigma)))),
                        ((ad: Unit) =>
                        {
                          val (): Unit = ad;
                          Predicate.bind[Unit,
                            Unit](hpsafe_i[A, B, C](USubst.Psubst[A, B, C](aa, sigma)),
                            ((ae: Unit) => {
                              val (): Unit = ae;
                              Predicate.single[Unit](())
                            }))
                        }))
                    }))
                }))
            case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
          Unit],
          Syntax.hp[A, B, C]),
          Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
          Syntax.hp[A, B, C])]((xa, xb)),
          ((a: (USubst.subst_ext[A, B, C, Unit],
            Syntax.hp[A, B, C]))
          =>
            (a match {
              case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.Assign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.DiffAssign(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.EvolveODE(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Choice(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Sequence(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Loop(aa)) =>
                Predicate.bind[Unit,
                  Unit](Padmit_i_i[A, B, C](sigma, aa),
                  ((ab: Unit) =>
                  {
                    val (): Unit = ab;
                    Predicate.bind[Unit,
                      Unit](Predicate.if_pred(USubst.PUadmit[A, B,
                      C](sigma, aa,
                      Static_Semantics.BVP[A, B,
                        C](USubst.Psubst[A, B, C](aa, sigma)))),
                      ((ac: Unit) =>
                      {
                        val (): Unit = ac;
                        Predicate.bind[Unit,
                          Unit](hpsafe_i[A, B, C](USubst.Psubst[A, B, C](aa, sigma)),
                          ((ad: Unit) => {
                            val (): Unit = ad;
                            Predicate.single[Unit](())
                          }))
                      }))
                  }))
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
            Syntax.hp[A, B, C]),
            Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
            Syntax.hp[A, B, C])]((xa, xb)),
            ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C])) =>
              (a match {
                case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.EvolveODE(ode, phi)) =>
                  Predicate.bind[Unit,
                    Unit](Oadmit_i_i_i[A, B,
                    C](sigma, ode, Static_Semantics.BVO[A, C](ode)),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.bind[Unit,
                        Unit](fadmit_i[A, B, C](sigma, phi),
                        ((ab: Unit) =>
                        {
                          val (): Unit = ab;
                          Predicate.bind[Unit,
                            Unit](Predicate.if_pred(USubst.FUadmit[A, B,
                            C](sigma, phi, Static_Semantics.BVO[A, C](ode))),
                            ((ac: Unit) => {
                              val (): Unit = ac;
                              Predicate.single[Unit](())
                            }))
                        }))
                    }))
                case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
              B, C, Unit],
              Syntax.hp[A, B, C]),
              Unit](Predicate.single[(USubst.subst_ext[A, B, C,
              Unit],
              Syntax.hp[A, B, C])]((xa, xb)),
              ((a: (USubst.subst_ext[A, B, C, Unit],
                Syntax.hp[A, B, C]))
              =>
                (a match {
                  case (_, Syntax.Pvar(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Assign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.DiffAssign(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Test(_)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.EvolveODE(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.Choice(aa, b)) =>
                    Predicate.bind[Unit,
                      Unit](Padmit_i_i[A, B, C](sigma, aa),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.bind[Unit,
                          Unit](Padmit_i_i[A, B, C](sigma, b),
                          ((ac: Unit) => {
                            val (): Unit = ac;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Sequence(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Loop(_)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
                Unit],
                Syntax.hp[A, B, C]),
                Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                Syntax.hp[A, B, C])]((xa, xb)),
                ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C]))
                =>
                  (a match {
                    case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Assign(_, theta)) =>
                      Predicate.bind[Unit,
                        Unit](Tadmit_i_i[A, B, C](sigma, theta),
                        ((aa: Unit) => {
                          val (): Unit = aa;
                          Predicate.single[Unit](())
                        }))
                    case (_, Syntax.DiffAssign(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.EvolveODE(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Choice(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Sequence(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.hp[A, B, C]),
                  Unit](Predicate.single[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.hp[A, B, C])]((xa, xb)),
                  ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C])) =>
                    (a match {
                      case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                      case (sigma, Syntax.DiffAssign(_, theta)) =>
                        Predicate.bind[Unit,
                          Unit](Tadmit_i_i[A, B, C](sigma, theta),
                          ((aa: Unit) =>
                          {
                            val (): Unit = aa;
                            Predicate.single[Unit](())
                          }))
                      case (_, Syntax.Test(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
                    Syntax.hp[A, B, C]),
                    Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                    Syntax.hp[A, B, C])]((xa, xb)),
                    ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.hp[A, B, C])) =>
                      (a match {
                        case (_, Syntax.Pvar(_)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Assign(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.DiffAssign(_, _)) => Predicate.bot_pred[Unit]
                        case (sigma, Syntax.Test(phi)) =>
                          Predicate.bind[Unit,
                            Unit](fadmit_i[A, B, C](sigma, phi),
                            ((aa: Unit) =>
                            {
                              val (): Unit = aa;
                              Predicate.single[Unit](())
                            }))
                        case (_, Syntax.EvolveODE(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Choice(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Sequence(_, _)) => Predicate.bot_pred[Unit]
                        case (_, Syntax.Loop(_)) => Predicate.bot_pred[Unit]
                      }))))))))))

  def fadmit_i[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](xa: USubst.subst_ext[A, B, C, Unit],
                             xb: Syntax.formula[A, B, C]):
  Predicate.pred[Unit]
  =
    Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
      Syntax.formula[A, B, C]),
      Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
      Syntax.formula[A, B, C])]((xa, xb)),
      ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.formula[A, B, C])) =>
        (a match {
          case (sigma, Syntax.Geq(theta_1, theta_2)) =>
            Predicate.bind[Unit,
              Unit](Tadmit_i_i[A, B, C](sigma, theta_1),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                Predicate.bind[Unit,
                  Unit](Tadmit_i_i[A, B, C](sigma, theta_2),
                  ((ab: Unit) => {
                    val (): Unit = ab;
                    Predicate.single[Unit](())
                  }))
              }))
          case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
          case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
          case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
        }))),
      Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
        B, C, Unit],
        Syntax.formula[A, B, C]),
        Unit](Predicate.single[(USubst.subst_ext[A, B, C,
        Unit],
        Syntax.formula[A, B, C])]((xa, xb)),
        ((a:
          (USubst.subst_ext[A, B, C, Unit], Syntax.formula[A, B, C]))
        =>
          (a match {
            case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
            case (sigma, Syntax.Prop(p, args)) =>
              Predicate.bind[Unit,
                Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                USubst.Tadmit[A, B, C](sigma, args(i))))),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  Predicate.bind[Unit,
                    Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                    Syntax.dsafe[A, C](USubst.Tsubst[A, C, B](args(i), sigma))))),
                    ((ab: Unit) =>
                    {
                      val (): Unit = ab;
                      Predicate.bind[Option[Syntax.formula[Sum_Type.sum[A, C], B,
                        C]],
                        Unit](eq_i_o[Option[Syntax.formula[Sum_Type.sum[A,
                        C],
                        B, C]]]((USubst.SPredicates[A, B, C,
                        Unit](sigma)).apply(p)),
                        ((ac: Option[Syntax.formula[Sum_Type.sum[A, C], B, C]]) =>
                          (ac match {
                            case None => Predicate.bot_pred[Unit]
                            case Some(pa) =>
                              Predicate.bind[Unit,
                                Unit](NFadmit_i_i[C, A, C,
                                B](((i: C) => USubst.Tsubst[A, C, B](args(i), sigma)), pa),
                                ((ad: Unit) => {
                                  val (): Unit = ad;
                                  Predicate.single[Unit](())
                                }))
                          })))
                    }))
                }))
            case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
            case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
            case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
          }))),
        Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
          Unit],
          Syntax.formula[A, B, C]),
          Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
          Syntax.formula[A, B, C])]((xa, xb)),
          ((a: (USubst.subst_ext[A, B, C, Unit],
            Syntax.formula[A, B, C]))
          =>
            (a match {
              case (_, Syntax.Geq(_, _)) =>
                Predicate.bot_pred[Unit]
              case (sigma, Syntax.Prop(p, args)) =>
                Predicate.bind[Unit,
                  Unit](Predicate.if_pred(HOL.All[C](((i: C) =>
                  USubst.Tadmit[A, B, C](sigma, args(i))))),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    Predicate.bind[Unit,
                      Unit](eq_i_i[Option[Syntax.formula[Sum_Type.sum[A,
                      C],
                      B, C]]]((USubst.SPredicates[A, B, C,
                      Unit](sigma)).apply(p),
                      None),
                      ((ab: Unit) =>
                      {
                        val (): Unit = ab;
                        Predicate.single[Unit](())
                      }))
                  }))
              case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
              case (_, Syntax.And(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Exists(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.Diamond(_, _)) =>
                Predicate.bot_pred[Unit]
              case (_, Syntax.InContext(_, _)) =>
                Predicate.bot_pred[Unit]
            }))),
          Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
            Syntax.formula[A, B, C]),
            Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
            Syntax.formula[A, B, C])]((xa, xb)),
            ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.formula[A, B, C])) =>
              (a match {
                case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                case (sigma, Syntax.Not(phi)) =>
                  Predicate.bind[Unit,
                    Unit](fadmit_i[A, B, C](sigma, phi),
                    ((aa: Unit) =>
                    {
                      val (): Unit = aa;
                      Predicate.single[Unit](())
                    }))
                case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.Diamond(_, _)) => Predicate.bot_pred[Unit]
                case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
              }))),
            Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
              B, C, Unit],
              Syntax.formula[A, B, C]),
              Unit](Predicate.single[(USubst.subst_ext[A, B, C,
              Unit],
              Syntax.formula[A, B, C])]((xa, xb)),
              ((a: (USubst.subst_ext[A, B, C, Unit],
                Syntax.formula[A, B, C]))
              =>
                (a match {
                  case (_, Syntax.Geq(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Prop(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Not(_)) =>
                    Predicate.bot_pred[Unit]
                  case (sigma, Syntax.And(phi, psi)) =>
                    Predicate.bind[Unit,
                      Unit](fadmit_i[A, B, C](sigma, phi),
                      ((aa: Unit) =>
                      {
                        val (): Unit = aa;
                        Predicate.bind[Unit,
                          Unit](fadmit_i[A, B, C](sigma, psi),
                          ((ab: Unit) => {
                            val (): Unit = ab;
                            Predicate.single[Unit](())
                          }))
                      }))
                  case (_, Syntax.Exists(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.Diamond(_, _)) =>
                    Predicate.bot_pred[Unit]
                  case (_, Syntax.InContext(_, _)) =>
                    Predicate.bot_pred[Unit]
                }))),
              Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A, B, C,
                Unit],
                Syntax.formula[A, B, C]),
                Unit](Predicate.single[(USubst.subst_ext[A, B, C, Unit],
                Syntax.formula[A, B, C])]((xa, xb)),
                ((a: (USubst.subst_ext[A, B, C, Unit],
                  Syntax.formula[A, B, C]))
                =>
                  (a match {
                    case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                    case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                    case (sigma, Syntax.Exists(x, phi)) =>
                      Predicate.bind[Unit,
                        Unit](fadmit_i[A, B, C](sigma, phi),
                        ((aa: Unit) =>
                        {
                          val (): Unit = aa;
                          Predicate.bind[Unit,
                            Unit](Predicate.if_pred(USubst.FUadmit[A, B,
                            C](sigma, phi,
                            Set.insert[Sum_Type.sum[C,
                              C]](Sum_Type.Inl[C, C](x),
                              Set.bot_set[Sum_Type.sum[C, C]]))),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              Predicate.single[Unit](())
                            }))
                        }))
                    case (_, Syntax.Diamond(_, _)) =>
                      Predicate.bot_pred[Unit]
                    case (_, Syntax.InContext(_, _)) =>
                      Predicate.bot_pred[Unit]
                  }))),
                Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.formula[A, B, C]),
                  Unit](Predicate.single[(USubst.subst_ext[A,
                  B, C, Unit],
                  Syntax.formula[A, B, C])]((xa, xb)),
                  ((a: (USubst.subst_ext[A, B, C, Unit], Syntax.formula[A, B, C])) =>
                    (a match {
                      case (_, Syntax.Geq(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Prop(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Not(_)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.And(_, _)) => Predicate.bot_pred[Unit]
                      case (_, Syntax.Exists(_, _)) => Predicate.bot_pred[Unit]
                      case (sigma, Syntax.Diamond(aa, phi)) =>
                        Predicate.bind[Unit,
                          Unit](fadmit_i[A, B, C](sigma, phi),
                          ((ab: Unit) =>
                          {
                            val (): Unit = ab;
                            Predicate.bind[Unit,
                              Unit](Padmit_i_i[A, B, C](sigma, aa),
                              ((ac: Unit) =>
                              {
                                val (): Unit = ac;
                                Predicate.bind[Unit,
                                  Unit](Predicate.if_pred(USubst.FUadmit[A, B,
                                  C](sigma, phi,
                                  Static_Semantics.BVP[A, B, C](USubst.Psubst[A, B, C](aa, sigma)))),
                                  ((ad: Unit) =>
                                  {
                                    val (): Unit = ad;
                                    Predicate.bind[Unit,
                                      Unit](hpsafe_i[A, B,
                                      C](USubst.Psubst[A, B, C](aa, sigma)),
                                      ((ae: Unit) =>
                                      {
                                        val (): Unit = ae;
                                        Predicate.single[Unit](())
                                      }))
                                  }))
                              }))
                          }))
                      case (_, Syntax.InContext(_, _)) => Predicate.bot_pred[Unit]
                    }))),
                  Predicate.sup_pred[Unit](Predicate.bind[(USubst.subst_ext[A,
                    B, C, Unit],
                    Syntax.formula[A, B, C]),
                    Unit](Predicate.single[(USubst.subst_ext[A, B, C,
                    Unit],
                    Syntax.formula[A, B, C])]((xa, xb)),
                    ((a: (USubst.subst_ext[A, B, C, Unit],
                      Syntax.formula[A, B, C]))
                    =>
                      (a match {
                        case (_, Syntax.Geq(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Prop(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Not(_)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.And(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Exists(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (_, Syntax.Diamond(_, _)) =>
                          Predicate.bot_pred[Unit]
                        case (sigma, Syntax.InContext(c, phi)) =>
                          Predicate.bind[Unit,
                            Unit](fadmit_i[A, B, C](sigma, phi),
                            ((aa: Unit) =>
                            {
                              val (): Unit = aa;
                              Predicate.bind[Unit,
                                Unit](Predicate.if_pred(USubst.FUadmit[A, B,
                                C](sigma, phi, Set.top_set[Sum_Type.sum[C, C]])),
                                ((ab: Unit) =>
                                {
                                  val (): Unit = ab;
                                  Predicate.bind[Unit,
                                    Unit](fsafe_i[A, B,
                                    C](USubst.Fsubst[A, B, C](phi, sigma)),
                                    ((ac: Unit) =>
                                    {
                                      val (): Unit = ac;
                                      Predicate.bind[Option[Syntax.formula[A, Sum_Type.sum[B, Unit], C]],
                                        Unit](eq_i_o[Option[Syntax.formula[A, Sum_Type.sum[B, Unit],
                                        C]]]((USubst.SContexts[A, B, C, Unit](sigma)).apply(c)),
                                        ((ad: Option[Syntax.formula[A, Sum_Type.sum[B, Unit],
                                          C]])
                                        =>
                                          (ad match {
                                            case None => Predicate.bot_pred[Unit]
                                            case Some(ca) =>
                                              Predicate.bind[Unit,
                                                Unit](PFadmit_i_i[Unit, A, B,
                                                C](((_: Unit) => USubst.Fsubst[A, B, C](phi, sigma)),
                                                ca),
                                                ((ae: Unit) => {
                                                  val (): Unit = ae;
                                                  Predicate.single[Unit](())
                                                }))
                                          })))
                                    }))
                                }))
                            }))
                      }))),
                    Predicate.bind[(USubst.subst_ext[A, B, C, Unit],
                      Syntax.formula[A, B, C]),
                      Unit](Predicate.single[(USubst.subst_ext[A, B, C,
                      Unit],
                      Syntax.formula[A, B, C])]((xa, xb)),
                      ((a: (USubst.subst_ext[A, B, C, Unit],
                        Syntax.formula[A, B, C]))
                      =>
                        (a match {
                          case (_, Syntax.Geq(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Prop(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Not(_)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.And(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Exists(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (_, Syntax.Diamond(_, _)) =>
                            Predicate.bot_pred[Unit]
                          case (sigma, Syntax.InContext(c, phi)) =>
                            Predicate.bind[Unit,
                              Unit](fadmit_i[A, B, C](sigma, phi),
                              ((aa: Unit) =>
                              {
                                val (): Unit = aa;
                                Predicate.bind[Unit,
                                  Unit](Predicate.if_pred(USubst.FUadmit[A, B,
                                  C](sigma, phi, Set.top_set[Sum_Type.sum[C, C]])),
                                  ((ab: Unit) =>
                                  {
                                    val (): Unit = ab;
                                    Predicate.bind[Unit,
                                      Unit](eq_i_i[Option[Syntax.formula[A,
                                      Sum_Type.sum[B, Unit],
                                      C]]]((USubst.SContexts[A, B, C,
                                      Unit](sigma)).apply(c),
                                      None),
                                      ((ac: Unit) =>
                                      {
                                        val (): Unit = ac;
                                        Predicate.single[Unit](())
                                      }))
                                  }))
                              }))
                        })))))))))))

  def ddl_ssafe(sigma: USubst.subst_ext[myvars, myvars, myvars, Unit]): Boolean =
    HOL.All[myvars](((i: myvars) =>
      ((USubst.SFunctions[myvars, myvars, myvars,
        Unit](sigma)).apply(i)
      match {
        case None => true
        case Some(a) =>
          Syntax.dfree[Sum_Type.sum[myvars, myvars], myvars](a)
      }))) &&
      (HOL.All[myvars](((f: myvars) =>
        ((USubst.SPredicates[myvars, myvars, myvars,
          Unit](sigma)).apply(f)
        match {
          case None => true
          case Some(a) =>
            Syntax.fsafe[Sum_Type.sum[myvars, myvars], myvars,
              myvars](a)
        }))) &&
        (HOL.All[myvars](((f: myvars) =>
          ((USubst.SFunls[myvars, myvars, myvars,
            Unit](sigma)).apply(f)
          match {
            case None => true
            case Some(a) => Syntax.dsafe[myvars, myvars](a)
          }))) &&
          (HOL.All[myvars](((f: myvars) =>
            ((USubst.SPrograms[myvars, myvars, myvars,
              Unit](sigma)).apply(f)
            match {
              case None => true
              case Some(a) =>
                Syntax.hpsafe[myvars, myvars, myvars](a)
            }))) &&
            (HOL.All[myvars](((f: myvars) =>
              ((USubst.SODEs[myvars, myvars, myvars,
                Unit](sigma)).apply(f)
              match {
                case None => true
                case Some(a) => Syntax.osafe[myvars, myvars](a)
              }))) &&
              HOL.All[myvars](((c: myvars) =>
                ((USubst.SContexts[myvars, myvars, myvars,
                  Unit](sigma)).apply(c)
                match {
                  case None => true
                  case Some(a) =>
                    Syntax.fsafe[myvars,
                      Sum_Type.sum[myvars, Unit], myvars](a)
                })))))))

  def ddl_Fadmit[A : Enum.enum : HOL.equal, B : Enum.enum : HOL.equal,
  C : Enum.enum : HOL.equal](x1: USubst.subst_ext[A, B, C, Unit],
                             x2: Syntax.formula[A, B, C]):
  Boolean
  =
    Predicate.holds(fadmit_i[A, B, C](x1, x2))

  def ddl_Iaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.And[myvars, myvars,
      myvars](Syntax.Predicational[myvars,
      myvars, myvars](i1()),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.Loop[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x)),
        Syntax.Implies[myvars, myvars,
          myvars](Syntax.Predicational[myvars, myvars, myvars](i1()),
          Syntax.Box[myvars, myvars,
            myvars](Syntax.Pvar[myvars, myvars, myvars](x),
            Syntax.Predicational[myvars, myvars,
              myvars](i1()))))),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.Loop[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x)),
        Syntax.Predicational[myvars, myvars, myvars](i1())))

  def ddl_Kaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars,
      myvars](x),
      Syntax.Implies[myvars, myvars,
        myvars](Syntax.Predicational[myvars, myvars,
        myvars](i1()),
        Syntax.Predicational[myvars, myvars,
          myvars](i2()))),
      Syntax.Implies[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        Syntax.Predicational[myvars, myvars,
          myvars](i1())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](x),
          Syntax.Predicational[myvars, myvars,
            myvars](i2()))))

  def ddl_Sadmit(sigma: USubst.subst_ext[myvars, myvars, myvars, Unit],
                 x1: (List[Syntax.formula[myvars, myvars, myvars]],
                   List[Syntax.formula[myvars, myvars, myvars]])):
  Boolean
  =
    (sigma, x1) match {
      case (sigma, (a, s)) =>
        Lista.list_all[Syntax.formula[myvars, myvars,
          myvars]](((aa:
                     Syntax.formula[myvars, myvars, myvars])
        =>
          ddl_Fadmit[myvars, myvars, myvars](sigma, aa)),
          a) &&
          Lista.list_all[Syntax.formula[myvars, myvars,
            myvars]](((aa:
                       Syntax.formula[myvars, myvars, myvars])
          =>
            ddl_Fadmit[myvars, myvars, myvars](sigma, aa)),
            s)
    }

  def ddl_Radmit(sigma: USubst.subst_ext[myvars, myvars, myvars, Unit],
                 r: (List[(List[Syntax.formula[myvars, myvars, myvars]],
                   List[Syntax.formula[myvars, myvars, myvars]])],
                   (List[Syntax.formula[myvars, myvars, myvars]],
                     List[Syntax.formula[myvars, myvars, myvars]]))):
  Boolean
  =
    Lista.list_all[(List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars,
        myvars]])](((a: (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
    =>
      ddl_Sadmit(sigma, a)),
      Product_Type.fst[List[(List[Syntax.formula[myvars, myvars, myvars]],
        List[Syntax.formula[myvars, myvars,
          myvars]])],
        (List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars,
            myvars]])](r)) &&
      ddl_Sadmit(sigma,
        Product_Type.snd[List[(List[Syntax.formula[myvars, myvars,
          myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](r))

  def ddl_Ssubst(x0: (List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]]),
                 sigma: USubst.subst_ext[myvars, myvars, myvars, Unit]):
  (List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])
  =
    (x0, sigma) match {
      case ((gamma, delta), sigma) =>
        (Lista.map[Syntax.formula[myvars, myvars, myvars],
          Syntax.formula[myvars, myvars,
            myvars]](((phi:
                       Syntax.formula[myvars, myvars, myvars])
        =>
          USubst.Fsubst[myvars, myvars, myvars](phi, sigma)),
          gamma),
          Lista.map[Syntax.formula[myvars, myvars, myvars],
            Syntax.formula[myvars, myvars,
              myvars]](((phi:
                         Syntax.formula[myvars, myvars, myvars])
          =>
            USubst.Fsubst[myvars, myvars, myvars](phi, sigma)),
            delta))
    }

  def ddl_Rsubst(x0: (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]])),
                 sigma: USubst.subst_ext[myvars, myvars, myvars, Unit]):
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (x0, sigma) match {
      case ((sg, c), sigma) =>
        (Lista.map[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]]),
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]])](((phi:
                           (List[Syntax.formula[myvars, myvars, myvars]],
                             List[Syntax.formula[myvars, myvars, myvars]]))
        =>
          ddl_Ssubst(phi, sigma)),
          sg),
          ddl_Ssubst(c, sigma))
    }

  def ddl_Vaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars,
      myvars](x, Syntax.empty[myvars, myvars]),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars,
        myvars](x),
        Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars])))

  def ddl_DCaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.OVar[myvars, myvars](x),
      Syntax.Predicational[myvars, myvars,
        myvars](i2())),
      Syntax.Predicational[myvars, myvars, myvars](i3())),
      Syntax.Equiv[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Predicational[myvars, myvars, myvars](i2())),
        Syntax.Predicational[myvars, myvars,
          myvars](i1())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.EvolveODE[myvars, myvars,
          myvars](Syntax.OVar[myvars, myvars](x),
          Syntax.And[myvars, myvars,
            myvars](Syntax.Predicational[myvars, myvars,
            myvars](i2()),
            Syntax.Predicational[myvars, myvars,
              myvars](i3()))),
          Syntax.Predicational[myvars, myvars,
            myvars](i1()))))
  def ddl_DEaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.OSing[myvars, myvars](x, ddl_f1(i1(), x)),
      ddl_p1(y, x)),
      ddl_P(i1())),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OSing[myvars, myvars](x, ddl_f1(i1(), x)),
        ddl_p1(y, x)),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.DiffAssign[myvars, myvars,
          myvars](x, ddl_f1(i1(), x)),
          ddl_P(i1()))))


  def ddl_DGaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.OSing[myvars, myvars](x, ddl_f1(i1(), x)),
      ddl_p1(x, x)),
      ddl_p1(y, x)),
      Syntax.Exists[myvars, myvars,
        myvars](y, Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.oprod[myvars,
        myvars](Syntax.OSing[myvars,
        myvars](x, ddl_f1(i1(), x)),
        Syntax.OSing[myvars,
          myvars](y, Syntax.Plus[myvars,
          myvars](Syntax.Times[myvars,
          myvars](ddl_f1(i2(), x), Syntax.Var[myvars, myvars](y)),
          ddl_f1(i3(), x)))),
        ddl_p1(x, x)),
        ddl_p1(y, x))))

  def ddl_DSaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.OSing[myvars, myvars](x, ddl_f0(i1())),
      ddl_p1(y, x)),
      ddl_p1(z, x)),
      Syntax.Forall[myvars, myvars,
        myvars](y, Syntax.Implies[myvars, myvars,
        myvars](Syntax.Geq[myvars, myvars,
        myvars](Syntax.Var[myvars, myvars](y),
        Syntax.Const[myvars, myvars](Real.zero_real)),
        Syntax.Implies[myvars, myvars,
          myvars](Syntax.Forall[myvars, myvars,
          myvars](z,
          Syntax.Implies[myvars, myvars,
            myvars](Syntax.And[myvars, myvars,
            myvars](Syntax.Geq[myvars, myvars,
            myvars](Syntax.Var[myvars, myvars](z),
            Syntax.Const[myvars, myvars](Real.zero_real)),
            Syntax.Geq[myvars, myvars,
              myvars](Syntax.Var[myvars, myvars](y),
              Syntax.Var[myvars, myvars](z))),
            Syntax.Prop[myvars, myvars,
              myvars](y, ((a: myvars) =>
              ddl_singleton[myvars](Syntax.Plus[myvars,
                myvars](Syntax.Var[myvars, myvars](x),
                Syntax.Times[myvars,
                  myvars](ddl_f0(i1()),
                  Syntax.Var[myvars, myvars](z))),
                a))))),
          Syntax.Box[myvars, myvars,
            myvars](Syntax.Assign[myvars, myvars,
            myvars](x, Syntax.Plus[myvars,
            myvars](Syntax.Var[myvars, myvars](x),
            Syntax.Times[myvars,
              myvars](ddl_f0(i1()), Syntax.Var[myvars, myvars](y)))),
            ddl_p1(z, x))))))

  def ddl_DWaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.OVar[myvars, myvars](x),
      Syntax.Predicational[myvars, myvars,
        myvars](i2())),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Predicational[myvars, myvars,
          myvars](i2())),
        Syntax.Implies[myvars, myvars,
          myvars](Syntax.Predicational[myvars, myvars,
          myvars](i2()),
          Syntax.Predicational[myvars, myvars,
            myvars](i1()))))
  def ddl_Gaxrule:
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (List((Nil, List(ddl_P(i1())))),
      (Nil, List(Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        ddl_P(i1())))))


  def ddl_CEaxrule:
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (List((Nil, List(Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Predicational[myvars, myvars,
      myvars](i1()),
      Syntax.Predicational[myvars, myvars, myvars](i2()))))),
      (Nil, List(Syntax.Equiv[myvars, myvars,
        myvars](Syntax.InContext[myvars, myvars,
        myvars](i3(),
        Syntax.Predicational[myvars, myvars, myvars](i1())),
        Syntax.InContext[myvars, myvars,
          myvars](i3(),
          Syntax.Predicational[myvars, myvars, myvars](i2()))))))

  def ddl_CQaxrule:
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (List((Nil, List(Syntax.Equals[myvars, myvars,
      myvars](Syntax.Functional[myvars,
      myvars](i1()),
      Syntax.Functional[myvars, myvars](i2()))))),
      (Nil, List(Syntax.Equiv[myvars, myvars,
        myvars](Syntax.Prop[myvars, myvars,
        myvars](z, ((a: myvars) =>
        ddl_singleton[myvars](Syntax.Functional[myvars,
          myvars](i1()),
          a))),
        Syntax.Prop[myvars, myvars,
          myvars](z, ((a: myvars) =>
          ddl_singleton[myvars](Syntax.Functional[myvars,
            myvars](i2()),
            a)))))))

  def ddl_CTaxrule:
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (Nil, (Nil, Nil))

  def ddl_monbrule:
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    (List((List(ddl_P(i1())), List(ddl_P(i2())))),
      (List(Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        ddl_P(i1()))),
        List(Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](x),
          ddl_P(i2())))))

  def ddl_DIGraxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Implies[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars]),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Prop[myvars, myvars,
          myvars](x, Syntax.empty[myvars, myvars])),
        Syntax.Geq[myvars, myvars,
          myvars](Syntax.Differential[myvars, myvars](ddl_f1(i1(), x)),
          Syntax.Differential[myvars, myvars](ddl_f1(i2(), x))))),
      Syntax.Implies[myvars, myvars,
        myvars](Syntax.Implies[myvars, myvars,
        myvars](Syntax.Prop[myvars, myvars,
        myvars](x, Syntax.empty[myvars, myvars]),
        Syntax.Greater[myvars, myvars,
          myvars](ddl_f1(i1(), x), ddl_f1(i2(), x))),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.EvolveODE[myvars, myvars,
          myvars](Syntax.OVar[myvars, myvars](x),
          Syntax.Prop[myvars, myvars,
            myvars](x, Syntax.empty[myvars, myvars])),
          Syntax.Greater[myvars, myvars,
            myvars](ddl_f1(i1(), x), ddl_f1(i2(), x)))))

  def ddl_box_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Diamond[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars, myvars](x),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.Not[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        Syntax.Not[myvars, myvars,
          myvars](Syntax.Predicational[myvars,
          myvars, myvars](i1())))))

  def ddl_EquivReflexiveAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars,
      myvars](x, Syntax.empty[myvars, myvars]),
      Syntax.Prop[myvars, myvars,
        myvars](x, Syntax.empty[myvars, myvars]))

  def ddl_loop_iterate_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Loop[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars, myvars](x)),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Predicational[myvars,
        myvars, myvars](i1()),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](x),
          Syntax.Box[myvars, myvars,
            myvars](Syntax.Loop[myvars, myvars,
            myvars](Syntax.Pvar[myvars, myvars, myvars](x)),
            Syntax.Predicational[myvars, myvars, myvars](i1())))))

  def ddl_AllElimAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Forall[myvars, myvars,
      myvars](x, Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.Predicational[myvars, myvars, myvars](i1()))

  def ddl_dMinusAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Minus[myvars,
      myvars](Syntax.DFunl[myvars, myvars](i1()),
      Syntax.DFunl[myvars, myvars](i2()))),
      Syntax.Minus[myvars,
        myvars](Syntax.Differential[myvars, myvars](Syntax.DFunl[myvars, myvars](i1())),
        Syntax.Differential[myvars,
          myvars](Syntax.DFunl[myvars, myvars](i2()))))

  def ddl_constFcongAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Equals[myvars, myvars,
      myvars](Syntax.Function[myvars, myvars](i1(), Syntax.empty[myvars, myvars]),
      Syntax.Function[myvars, myvars](i2(), Syntax.empty[myvars, myvars])),
      Syntax.Equiv[myvars, myvars,
        myvars](Syntax.Prop[myvars, myvars,
        myvars](x, ((a: myvars) =>
        ddl_singleton[myvars](Syntax.Function[myvars,
          myvars](i1(), Syntax.empty[myvars, myvars]),
          a))),
        Syntax.Prop[myvars, myvars,
          myvars](x, ((a: myvars) =>
          ddl_singleton[myvars](Syntax.Function[myvars,
            myvars](i2(), Syntax.empty[myvars, myvars]),
            a)))))

  def ddl_DiffLinearAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Times[myvars,
      myvars](Syntax.Function[myvars,
      myvars](i2(), Syntax.empty[myvars, myvars]),
      Syntax.DFunl[myvars, myvars](i1()))),
      Syntax.Times[myvars,
        myvars](Syntax.Function[myvars, myvars](i2(), Syntax.empty[myvars, myvars]),
        Syntax.Differential[myvars,
          myvars](Syntax.DFunl[myvars, myvars](i1()))))

  def ddl_diff_var_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Var[myvars, myvars](x)),
      Syntax.DiffVar[myvars, myvars](x))

  def ddl_compose_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Sequence[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars, myvars](x),
      Syntax.Pvar[myvars, myvars, myvars](y)),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars,
        myvars](x),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](y),
          Syntax.Predicational[myvars, myvars, myvars](i1()))))

  def ddl_assignEqAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Assign[myvars, myvars,
      myvars](x, Syntax.Function[myvars,
      myvars](i1(), Syntax.empty[myvars, myvars])),
      ddl_P(i1())),
      Syntax.Forall[myvars, myvars,
        myvars](x, Syntax.Implies[myvars, myvars,
        myvars](Syntax.Equals[myvars, myvars,
        myvars](Syntax.Var[myvars, myvars](x),
        Syntax.Function[myvars,
          myvars](i1(),
          Syntax.empty[myvars, myvars])),
        ddl_P(i1()))))

  def ddl_BoxSplitAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars,
      myvars](x),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Predicational[myvars, myvars, myvars](i1()),
        Syntax.Predicational[myvars, myvars, myvars](i2()))),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        Syntax.Predicational[myvars, myvars, myvars](i1())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](x),
          Syntax.Predicational[myvars, myvars, myvars](i2()))))

  def ddl_choice_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Choice[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars, myvars](x),
      Syntax.Pvar[myvars, myvars, myvars](y)),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        Syntax.Predicational[myvars, myvars, myvars](i1())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](y),
          Syntax.Predicational[myvars, myvars, myvars](i1()))))

  def ddl_allInstAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Forall[myvars, myvars,
      myvars](x, Syntax.Prop[myvars, myvars,
      myvars](x, ((a: myvars) =>
      ddl_singleton[myvars](Syntax.Var[myvars,
        myvars](x),
        a)))),
      Syntax.Prop[myvars, myvars,
        myvars](x, ((a: myvars) =>
        ddl_singleton[myvars](Syntax.Function[myvars,
          myvars](i1(), Syntax.empty[myvars, myvars]),
          a))))

  def ddl_ImpSelfAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Implies[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars]),
      Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars])),
      Syntax.TT[myvars, myvars, myvars])


  def ddl_DiffEffectSysAxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.EvolveODE[myvars, myvars,
      myvars](Syntax.oprod[myvars,
      myvars](Syntax.OSing[myvars, myvars](x, Syntax.DFunl[myvars, myvars](i1())),
      Syntax.OVar[myvars, myvars](x)),
      ddl_P(i2())),
      ddl_P(i1())),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.oprod[myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.OSing[myvars,
          myvars](x, Syntax.DFunl[myvars, myvars](i1()))),
        ddl_P(i2())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.DiffAssign[myvars, myvars,
          myvars](x, Syntax.DFunl[myvars, myvars](i1())),
          ddl_P(i1()))))

  def ddl_diff_assign_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.DiffAssign[myvars, myvars,
      myvars](x, Syntax.Function[myvars,
      myvars](i1(), Syntax.empty[myvars, myvars])),
      Syntax.Prop[myvars, myvars,
        myvars](x, ((a: myvars) =>
        ddl_singleton[myvars](Syntax.DiffVar[myvars,
          myvars](x),
          a)))),
      Syntax.Prop[myvars, myvars,
        myvars](x,
        ((a: myvars) =>
          ddl_singleton[myvars](Syntax.Function[myvars,
            myvars](i1(), Syntax.empty[myvars, myvars]),
            a))))

  def ddl_state_fun(f: myvars): Syntax.trm[myvars, myvars] =
    Syntax.Function[myvars,
      myvars](f, ((a: myvars) => Syntax.Var[myvars, myvars](a)))

  def ddl_diff_times_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Times[myvars,
      myvars](ddl_state_fun(i1()), ddl_state_fun(i2()))),
      Syntax.Plus[myvars,
        myvars](Syntax.Times[myvars,
        myvars](Syntax.Differential[myvars,
        myvars](ddl_state_fun(i1())),
        ddl_state_fun(i2())),
        Syntax.Times[myvars,
          myvars](ddl_state_fun(i1()),
          Syntax.Differential[myvars,
            myvars](ddl_state_fun(i2())))))

  def ddl_diff_const_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Function[myvars,
      myvars](i1(), Syntax.empty[myvars, myvars])),
      Syntax.Const[myvars, myvars](Real.zero_real))

  def ddl_diff_plus_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Plus[myvars,
      myvars](ddl_state_fun(i1()), ddl_state_fun(i2()))),
      Syntax.Plus[myvars,
        myvars](Syntax.Differential[myvars,
        myvars](ddl_state_fun(i1())),
        Syntax.Differential[myvars, myvars](ddl_state_fun(i2()))))

  /*def ddl_diff_var_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equals[myvars, myvars,
      myvars](Syntax.Differential[myvars,
      myvars](Syntax.Var[myvars, myvars](x)),
      Syntax.DiffVar[myvars, myvars](x))
*/
/*  def ddl_choice_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Choice[myvars, myvars,
      myvars](Syntax.Pvar[myvars, myvars, myvars](x),
      Syntax.Pvar[myvars, myvars, myvars](y)),
      Syntax.Predicational[myvars, myvars, myvars](i1())),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.Pvar[myvars, myvars, myvars](x),
        Syntax.Predicational[myvars, myvars, myvars](i1())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Pvar[myvars, myvars, myvars](y),
          Syntax.Predicational[myvars, myvars, myvars](i1()))))
*/
  def ddl_assign_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Assign[myvars, myvars,
      myvars](x, Syntax.Function[myvars,
      myvars](i1(), Syntax.empty[myvars, myvars])),
      Syntax.Prop[myvars, myvars,
        myvars](x, ((a: myvars) =>
        ddl_singleton[myvars](Syntax.Var[myvars,
          myvars](x),
          a)))),
      Syntax.Prop[myvars, myvars,
        myvars](x,
        ((a: myvars) =>
          ddl_singleton[myvars](Syntax.Function[myvars,
            myvars](i1(), Syntax.empty[myvars, myvars]),
            a))))

  def ddl_test_axiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Equiv[myvars, myvars,
      myvars](Syntax.Box[myvars, myvars,
      myvars](Syntax.Test[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars,
      myvars](y, Syntax.empty[myvars, myvars])),
      Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars])),
      Syntax.Implies[myvars, myvars,
        myvars](Syntax.Prop[myvars, myvars, myvars](y, Syntax.empty[myvars, myvars]),
        Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars])))

  def ddl_DIGeqaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Implies[myvars, myvars,
      myvars](Syntax.Predicational[myvars, myvars, myvars](i2()),
      Syntax.And[myvars, myvars,
        myvars](Syntax.Geq[myvars, myvars,
        myvars](Syntax.Functional[myvars, myvars](i1()),
        Syntax.Functional[myvars, myvars](i2())),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.EvolveODE[myvars, myvars,
          myvars](Syntax.OVar[myvars, myvars](x),
          Syntax.Predicational[myvars, myvars,
            myvars](i2())),
          Syntax.Geq[myvars, myvars,
            myvars](Syntax.Differential[myvars,
            myvars](Syntax.Functional[myvars, myvars](i1())),
            Syntax.Differential[myvars,
              myvars](Syntax.Functional[myvars, myvars](i2())))))),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Predicational[myvars, myvars,
          myvars](i2())),
        Syntax.Geq[myvars, myvars,
          myvars](Syntax.Functional[myvars, myvars](i1()),
          Syntax.Functional[myvars, myvars](i2()))))
/*
  def ddl_DIGeqaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Implies[myvars, myvars,
      myvars](Syntax.Predicational[myvars, myvars, myvars](i2()),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Predicational[myvars, myvars, myvars](i2())),
        Syntax.Geq[myvars, myvars,
          myvars](Syntax.Differential[myvars,
          myvars](Syntax.Functional[myvars,
          myvars](i1())),
          Syntax.Differential[myvars,
            myvars](Syntax.Functional[myvars,
            myvars](i2()))))),
      Syntax.Equiv[myvars, myvars,
        myvars](Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Prop[myvars, myvars,
          myvars](x, Syntax.empty[myvars, myvars])),
        Syntax.Geq[myvars, myvars,
          myvars](Syntax.Functional[myvars, myvars](i1()),
          Syntax.Functional[myvars, myvars](i2()))),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.Test[myvars, myvars,
          myvars](Syntax.Prop[myvars, myvars,
          myvars](x, Syntax.empty[myvars, myvars])),
          Syntax.Geq[myvars, myvars,
            myvars](Syntax.Functional[myvars, myvars](i1()),
            Syntax.Functional[myvars, myvars](i2())))))*/
/*
  def ddl_DIGeqaxiom: Syntax.formula[myvars, myvars, myvars] =
    Syntax.Implies[myvars, myvars,
      myvars](Syntax.Implies[myvars, myvars,
      myvars](Syntax.Prop[myvars, myvars, myvars](x, Syntax.empty[myvars, myvars]),
      Syntax.Box[myvars, myvars,
        myvars](Syntax.EvolveODE[myvars, myvars,
        myvars](Syntax.OVar[myvars, myvars](x),
        Syntax.Prop[myvars, myvars,
          myvars](x, Syntax.empty[myvars, myvars])),
        Syntax.Geq[myvars, myvars,
          myvars](Syntax.Differential[myvars, myvars](ddl_f1(i1(), x)),
          Syntax.Differential[myvars, myvars](ddl_f1(i2(), x))))),
      Syntax.Implies[myvars, myvars,
        myvars](Syntax.Implies[myvars, myvars,
        myvars](Syntax.Prop[myvars, myvars,
        myvars](x, Syntax.empty[myvars, myvars]),
        Syntax.Geq[myvars, myvars,
          myvars](ddl_f1(i1(), x), ddl_f1(i2(), x))),
        Syntax.Box[myvars, myvars,
          myvars](Syntax.EvolveODE[myvars, myvars,
          myvars](Syntax.OVar[myvars, myvars](x),
          Syntax.Prop[myvars, myvars,
            myvars](x, Syntax.empty[myvars, myvars])),
          Syntax.Geq[myvars, myvars,
            myvars](ddl_f1(i1(), x), ddl_f1(i2(), x)))))

  */

  def ddl_get_axiom(x0: Proof_Checker.axiom):
  Syntax.formula[myvars, myvars, myvars]
  =
    x0 match {
      case Proof_Checker.AloopIter() => ddl_loop_iterate_axiom
      case Proof_Checker.AI() => ddl_Iaxiom
      case Proof_Checker.Atest() => ddl_test_axiom
      case Proof_Checker.Abox() => ddl_box_axiom
      case Proof_Checker.Achoice() => ddl_choice_axiom
      case Proof_Checker.AK() => ddl_Kaxiom
      case Proof_Checker.AV() => ddl_Vaxiom
      case Proof_Checker.Aassign() => ddl_assign_axiom
      case Proof_Checker.Adassign() => ddl_diff_assign_axiom
      case Proof_Checker.AdConst() => ddl_diff_const_axiom
      case Proof_Checker.AdPlus() => ddl_diff_plus_axiom
      case Proof_Checker.AdMult() => ddl_diff_times_axiom
      case Proof_Checker.Advar() => ddl_diff_var_axiom
      case Proof_Checker.ADW() => ddl_DWaxiom
      case Proof_Checker.ADE() => ddl_DEaxiom
      case Proof_Checker.ADC() => ddl_DCaxiom
      case Proof_Checker.ADS() => ddl_DSaxiom
      case Proof_Checker.ADIGeq() => ddl_DIGeqaxiom
      case Proof_Checker.ADIGr() => ddl_DIGraxiom
      case Proof_Checker.ADG() => ddl_DGaxiom
      case Proof_Checker.AEquivReflexive() => ddl_EquivReflexiveAxiom
      case Proof_Checker.ADiffEffectSys() => ddl_DiffEffectSysAxiom
      case Proof_Checker.AAllElim() => ddl_AllElimAxiom
      case Proof_Checker.ADiffLinear() => ddl_DiffLinearAxiom
      case Proof_Checker.ABoxSplit() => ddl_BoxSplitAxiom
      case Proof_Checker.AImpSelf() => ddl_ImpSelfAxiom
      case Proof_Checker.Acompose() => ddl_compose_axiom
      case Proof_Checker.AconstFcong() => ddl_constFcongAxiom
      case Proof_Checker.AdMinus() => ddl_dMinusAxiom
      case Proof_Checker.AassignEq() => ddl_assignEqAxiom
      case Proof_Checker.AallInst() => ddl_allInstAxiom
    }

  def ddl_get_axrule(x0: Proof_Checker.axRule):
  (List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))
  =
    x0 match {
      case Proof_Checker.CT() => ddl_CTaxrule
      case Proof_Checker.CQ() => ddl_CQaxrule
      case Proof_Checker.CE() => ddl_CEaxrule
      case Proof_Checker.G() => ddl_Gaxrule
      case Proof_Checker.monb() => ddl_monbrule
    }


  var which_subst = 0
  var stepsStarted = 0
  def ddl_pt_result(x0: Proof_Checker.pt[myvars, myvars, myvars]):
  Option[(List[(List[Syntax.formula[myvars, myvars, myvars]],
    List[Syntax.formula[myvars, myvars, myvars]])],
    (List[Syntax.formula[myvars, myvars, myvars]],
      List[Syntax.formula[myvars, myvars, myvars]]))]
  = {
    stepsStarted = stepsStarted + 1
    if(stepsStarted % 25 == 0) println("Step count: " + stepsStarted)
    x0 match {
      case Proof_Checker.FOLRConstant(f) =>
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]))]((Nil, (Nil, List(f))))
      case Proof_Checker.RuleApp(pt, ra, i) =>
        (ddl_pt_result(pt) match {
          case None => fail()
          case Some(res) =>
            (if (Nat.less_eq_nat(Lista.size_list[(List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])].apply(Product_Type.fst[List[(List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])],
              (List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])](res)),
              i))
              fail() else {
              val ress = ddl_rule_result(res, (i, ra))
              ress match {
                case None => ()
                case Some(rule) => if (PRINT_ALL_RESULTS) {
                  println("Rule app result: (" + ra + "): " + ddl_rule_to_string(rule).mkString)
                }
              }
              ress
            }
              )
        })
      case Proof_Checker.AxRule(ar) => {
        val res = ddl_get_axrule(ar)
        if (PRINT_ALL_RESULTS) {
          println("Rule app result:" + ddl_rule_to_string(res).mkString)
        }
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]]))](res)
      }
      case Proof_Checker.PrUSubst(pt, sub) =>
        (ddl_pt_result(pt) match {
          case None => fail()
          case Some(res) =>
            (if ((ddl_ssafe(sub) && ddl_Radmit(sub, res)) || true) {
              val ress = ddl_Rsubst(res, sub)
              if(which_subst == 57) {
                val 2 = 1 + 1
              }
              if (PRINT_ALL_RESULTS) {
                println(s"USubst ($which_subst) result:" + ddl_rule_to_string(ress).mkString)
                which_subst = which_subst + 1
              }
              Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])],
                (List[Syntax.formula[myvars, myvars, myvars]],
                  List[Syntax.formula[myvars, myvars,
                    myvars]]))](ress)
            }
            else
              fail())
        })
      case Proof_Checker.Ax(a) => {
        val res = ddl_get_axiom(a)
        if (PRINT_ALL_RESULTS) {
          println(s"Ax ($a):" + ddl_rule_to_string((Nil, (Nil, List(res)))).mkString)
        }
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars,
              myvars]]))]((Nil,
          (Nil, List(res))))
      }
      case Proof_Checker.FNC(pt, seq, ra) =>
        (ddl_pt_result(pt) match {
          case None => fail()
          case Some(res) => {
            val ress = ddl_fnc(res, seq, ra)
            ress match {
              case Some(ress) => if (PRINT_ALL_RESULTS) {
                println("FNC:" + ddl_rule_to_string(ress).mkString)
              }
              case None => ()
            }
            ress
          }
        })
      case Proof_Checker.Pro(pt1, pt2) =>
        (ddl_pt_result(pt2) match {
          case None => fail()
          case Some(res2) =>
            (if (!(Nat.equal_nat(Nat.one_nat,
              Lista.size_list[(List[Syntax.formula[myvars,
                myvars, myvars]],
                List[Syntax.formula[myvars, myvars,
                  myvars]])].apply(Product_Type.fst[List[(List[Syntax.formula[myvars,
                myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])],
                (List[Syntax.formula[myvars, myvars, myvars]],
                  List[Syntax.formula[myvars, myvars,
                    myvars]])](res2)))))
              fail() else (ddl_pt_result(pt1) match {
              case None => fail()
              case Some(res1) => {
                val res = ddl_pro(res1, res2)
                res match {
                  case Some(ress) => if (PRINT_ALL_RESULTS) {
                    println("Pro:" + ddl_rule_to_string(ress).mkString)
                  }
                  case None => ()
                }
                res
              }
            }))
        })
      case Proof_Checker.Start(f) => {
        val res = ddl_start_proof(f)
        if (PRINT_ALL_RESULTS) {
          println("Start:" + ddl_rule_to_string(res).mkString)
        }
        Some[(List[(List[Syntax.formula[myvars, myvars, myvars]],
          List[Syntax.formula[myvars, myvars, myvars]])],
          (List[Syntax.formula[myvars, myvars, myvars]],
            List[Syntax.formula[myvars, myvars, myvars]]))](res)
      }
      case Proof_Checker.Sub(pt1, pt2, i) =>
        (ddl_pt_result(pt1) match {
          case None => fail()
          case Some(res1) =>
            (if (Nat.less_eq_nat(Lista.size_list[(List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars,
                myvars]])].apply(Product_Type.fst[List[(List[Syntax.formula[myvars,
              myvars, myvars]],
              List[Syntax.formula[myvars, myvars, myvars]])],
              (List[Syntax.formula[myvars, myvars, myvars]],
                List[Syntax.formula[myvars, myvars, myvars]])](res1)),
              i))
              fail() else (ddl_pt_result(pt2) match {
              case None => fail()
              case Some(res2) => {
                if (PRINT_ALL_RESULTS) {
                  println("SubL:" + ddl_rule_to_string(res1).mkString)
                }
                if (PRINT_ALL_RESULTS) {
                  println("SubR:" + ddl_rule_to_string(res2).mkString)
                }
                if (PRINT_ALL_RESULTS) {
                  println("Merge index:" + i)
                }
                val res = ddl_merge_rules(res1, res2, i)
                res match {
                  case Some(ress) => if (PRINT_ALL_RESULTS) {
                    println("Sub:" + ddl_rule_to_string(ress).mkString)
                  }
                  case None => ()
                }
                res

              }
            }))
        })
    }
  }
} /* object Scratch */

object Static_Semantics {

  def BVO[A, B : HOL.equal](x0: Syntax.ODE[A, B]): Set.set[Sum_Type.sum[B, B]] =
    x0 match {
      case Syntax.OVar(c) => Set.top_set[Sum_Type.sum[B, B]]
      case Syntax.OSing(x, theta) =>
        Set.insert[Sum_Type.sum[B, B]](Sum_Type.Inl[B, B](x),
          Set.insert[Sum_Type.sum[B,
            B]](Sum_Type.Inr[B, B](x),
            Set.bot_set[Sum_Type.sum[B, B]]))
      case Syntax.OProd(oDE1, oDE2) =>
        Set.sup_set[Sum_Type.sum[B, B]](BVO[A, B](oDE1), BVO[A, B](oDE2))
    }

  def BVP[A, B, C : HOL.equal](x0: Syntax.hp[A, B, C]):
  Set.set[Sum_Type.sum[C, C]]
  =
    x0 match {
      case Syntax.Pvar(a) => Set.top_set[Sum_Type.sum[C, C]]
      case Syntax.Assign(x, theta) =>
        Set.insert[Sum_Type.sum[C, C]](Sum_Type.Inl[C, C](x),
          Set.bot_set[Sum_Type.sum[C, C]])
      case Syntax.DiffAssign(x, theta) =>
        Set.insert[Sum_Type.sum[C, C]](Sum_Type.Inr[C, C](x),
          Set.bot_set[Sum_Type.sum[C, C]])
      case Syntax.Test(phi) => Set.bot_set[Sum_Type.sum[C, C]]
      case Syntax.EvolveODE(ode, phi) => BVO[A, C](ode)
      case Syntax.Choice(alpha, beta) =>
        Set.sup_set[Sum_Type.sum[C, C]](BVP[A, B, C](alpha), BVP[A, B, C](beta))
      case Syntax.Sequence(alpha, beta) =>
        Set.sup_set[Sum_Type.sum[C, C]](BVP[A, B, C](alpha), BVP[A, B, C](beta))
      case Syntax.Loop(alpha) => BVP[A, B, C](alpha)
    }

  def MBV[A, B, C : Enum.enum : HOL.equal](x0: Syntax.hp[A, B, C]):
  Set.set[Sum_Type.sum[C, C]]
  =
    x0 match {
      case Syntax.Pvar(a) => Set.bot_set[Sum_Type.sum[C, C]]
      case Syntax.Choice(alpha, beta) =>
        Set.inf_set[Sum_Type.sum[C, C]](MBV[A, B, C](alpha), MBV[A, B, C](beta))
      case Syntax.Sequence(alpha, beta) =>
        Set.sup_set[Sum_Type.sum[C, C]](MBV[A, B, C](alpha), MBV[A, B, C](beta))
      case Syntax.Loop(alpha) => Set.bot_set[Sum_Type.sum[C, C]]
      case Syntax.EvolveODE(ode, uu) =>
        Set.sup_set[Sum_Type.sum[C, C]](Set.image[C,
          Sum_Type.sum[C, C]](((a: C) => Sum_Type.Inl[C, C](a)),
          Syntax.ODE_dom[A, C](ode)),
          Set.image[C,
            Sum_Type.sum[C, C]](((a: C) => Sum_Type.Inr[C, C](a)),
            Syntax.ODE_dom[A, C](ode)))
      case Syntax.Assign(v, va) => BVP[A, B, C](Syntax.Assign[C, A, B](v, va))
      case Syntax.DiffAssign(v, va) =>
        BVP[A, B, C](Syntax.DiffAssign[C, A, B](v, va))
      case Syntax.Test(v) => BVP[A, B, C](Syntax.Test[A, B, C](v))
    }

  def primify[A : HOL.equal](x0: Sum_Type.sum[A, A]): Set.set[Sum_Type.sum[A, A]]
  =
    x0 match {
      case Sum_Type.Inl(x) =>
        Set.insert[Sum_Type.sum[A, A]](Sum_Type.Inl[A, A](x),
          Set.insert[Sum_Type.sum[A,
            A]](Sum_Type.Inr[A, A](x),
            Set.bot_set[Sum_Type.sum[A, A]]))
      case Sum_Type.Inr(x) =>
        Set.insert[Sum_Type.sum[A, A]](Sum_Type.Inl[A, A](x),
          Set.insert[Sum_Type.sum[A,
            A]](Sum_Type.Inr[A, A](x),
            Set.bot_set[Sum_Type.sum[A, A]]))
    }

  def FVT[A, B : Enum.enum : HOL.equal](x0: Syntax.trm[A, B]):
  Set.set[Sum_Type.sum[B, B]]
  =
    x0 match {
      case Syntax.Var(x) =>
        Set.insert[Sum_Type.sum[B, B]](Sum_Type.Inl[B, B](x),
          Set.bot_set[Sum_Type.sum[B, B]])
      case Syntax.Const(x) => Set.bot_set[Sum_Type.sum[B, B]]
      case Syntax.Function(f, args) =>
        Complete_Lattices.Sup_set[Sum_Type.sum[B,
          B]](Set.image[B, Set.set[Sum_Type.sum[B,
          B]]](((i: B) => FVT[A, B](args(i))), Set.top_set[B]))
      case Syntax.Functional(f) => Set.top_set[Sum_Type.sum[B, B]]
      case Syntax.Plus(f, g) =>
        Set.sup_set[Sum_Type.sum[B, B]](FVT[A, B](f), FVT[A, B](g))
      case Syntax.Times(f, g) =>
        Set.sup_set[Sum_Type.sum[B, B]](FVT[A, B](f), FVT[A, B](g))
      case Syntax.Differential(f) =>
        Complete_Lattices.Sup_set[Sum_Type.sum[B,
          B]](Set.image[Sum_Type.sum[B, B],
          Set.set[Sum_Type.sum[B,
            B]]](((a: Sum_Type.sum[B, B]) => primify[B](a)), FVT[A, B](f)))
      case Syntax.DiffVar(x) =>
        Set.insert[Sum_Type.sum[B, B]](Sum_Type.Inr[B, B](x),
          Set.bot_set[Sum_Type.sum[B, B]])
    }

  def FVO[A, B : Enum.enum : HOL.equal](x0: Syntax.ODE[A, B]): Set.set[B] = x0
  match {
    case Syntax.OVar(c) => Set.top_set[B]
    case Syntax.OSing(x, theta) =>
      Set.sup_set[B](Set.insert[B](x, Set.bot_set[B]),
        Set.image[B, B](((xa: B) => xa),
          Set.vimage[B,
            Sum_Type.sum[B, B]](((a: B) => Sum_Type.Inl[B, B](a)),
            FVT[A, B](theta))))
    case Syntax.OProd(oDE1, oDE2) =>
      Set.sup_set[B](FVO[A, B](oDE1), FVO[A, B](oDE2))
  }

  def FVP[A, B, C : Enum.enum : HOL.equal](x0: Syntax.hp[A, B, C]):
  Set.set[Sum_Type.sum[C, C]]
  =
    x0 match {
      case Syntax.Pvar(a) => Set.top_set[Sum_Type.sum[C, C]]
      case Syntax.Assign(x, theta) => FVT[A, C](theta)
      case Syntax.DiffAssign(x, theta) => FVT[A, C](theta)
      case Syntax.Test(phi) => FVF[A, B, C](phi)
      case Syntax.EvolveODE(ode, phi) =>
        Set.sup_set[Sum_Type.sum[C, C]](Set.sup_set[Sum_Type.sum[C,
          C]](Set.image[C, Sum_Type.sum[C,
          C]](((a: C) => Sum_Type.Inl[C, C](a)),
          Set.vimage[C, Sum_Type.sum[C,
            C]](((a: C) => Sum_Type.Inl[C, C](a)), BVO[A, C](ode))),
          Set.image[C, Sum_Type.sum[C,
            C]](((a: C) => Sum_Type.Inl[C, C](a)), FVO[A, C](ode))),
          FVF[A, B, C](phi))
      case Syntax.Choice(alpha, beta) =>
        Set.sup_set[Sum_Type.sum[C, C]](FVP[A, B, C](alpha), FVP[A, B, C](beta))
      case Syntax.Sequence(alpha, beta) =>
        Set.sup_set[Sum_Type.sum[C, C]](FVP[A, B, C](alpha),
          Set.minus_set[Sum_Type.sum[C,
            C]](FVP[A, B, C](beta), MBV[A, B, C](alpha)))
      case Syntax.Loop(alpha) => FVP[A, B, C](alpha)
    }
  def FVF[A, B, C : Enum.enum : HOL.equal](x0: Syntax.formula[A, B, C]):
  Set.set[Sum_Type.sum[C, C]]
  =
    x0 match {
      case Syntax.Geq(f, g) =>
        Set.sup_set[Sum_Type.sum[C, C]](FVT[A, C](f), FVT[A, C](g))
      case Syntax.Prop(p, args) =>
        Complete_Lattices.Sup_set[Sum_Type.sum[C,
          C]](Set.image[C, Set.set[Sum_Type.sum[C,
          C]]](((i: C) => FVT[A, C](args(i))), Set.top_set[C]))
      case Syntax.Not(p) => FVF[A, B, C](p)
      case Syntax.And(p, q) =>
        Set.sup_set[Sum_Type.sum[C, C]](FVF[A, B, C](p), FVF[A, B, C](q))
      case Syntax.Exists(x, p) =>
        Set.remove[Sum_Type.sum[C, C]](Sum_Type.Inl[C, C](x), FVF[A, B, C](p))
      case Syntax.Diamond(alpha, p) =>
        Set.sup_set[Sum_Type.sum[C, C]](FVP[A, B, C](alpha),
          Set.minus_set[Sum_Type.sum[C,
            C]](FVF[A, B, C](p), MBV[A, B, C](alpha)))
      case Syntax.InContext(c, p) => Set.top_set[Sum_Type.sum[C, C]]
    }

  def SIGT[A : HOL.equal, B : Enum.enum : HOL.equal](x0: Syntax.trm[A, B]):
  Set.set[A]
  =
    x0 match {
      case Syntax.Var(vara) => Set.bot_set[A]
      case Syntax.Const(r) => Set.bot_set[A]
      case Syntax.Function(vara, f) =>
        Set.sup_set[A](Set.insert[A](vara, Set.bot_set[A]),
          Complete_Lattices.Sup_set[A](Set.image[B,
            Set.set[A]](((i: B) => SIGT[A, B](f(i))), Set.top_set[B])))
      case Syntax.Functional(vara) => Set.insert[A](vara, Set.bot_set[A])
      case Syntax.Plus(t1, t2) => Set.sup_set[A](SIGT[A, B](t1), SIGT[A, B](t2))
      case Syntax.Times(t1, t2) => Set.sup_set[A](SIGT[A, B](t1), SIGT[A, B](t2))
      case Syntax.DiffVar(x) => Set.bot_set[A]
      case Syntax.Differential(t) => SIGT[A, B](t)
    }

  def SIGO[A : Enum.enum : HOL.equal,
  B : Enum.enum : HOL.equal](x0: Syntax.ODE[A, B]):
  Set.set[Sum_Type.sum[A, B]]
  =
    x0 match {
      case Syntax.OVar(c) =>
        Set.insert[Sum_Type.sum[A, B]](Sum_Type.Inr[B, A](c),
          Set.bot_set[Sum_Type.sum[A, B]])
      case Syntax.OSing(x, theta) =>
        Set.image[A, Sum_Type.sum[A, B]](((a: A) => Sum_Type.Inl[A, B](a)),
          SIGT[A, B](theta))
      case Syntax.OProd(oDE1, oDE2) =>
        Set.sup_set[Sum_Type.sum[A, B]](SIGO[A, B](oDE1), SIGO[A, B](oDE2))
    }

  def SIGP[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x0: Syntax.hp[A, B, C]):
  Set.set[Sum_Type.sum[A, Sum_Type.sum[B, C]]]
  =
    x0 match {
      case Syntax.Pvar(vara) =>
        Set.insert[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Sum_Type.Inr[Sum_Type.sum[B, C], A](Sum_Type.Inr[C, B](vara)),
          Set.bot_set[Sum_Type.sum[A, Sum_Type.sum[B, C]]])
      case Syntax.Assign(vara, t) =>
        Set.image[A, Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](((a: A) => Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)), SIGT[A, C](t))
      case Syntax.DiffAssign(vara, t) =>
        Set.image[A, Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](((a: A) => Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)), SIGT[A, C](t))
      case Syntax.Test(p) => SIGF[A, B, C](p)
      case Syntax.EvolveODE(ode, p) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](SIGF[A, B, C](p),
          Set.image[A, Sum_Type.sum[A,
            Sum_Type.sum[B, C]]](((a: A) => Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)),
            Set.vimage[A,
              Sum_Type.sum[A, C]](((a: A) => Sum_Type.Inl[A, C](a)), SIGO[A, C](ode)))),
          Set.image[C, Sum_Type.sum[A, Sum_Type.sum[B,
            C]]](((x: C) =>
            Sum_Type.Inr[Sum_Type.sum[B, C],
              A](Sum_Type.Inr[C, B](x))),
            Set.vimage[C, Sum_Type.sum[A,
              C]](((a: C) => Sum_Type.Inr[C, A](a)), SIGO[A, C](ode))))
      case Syntax.Choice(a, b) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](SIGP[A, B, C](a), SIGP[A, B, C](b))
      case Syntax.Sequence(a, b) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](SIGP[A, B, C](a), SIGP[A, B, C](b))
      case Syntax.Loop(a) => SIGP[A, B, C](a)
    }

  def SIGF[A : Enum.enum : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x0: Syntax.formula[A, B, C]):
  Set.set[Sum_Type.sum[A, Sum_Type.sum[B, C]]]
  =
    x0 match {
      case Syntax.Geq(t1, t2) =>
        Set.image[A, Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](((a: A) => Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)),
          Set.sup_set[A](SIGT[A, C](t1), SIGT[A, C](t2)))
      case Syntax.Prop(vara, args) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Set.insert[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Sum_Type.Inr[Sum_Type.sum[B, C], A](Sum_Type.Inr[C, B](vara)),
          Set.bot_set[Sum_Type.sum[A, Sum_Type.sum[B, C]]]),
          Set.image[A, Sum_Type.sum[A, Sum_Type.sum[B,
            C]]](((a: A) => Sum_Type.Inl[A, Sum_Type.sum[B, C]](a)),
            Complete_Lattices.Sup_set[A](Set.image[C,
              Set.set[A]](((i: C) => SIGT[A, C](args(i))),
              Set.top_set[C]))))
      case Syntax.Not(p) => SIGF[A, B, C](p)
      case Syntax.And(p1, p2) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](SIGF[A, B, C](p1), SIGF[A, B, C](p2))
      case Syntax.Exists(vara, p) => SIGF[A, B, C](p)
      case Syntax.Diamond(a, p) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](SIGP[A, B, C](a), SIGF[A, B, C](p))
      case Syntax.InContext(vara, p) =>
        Set.sup_set[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Set.insert[Sum_Type.sum[A, Sum_Type.sum[B,
          C]]](Sum_Type.Inr[Sum_Type.sum[B, C], A](Sum_Type.Inl[B, C](vara)),
          Set.bot_set[Sum_Type.sum[A, Sum_Type.sum[B, C]]]),
          SIGF[A, B, C](p))
    }


  def FVSeq[A, B,
  C : Enum.enum : HOL.equal](x0:
                             (List[Syntax.formula[A, B, C]], List[Syntax.formula[A, B, C]])):
  Set.set[Sum_Type.sum[C, C]]
  =
    x0 match {
      case (a, s) =>
        Lista.foldl[Set.set[Sum_Type.sum[C, C]],
          Syntax.formula[A, B,
            C]](((acc: Set.set[Sum_Type.sum[C, C]]) =>
          (x: Syntax.formula[A, B, C]) =>
            Set.sup_set[Sum_Type.sum[C,
              C]](acc, FVF[A, B, C](x))),
          Set.bot_set[Sum_Type.sum[C, C]], a ++ s)
    }

} /* object Static_Semantics */

object Syntax {

  abstract sealed class trm[A, B]
  final case class Var[B, A](a: B) extends trm[A, B]
  final case class Const[A, B](a: Real.real) extends trm[A, B]
  {
    override def toString():String = {
      val Real.Ratreal(Rat.Frct((Int.int_of_integer(n),Int.int_of_integer(d)))) = a
      if(d.intValue() == 1) {
        n.toString
      } else {
        n.toString + "/" + d.toString
      }
    }
  }
  final case class Function[A, B](a: A, b: B => trm[A, B]) extends trm[A, B]
  final case class Functional[A, B](a: A) extends trm[A, B]
  final case class Plus[A, B](a: trm[A, B], b: trm[A, B]) extends trm[A, B]
  final case class Times[A, B](a: trm[A, B], b: trm[A, B]) extends trm[A, B]
  final case class DiffVar[B, A](a: B) extends trm[A, B]
  final case class Differential[A, B](a: trm[A, B]) extends trm[A, B]

  def equal_trma[A : HOL.equal,
  B : Enum.enum : HOL.equal](x0: trm[A, B], x1: trm[A, B]):
  Boolean
  =
    (x0, x1) match {
      case (DiffVar(x7), Differential(x8)) => false
      case (Differential(x8), DiffVar(x7)) => false
      case (Times(x61, x62), Differential(x8)) => false
      case (Differential(x8), Times(x61, x62)) => false
      case (Times(x61, x62), DiffVar(x7)) => false
      case (DiffVar(x7), Times(x61, x62)) => false
      case (Plus(x51, x52), Differential(x8)) => false
      case (Differential(x8), Plus(x51, x52)) => false
      case (Plus(x51, x52), DiffVar(x7)) => false
      case (DiffVar(x7), Plus(x51, x52)) => false
      case (Plus(x51, x52), Times(x61, x62)) => false
      case (Times(x61, x62), Plus(x51, x52)) => false
      case (Functional(x4), Differential(x8)) => false
      case (Differential(x8), Functional(x4)) => false
      case (Functional(x4), DiffVar(x7)) => false
      case (DiffVar(x7), Functional(x4)) => false
      case (Functional(x4), Times(x61, x62)) => false
      case (Times(x61, x62), Functional(x4)) => false
      case (Functional(x4), Plus(x51, x52)) => false
      case (Plus(x51, x52), Functional(x4)) => false
      case (Function(x31, x32), Differential(x8)) => false
      case (Differential(x8), Function(x31, x32)) => false
      case (Function(x31, x32), DiffVar(x7)) => false
      case (DiffVar(x7), Function(x31, x32)) => false
      case (Function(x31, x32), Times(x61, x62)) => false
      case (Times(x61, x62), Function(x31, x32)) => false
      case (Function(x31, x32), Plus(x51, x52)) => false
      case (Plus(x51, x52), Function(x31, x32)) => false
      case (Function(x31, x32), Functional(x4)) => false
      case (Functional(x4), Function(x31, x32)) => false
      case (Const(x2), Differential(x8)) => false
      case (Differential(x8), Const(x2)) => false
      case (Const(x2), DiffVar(x7)) => false
      case (DiffVar(x7), Const(x2)) => false
      case (Const(x2), Times(x61, x62)) => false
      case (Times(x61, x62), Const(x2)) => false
      case (Const(x2), Plus(x51, x52)) => false
      case (Plus(x51, x52), Const(x2)) => false
      case (Const(x2), Functional(x4)) => false
      case (Functional(x4), Const(x2)) => false
      case (Const(x2), Function(x31, x32)) => false
      case (Function(x31, x32), Const(x2)) => false
      case (Var(x1), Differential(x8)) => false
      case (Differential(x8), Var(x1)) => false
      case (Var(x1), DiffVar(x7)) => false
      case (DiffVar(x7), Var(x1)) => false
      case (Var(x1), Times(x61, x62)) => false
      case (Times(x61, x62), Var(x1)) => false
      case (Var(x1), Plus(x51, x52)) => false
      case (Plus(x51, x52), Var(x1)) => false
      case (Var(x1), Functional(x4)) => false
      case (Functional(x4), Var(x1)) => false
      case (Var(x1), Function(x31, x32)) => false
      case (Function(x31, x32), Var(x1)) => false
      case (Var(x1), Const(x2)) => false
      case (Const(x2), Var(x1)) => false
      case (Differential(x8), Differential(y8)) => equal_trma[A, B](x8, y8)
      case (DiffVar(x7), DiffVar(y7)) => HOL.eq[B](x7, y7)
      case (Times(x61, x62), Times(y61, y62)) =>
        equal_trma[A, B](x61, y61) && equal_trma[A, B](x62, y62)
      case (Plus(x51, x52), Plus(y51, y52)) =>
        equal_trma[A, B](x51, y51) && equal_trma[A, B](x52, y52)
      case (Functional(x4), Functional(y4)) => HOL.eq[A](x4, y4)
      case (Function(x31, x32), Function(y31, y32)) =>
        HOL.eq[A](x31, y31) && HOL.eq[B => trm[A, B]](x32, y32)
      case (Const(x2), Const(y2)) => Real.equal_real(x2, y2)
      case (Var(x1), Var(y1)) => HOL.eq[B](x1, y1)
    }

  abstract sealed class ODE[A, B]
  final case class OVar[B, A](a: B) extends ODE[A, B]
  final case class OSing[B, A](a: B, b: trm[A, B]) extends ODE[A, B]
  final case class OProd[A, B](a: ODE[A, B], b: ODE[A, B]) extends ODE[A, B]

  def equal_ODE[A : HOL.equal,
  B : Enum.enum : HOL.equal](x0: ODE[A, B], x1: ODE[A, B]):
  Boolean
  =
    (x0, x1) match {
      case (OSing(x21, x22), OProd(x31, x32)) => false
      case (OProd(x31, x32), OSing(x21, x22)) => false
      case (OVar(x1), OProd(x31, x32)) => false
      case (OProd(x31, x32), OVar(x1)) => false
      case (OVar(x1), OSing(x21, x22)) => false
      case (OSing(x21, x22), OVar(x1)) => false
      case (OProd(x31, x32), OProd(y31, y32)) =>
        equal_ODE[A, B](x31, y31) && equal_ODE[A, B](x32, y32)
      case (OSing(x21, x22), OSing(y21, y22)) =>
        HOL.eq[B](x21, y21) && equal_trma[A, B](x22, y22)
      case (OVar(x1), OVar(y1)) => HOL.eq[B](x1, y1)
    }

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

  def equal_hp[A : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x0: hp[A, B, C], x1: hp[A, B, C]):
  Boolean
  =
    (x0, x1) match {
      case (Sequence(x71, x72), Loop(x8)) => false
      case (Loop(x8), Sequence(x71, x72)) => false
      case (Choice(x61, x62), Loop(x8)) => false
      case (Loop(x8), Choice(x61, x62)) => false
      case (Choice(x61, x62), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), Choice(x61, x62)) => false
      case (EvolveODE(x51, x52), Loop(x8)) => false
      case (Loop(x8), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), Choice(x61, x62)) => false
      case (Choice(x61, x62), EvolveODE(x51, x52)) => false
      case (Test(x4), Loop(x8)) => false
      case (Loop(x8), Test(x4)) => false
      case (Test(x4), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), Test(x4)) => false
      case (Test(x4), Choice(x61, x62)) => false
      case (Choice(x61, x62), Test(x4)) => false
      case (Test(x4), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), Test(x4)) => false
      case (DiffAssign(x31, x32), Loop(x8)) => false
      case (Loop(x8), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), Choice(x61, x62)) => false
      case (Choice(x61, x62), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), Test(x4)) => false
      case (Test(x4), DiffAssign(x31, x32)) => false
      case (Assign(x21, x22), Loop(x8)) => false
      case (Loop(x8), Assign(x21, x22)) => false
      case (Assign(x21, x22), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), Assign(x21, x22)) => false
      case (Assign(x21, x22), Choice(x61, x62)) => false
      case (Choice(x61, x62), Assign(x21, x22)) => false
      case (Assign(x21, x22), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), Assign(x21, x22)) => false
      case (Assign(x21, x22), Test(x4)) => false
      case (Test(x4), Assign(x21, x22)) => false
      case (Assign(x21, x22), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), Assign(x21, x22)) => false
      case (Pvar(x1), Loop(x8)) => false
      case (Loop(x8), Pvar(x1)) => false
      case (Pvar(x1), Sequence(x71, x72)) => false
      case (Sequence(x71, x72), Pvar(x1)) => false
      case (Pvar(x1), Choice(x61, x62)) => false
      case (Choice(x61, x62), Pvar(x1)) => false
      case (Pvar(x1), EvolveODE(x51, x52)) => false
      case (EvolveODE(x51, x52), Pvar(x1)) => false
      case (Pvar(x1), Test(x4)) => false
      case (Test(x4), Pvar(x1)) => false
      case (Pvar(x1), DiffAssign(x31, x32)) => false
      case (DiffAssign(x31, x32), Pvar(x1)) => false
      case (Pvar(x1), Assign(x21, x22)) => false
      case (Assign(x21, x22), Pvar(x1)) => false
      case (Loop(x8), Loop(y8)) => equal_hp[A, B, C](x8, y8)
      case (Sequence(x71, x72), Sequence(y71, y72)) =>
        equal_hp[A, B, C](x71, y71) && equal_hp[A, B, C](x72, y72)
      case (Choice(x61, x62), Choice(y61, y62)) =>
        equal_hp[A, B, C](x61, y61) && equal_hp[A, B, C](x62, y62)
      case (EvolveODE(x51, x52), EvolveODE(y51, y52)) =>
        equal_ODE[A, C](x51, y51) && equal_formulaa[A, B, C](x52, y52)
      case (Test(x4), Test(y4)) => equal_formulaa[A, B, C](x4, y4)
      case (DiffAssign(x31, x32), DiffAssign(y31, y32)) =>
        HOL.eq[C](x31, y31) && equal_trma[A, C](x32, y32)
      case (Assign(x21, x22), Assign(y21, y22)) =>
        HOL.eq[C](x21, y21) && equal_trma[A, C](x22, y22)
      case (Pvar(x1), Pvar(y1)) => HOL.eq[C](x1, y1)
    }

  def equal_formulaa[A : HOL.equal, B : HOL.equal,
  C : Enum.enum : HOL.equal](x0: formula[A, B, C],
                             x1: formula[A, B, C]):
  Boolean
  =
    (x0, x1) match {
      case (Diamond(x61, x62), InContext(x71, x72)) => false
      case (InContext(x71, x72), Diamond(x61, x62)) => false
      case (Exists(x51, x52), InContext(x71, x72)) => false
      case (InContext(x71, x72), Exists(x51, x52)) => false
      case (Exists(x51, x52), Diamond(x61, x62)) => false
      case (Diamond(x61, x62), Exists(x51, x52)) => false
      case (And(x41, x42), InContext(x71, x72)) => false
      case (InContext(x71, x72), And(x41, x42)) => false
      case (And(x41, x42), Diamond(x61, x62)) => false
      case (Diamond(x61, x62), And(x41, x42)) => false
      case (And(x41, x42), Exists(x51, x52)) => false
      case (Exists(x51, x52), And(x41, x42)) => false
      case (Not(x3), InContext(x71, x72)) => false
      case (InContext(x71, x72), Not(x3)) => false
      case (Not(x3), Diamond(x61, x62)) => false
      case (Diamond(x61, x62), Not(x3)) => false
      case (Not(x3), Exists(x51, x52)) => false
      case (Exists(x51, x52), Not(x3)) => false
      case (Not(x3), And(x41, x42)) => false
      case (And(x41, x42), Not(x3)) => false
      case (Prop(x21, x22), InContext(x71, x72)) => false
      case (InContext(x71, x72), Prop(x21, x22)) => false
      case (Prop(x21, x22), Diamond(x61, x62)) => false
      case (Diamond(x61, x62), Prop(x21, x22)) => false
      case (Prop(x21, x22), Exists(x51, x52)) => false
      case (Exists(x51, x52), Prop(x21, x22)) => false
      case (Prop(x21, x22), And(x41, x42)) => false
      case (And(x41, x42), Prop(x21, x22)) => false
      case (Prop(x21, x22), Not(x3)) => false
      case (Not(x3), Prop(x21, x22)) => false
      case (Geq(x11, x12), InContext(x71, x72)) => false
      case (InContext(x71, x72), Geq(x11, x12)) => false
      case (Geq(x11, x12), Diamond(x61, x62)) => false
      case (Diamond(x61, x62), Geq(x11, x12)) => false
      case (Geq(x11, x12), Exists(x51, x52)) => false
      case (Exists(x51, x52), Geq(x11, x12)) => false
      case (Geq(x11, x12), And(x41, x42)) => false
      case (And(x41, x42), Geq(x11, x12)) => false
      case (Geq(x11, x12), Not(x3)) => false
      case (Not(x3), Geq(x11, x12)) => false
      case (Geq(x11, x12), Prop(x21, x22)) => false
      case (Prop(x21, x22), Geq(x11, x12)) => false
      case (InContext(x71, x72), InContext(y71, y72)) =>
        HOL.eq[B](x71, y71) && equal_formulaa[A, B, C](x72, y72)
      case (Diamond(x61, x62), Diamond(y61, y62)) =>
        equal_hp[A, B, C](x61, y61) && equal_formulaa[A, B, C](x62, y62)
      case (Exists(x51, x52), Exists(y51, y52)) =>
        HOL.eq[C](x51, y51) && equal_formulaa[A, B, C](x52, y52)
      case (And(x41, x42), And(y41, y42)) =>
        equal_formulaa[A, B, C](x41, y41) && equal_formulaa[A, B, C](x42, y42)
      case (Not(x3), Not(y3)) => equal_formulaa[A, B, C](x3, y3)
      case (Prop(x21, x22), Prop(y21, y22)) =>
        HOL.eq[C](x21, y21) && HOL.eq[C => trm[A, C]](x22, y22)
      case (Geq(x11, x12), Geq(y11, y12)) =>
        equal_trma[A, C](x11, y11) && equal_trma[A, C](x12, y12)
    }

  def Or[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C] =
    Not[A, B, C](And[A, B, C](Not[A, B, C](p), Not[A, B, C](q)))

  def TT[A, B, C]: formula[A, B, C] =
    Geq[A, C, B](Const[A, C](Real.zero_real), Const[A, C](Real.zero_real))

  def Box[A, B, C](alpha: hp[A, B, C], p: formula[A, B, C]): formula[A, B, C] =
    Not[A, B, C](Diamond[A, B, C](alpha, Not[A, B, C](p)))

  def DFunl[A, B](fid: A): trm[A, B] =
    Function[A, B](fid, ((a: B) => Var[B, A](a)))

  def Equiv[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C] =
    Or[A, B,
      C](And[A, B, C](p, q), And[A, B, C](Not[A, B, C](p), Not[A, B, C](q)))

  def Minus[A, B](theta_1: trm[A, B], theta_2: trm[A, B]): trm[A, B] =
    Plus[A, B](theta_1,
      Times[A, B](theta_2,
        Const[A, B](Real.uminus_real(Real.one_real))))

  def dfree[A, B : Enum.enum](x1: trm[A, B]): Boolean =
    Predicate.holds(Scratch.dfree_i[A, B](x1))

  def dsafe[A, B : Enum.enum](x1: trm[A, B]): Boolean =
    Predicate.holds(Scratch.dsafe_i[A, B](x1))

  def fsafe[A, B, C : Enum.enum : HOL.equal](x1: formula[A, B, C]): Boolean =
    Predicate.holds(Scratch.fsafe_i[A, B, C](x1))

  def oprod[A, B](x0: ODE[A, B], oDE2: ODE[A, B]): ODE[A, B] = (x0, oDE2) match {
    case (OSing(x, t), oDE2) => OProd[A, B](OSing[B, A](x, t), oDE2)
    case (OVar(c), oDE2) => OProd[A, B](OVar[B, A](c), oDE2)
    case (OProd(ll, lr), oDE2) => oprod[A, B](ll, oprod[A, B](lr, oDE2))
  }

  def osafe[A, B : Enum.enum : HOL.equal](x1: ODE[A, B]): Boolean =
    Predicate.holds(Scratch.osafe_i[A, B](x1))

  def Equals[A, B, C](thetaa: trm[A, B], theta: trm[A, B]): formula[A, C, B] =
    And[A, C, B](Geq[A, B, C](thetaa, theta), Geq[A, B, C](theta, thetaa))

  def Forall[A, B, C](x: A, p: formula[B, C, A]): formula[B, C, A] =
    Not[B, C, A](Exists[A, B, C](x, Not[B, C, A](p)))

  def hpsafe[A, B, C : Enum.enum : HOL.equal](x1: hp[A, B, C]): Boolean =
    Predicate.holds(Scratch.hpsafe_i[A, B, C](x1))

  def Greater[A, B, C](thetaa: trm[A, B], theta: trm[A, B]): formula[A, C, B] =
    And[A, C,
      B](Geq[A, B, C](thetaa, theta),
      Not[A, C, B](Geq[A, B, C](theta, thetaa)))

  def Implies[A, B, C](p: formula[A, B, C], q: formula[A, B, C]): formula[A, B, C]
  =
    Or[A, B, C](q, Not[A, B, C](p))

  def ODE_dom[A, B : HOL.equal](x0: ODE[A, B]): Set.set[B] = x0 match {
    case OVar(c) => Set.bot_set[B]
    case OSing(x, theta) => Set.insert[B](x, Set.bot_set[B])
    case OProd(oDE1, oDE2) =>
      Set.sup_set[B](ODE_dom[A, B](oDE1), ODE_dom[A, B](oDE2))
  }

  def empty[A, B]: A => trm[B, A] = ((_: A) => Const[B, A](Real.zero_real))

  def Predicational[A, B, C](p: A): formula[B, A, C] =
    InContext[A, B,
      C](p, Geq[B, C,
      A](Const[B, C](Real.zero_real),
      Const[B, C](Real.zero_real)))

} /* object Syntax */
object ProofTerm {
  import Real._
  import Rat._
  import Int._
  import Proof_Checker._
  import Syntax._
  import Nat._
  import USubst._
  import Scratch._
  import Sum_Type._
  val z:trm[myvars,myvars] = Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))
  val e:(myvars => trm[myvars,myvars]) = {case i1() => z case i2() => z case i3() => z case i4() => z case i5() => z case i6() => z case i7() => z case i8() => z case i9() => z case i10() => z case i11() => z}
  val zst:trm[sum[myvars,myvars],myvars] = Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))
  val est:(myvars => trm[sum[myvars,myvars],myvars]) = {case i1() => zst case i2() => zst case i3() => zst case i4() => zst case i5() => zst case i6() => zst case i7() => zst case i8() => zst case i9() => zst case i10() => zst case i11() => zst}
  def ns[T]:(myvars => Option[T]) =   {case i1() => None case i2() => None case i3() => None case i4() => None case i5() => None case i6() => None case i7() => None case i8() => None case i9() => None case i10() => None case i11() => None}
  def s(t:trm[myvars,myvars]):(myvars =>trm[myvars,myvars]) = {case i1() => t case i2() => z case i3() => z case i4() => z case i5() => z case i6() => z case i7() => z case i8() => z case i9() => z case i10() => z case i11() => z}
  def sst(t:trm[sum[myvars,myvars],myvars]):(myvars =>trm[sum[myvars,myvars],myvars]) = {case i1() => t case i2() => zst case i3() => zst case i4() => zst case i5() => zst case i6() => zst case i7() => zst case i8() => zst case i9() => zst case i10() => zst case i11() => zst}
  val i1mv:myvars = i1()
  val i2mv:myvars = i2()
  val i3mv:myvars = i3()
  val i4mv:myvars = i4()
  val i5mv:myvars = i5()
  val i6mv:myvars = i6()
  val i7mv:myvars = i7()
  val i8mv:myvars = i8()
  val i9mv:myvars = i9()
  val i10mv:myvars = i10()
  val i11mv:myvars = i11()
  val fancyStr = ""
  val proofTerm:pt[myvars,myvars,myvars] = ???

}

object Parser {

  import pt.Int._
  import pt.Nat._
  import pt.Rat._
  import pt.Real._
  import pt.Proof_Checker._
  import pt.Sum_Type._
  import pt.Syntax._
  import pt.Scratch._

  type myvars = pt.Scratch.myvars

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
    ("i11",i11()),
    ("i12",i12()),
    ("i13",i13()),
    ("i14",i14()),
    ("i15",i15()),
    ("i16",i16()),
    ("i17",i17()),
    ("i18",i18()),
    ("i19",i19()),
    ("i20",i20())
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
    (i11(),10),
    (i12(),11),
    (i13(),12),
    (i14(),13),
    (i15(),14),
    (i16(),15),
    (i17(),16),
    (i18(),17),
    (i19(),18),
    (i20(),19)

  )

  @inline
  val mv:Parse[myvars] = {(str,i) =>
    val (ident,j) = alphanum(str,i)
    //println("The id is:" + ident)
    if (ident == "") {{
      val 2 = 1 + 1
      ???
    }}
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
        case "BRenameL" =>
          val i3 = eatChar(str, i2, ' ')
          val (w,i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = mv(str,i5)
          (BRenameL(w,r),i6)
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
        case "BRenameR" =>
          val i3 = eatChar(str, i2, ' ')
          val (w,i4) = mv(str,i3)
          val i5 = eatChar(str,i4,' ')
          val (r,i6) = mv(str,i5)
          (BRenameR(w,r),i6)

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
object GeneratedProofChecker {
  import Real._
  import Rat._
 import Int._
  import Proof_Checker._
  import Syntax._
  import Nat._
  import USubst._
  import Scratch._
  import Sum_Type._
  def main(input : Array[String]) = {
    val path = if(input.isEmpty) {"/usr0/home/bbohrer/KeYmaeraX/velocityCar-defun.pt"  /*"/usr0/home/bbohrer/KeYmaeraX/velocityCar.pt"*/}  else input(0) //e.g. "/usr0/home/bbohrer/KeYmaeraX/velocityCar.pt"
    val str = Source.fromFile(path).mkString
    val start = System.currentTimeMillis()
    val (term,_) = Parser.proofTerm(str,0)
    val mid = System.currentTimeMillis()
    println("Parsing time taken(seconds): "+ (mid-start)/1000.0)

    //    val res =
    val res = ddl_pt_result(term)
    //    val res = Predicate.eval(pred)
    val end = System.currentTimeMillis()
    println(res)
    println("Proof time elapsed (s):" + (end-mid)/1000.0)
  }}

