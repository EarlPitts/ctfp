import cats._
import cats.implicits._

case class Writer[W, A](runWriter: (W, A))

object Writer:
  given [W: Monoid]: Monad[[X] =>> Writer[W, X]] with
    def tailRecM[A, B](a: A)(f: A => Writer[W, Either[A, B]]): Writer[W, B] =
      ???

    def pure[A](a: A): Writer[W, A] = Writer((Monoid[W].empty, a))
    def flatMap[A, B](fa: Writer[W, A])(f: A => Writer[W, B]): Writer[W, B] =
      fa match
        case Writer((w1, a)) =>
          f(a) match
            case Writer((w2, b)) => Writer((w1.combine(w2), b))

def negate(b: Boolean): Writer[String, Boolean] = Writer(("Not so! ", !b))

// We separated concerns: the negate function can focus on negating,
// and the monad instance carries the logic for aggregating the logs

val negThrice = for
  a <- negate(true)
  b <- negate(a)
  c <- negate(b)
yield c

def negate2(b: Boolean): Writer[List[String], Boolean] = Writer(
  (List("Not so!"), !b)
)

val negThrice2 = for
  a <- negate2(true)
  b <- negate2(a)
  c <- negate2(b)
yield c

negThrice2.runWriter

import cats.data.Writer as W

def neg(b: Boolean): W[String, Boolean] =
  W.tell("Not so!") >> W.value(!b)

neg(true).flatMap(neg(_)).run

def toUpper(s: String): W[List[String], String] =
  W.tell(List("called toUpper"))
    >> W.value(s.map(_.toUpper))

def toWords(s: String): W[List[String], List[String]] =
  W.tell(List("called toWords"))
    >> W.value(s.split(" ").toList)

toUpper("foo bar baz").flatMap(toWords(_)).run

// Kleisli is about composing effectful functions

def normalNeg(b: Boolean) = !b

// Applicative style and point-free style
normalNeg(normalNeg(true))
(normalNeg compose normalNeg)(true)

// Applicative style with flatMap (>>=)
(toUpper("foo bar baz") >>= toWords).run

// Point-free style with Kleisli fish
val composite = toUpper >=> toWords

composite("foo bar baz").run

// Challenges
enum Maybe[+A]:
  case Nothing
  case Just(a: A)
import Maybe.*

object Maybe:
  given Monad[Maybe] with
    def tailRecM[A, B](a: A)(f: A => Maybe[Either[A, B]]): Maybe[B] = ???

    def pure[A](x: A): Maybe[A] = Just(x)
    def flatMap[A, B](fa: Maybe[A])(f: A => Maybe[B]): Maybe[B] = fa match
      case Nothing => Nothing
      case Just(a) => f(a)

def safeReciprocal(n: Double): Maybe[Double] =
  if (n == 0) then Nothing else Just(1/n)

def safeRoot(n: Double): Maybe[Double] =
  if n >= 0 then Just(Math.sqrt(n)) else Nothing

val safeRootReciprocal: Double => Maybe[Double] =
  safeReciprocal >=> safeRoot

safeRootReciprocal(12)

// Another example
case class User(age: Int, name: String)

object User:
  def mkUser(age: Int, name: String): Maybe[User] = for
    age <- verifyAge(age)
    name <- verifyName(name)
  yield User(age, name)

  def verifyAge(age: Int): Maybe[Int] =
    if age >= 18 then Just(age) else Nothing

  def verifyName(name: String): Maybe[String] =
    if name.length < 100 then Just(name) else Nothing
