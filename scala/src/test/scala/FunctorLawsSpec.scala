import cats.*
import cats.derived.*
import cats.implicits.*
import cats.laws.*
import cats.laws.discipline.*
import org.scalacheck.*
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.Configuration
import org.typelevel.discipline.scalatest.FunSuiteDiscipline

val arbInt: Arbitrary[Int] = implicitly[Arbitrary[Int]]
val arbString: Arbitrary[String] = implicitly[Arbitrary[String]]
val arbDouble: Arbitrary[Double] = implicitly[Arbitrary[Double]]

given [A](using arbA: Arbitrary[A]): Arbitrary[Maybe[A]] = Arbitrary {
  Gen.frequency(
    1 -> Gen.const(Maybe.Nothing),
    3 -> arbA.arbitrary.map(Maybe.Just(_))
  )
}

enum Maybe[+A] derives Eq:
  case Nothing
  case Just(a: A)

object Maybe:
  given Functor[Maybe] with
    def map[A, B](fa: Maybe[A])(f: A => B): Maybe[B] = fa match
      case Nothing => Nothing
      case Just(a) => Just(f(a))

  // // Exercise 1
  // given badFunctor: Functor[Maybe] with
  //   def map[A, B](fa: Maybe[A])(f: A => B): Maybe[B] = Nothing

class FunctorLawsSpec
    extends AnyFunSuite
    with FunSuiteDiscipline
    with Configuration:

  checkAll(
    "Maybe.FunctorLaws",
    FunctorTests[Maybe].functor[Int, String, Double]
  )
