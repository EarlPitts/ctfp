import Maybe.*

// A Functor is mapping between two categories
// It's a function between objects of the two categories
// that preserves the morphisms

// We express them with a *Type Constructor* and
// a *Function* called fmap/map

// Functor Laws:
// Identity: map(identity) = identity
// Composition: map(f).map(g) == map(f compose g)

// Intuition: the structure of the source category
// has to be preserverd -> things cannot be broken
// apart (think continuity in calculus)!

// Collapsing functors: source > target
// Embedding functors: source < target

// In programming we usually refer to
// *Endofunctors* when talking about functors
// (Mapping Set to Set)

enum Maybe[+A]:
  case Nothing
  case Just(a: A)

// If we want to show that Maybe is a functor,
// we have to *provide some evidence* in the form
// of a *Typeclass instance*

object Maybe:
  given Functor[Maybe] with
    extension [A](fa: Maybe[A])
      def map[B](f: A => B): Maybe[B] = fa match
        case Nothing => Nothing
        case Just(a) => Just(f(a))

// Mapping types: Maybe: A => Maybe A
// Mapping morphisms: map: (A => B) => (Maybe A => Maybe B)
// You can think of this as *lifting* the function into
// some context/structure

// Our implementation has to obey rules! (check FunctorLawsSpec)

// Equational Reasoning
// We can substitute terms to their normalized form
// Intuition: substitute function with their result

// Id law
Nothing.map(identity) == Nothing
Just(2).map(identity) == Just(2)

// Comp law
Just(2).map(_ + 1).map(_ + 2) ==
  Just(2).map(((n: Int) => n + 1) compose (_ + 2))

(Nothing: Maybe[Int]).map(_ + 1).map(_ + 2) ==
  (Nothing: Maybe[Int]).map(((n: Int) => n + 1) compose (_ + 2))

// We express Functor as a Typeclass
// Note the higher-kinded type:
// Functor iself gets a type constructor,
// instead of a type
trait Functor[F[_]]:
  extension [A](fa: F[A]) def map[B](f: A => B): F[B]

// List functor instance
given Functor[List] with
  extension [A](fa: List[A])
    def map[B](f: A => B): List[B] = fa match
      case Nil     => Nil
      case x :: xs => f(x) :: xs.map(f)

List(1, 2, 3).map(_ + 1)

// Reader functor instance
given [R]: Functor[[A] =>> Function1[R, A]] with
  extension [A](fa: Function1[R, A])
    def map[B](f: A => B): Function1[R, B] =
      f compose fa
      // r => f(fa(r))

val g = ((n: Int) => n + 1).map((n: Int) => n + 1)

g(2)

// Functors as Containers
// This analogy breaks down even in simple cases
// E.g.: reader functor (it doesn't really "contain" the input)
// BUT! If we think of functions as data (lookup table),
// it still works!

// It may contains the value, or it may contain
// some recipe for creating it

// Functors are not about "accessing" the value,
// but "manipulating it"

// Const functor, maps every object from
// the source to a single objects in the target
// and maps every morphism to id

case class Const[A,B](value: A):
  def map[C](f: B => C): Const[A,C] = Const(value)

Const[Int, String](3).map(_ + 2)

// Most people when they say functor what they really mean
// is a covariant functor
// Contravariant functors are more like functors that
// "consume" their type parameter

// https://typelevel.org/cats/typeclasses/contravariant.html
trait Contravariant[F[_]]:
  extension [A](fa: F[A]) def contramap[B](f: B => A): F[B]

type Predicate[A] = Function1[A, Boolean]

given Contravariant[Predicate] with
  extension [A](fa: Predicate[A])
    def contramap[B](f: B => A): Predicate[B] =
      f andThen fa
      // b => fa(f(b))

val p = ((_ > 10): Predicate[Int]).contramap[String](_.length)

p("sajtsokifli")

// George Wilson - The Extended Functor Family: https://youtu.be/JZPXzJ5tp9w

// Composing Functors

val x = List(Just(2), Just(3)).map(_.map(_ + 2))

object Functor:
  def apply[F[_]](implicit instance: Functor[F]) = instance

type MaybeList[A] = Maybe[List[A]]

given Functor[MaybeList] with
  extension [A](fa: MaybeList[A])
    def map[B](f: A => B): MaybeList[B] =
      Functor[Maybe].map(fa)(Functor[List].map(_)(f))
      // Functor[Maybe].map compose Functor[List].map

// We have a category called Cat, where
// morphisms are functors (they compose,
// and we have an identity functor), and
// objects are categories

// Exercises (See functor law proofs in Functor.agda)
val f: Int => Int = _ + 2
val h: Int => Int = _ + 1
val i: Int => Int = _ + 4

f.map(identity)(2) == identity(f(2))
f.map(h).map(i)(3) == f.map(h compose i)(3)

// f.map(identity)
// identity compose f
// f
// identity(f)

// f.map(g).map(h)
// h compose f.map(g)
// h compose g compose f
// f.map(g compose h)
