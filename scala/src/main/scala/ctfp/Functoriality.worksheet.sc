// Bifunctors

trait Bifunctor[F[_, _]]:
  extension [A, C](fa: F[A, C]) def bimap[B, D](f: A => B, g: C => D): F[B, D]
  extension [A, C](fa: F[A, C])
    def first[B](f: A => B): F[B, C] =
      bimap(fa)(f, identity)
  extension [A, C](fa: F[A, C])
    def second[D](g: C => D): F[A, D] =
      bimap(fa)(identity, g)

given Bifunctor[Tuple2] with
  extension [A, C](fa: (A, C))
    def bimap[B, D](f: A => B, g: C => D): (B, D) = fa match
      case (a, c) => (f(a), g(c))

(1, 2).bimap(_ + 1, _ + 2)
(1, 2).first(_ + 1)
(1, 2).second(_ + 1)

given Bifunctor[Either] with
  extension [A, C](fa: Either[A, C])
    def bimap[B, D](f: A => B, g: C => D): Either[B, D] = fa match
      case Left(a)  => Left(f(a))
      case Right(c) => Right(g(c))

val succ: Int => Int = _ + 1

Left(1).bimap(succ, succ)
Right(2).bimap(succ, succ)
Right(2).first(succ)
Left(2).first(succ)

// Functors compose, and we know that
// Product and Sum are functorial

// If we can show that the basic buildings
// blocks of ADTs are functorial, then
// our ADTs also have to be functorial

// The basic building blocks are
// Identity and Const
case class Identity[A](a: A)
case class Const[A, B](a: A)

// (We will also need the Fixpoint for recursive types)

// Both of them are functors:
trait Functor[F[_]]:
  extension [A](fa: F[A]) def map[B](f: A => B): F[B]

given Functor[Identity] with
  extension [A](fa: Identity[A])
    def map[B](f: A => B): Identity[B] = Identity(f(fa.a))

given [C]: Functor[[A] =>> Const[C, A]] with
  extension [A](fa: Const[C, A])
    def map[B](f: A => B): Const[C, B] = Const(fa.a)

Identity(2).map(_ + 3)
Const[Int, Int](2).map(_ + 3)

// We can express the composition of
// a bifunctor and two functors
// into another bifunctor
case class BiComp[BF[_, _], FU[_], GU[_], A, B](comp: BF[FU[A], GU[B]])

type BestOption[A, B] = BiComp[Either, [C] =>> Const[Unit, C], Identity, A, B]

object BestOptionIso:
  def to[A, B](a: Option[A]): BestOption[B, A] = a match
    case None    => BiComp(Left(Const(())))
    case Some(a) => BiComp(Right(Identity(a)))

  def from[A, B](a: BestOption[B, A]): Option[A] = a match
    case BiComp(Left(_))            => None
    case BiComp(Right(Identity(a))) => Some(a)

// Scala needs just a tiny bit more
// type annotations than Haskell
given [BF[_, _]: Bifunctor, FU[_]: Functor, GU[_]: Functor]
    : Bifunctor[[A, C] =>> BiComp[BF, FU, GU, A, C]] with
  extension [A, C](fa: BiComp[BF, FU, GU, A, C])
    def bimap[B, D](f: A => B, g: C => D): BiComp[BF, FU, GU, B, D] =
      BiComp(fa.comp.bimap((fu: FU[A]) => fu.map(f), (gu: GU[C]) => gu.map(g)))

// We could use this superior version instead
// of just using Option, but we have to add
// some annotations
val someInt = BiComp(Right(Identity(2))): BestOption[Any, Int]
someInt.second(_ + 2)

// This compositionality of functorial
// primitives makes it possible to
// derive functors automatically

// In scala there are libs for this like
// shapeless and kittens (based on shapeless)

trait Monad[M[_]: Functor]:
  extension [A](ma: M[A])
    def flatMap[B](f: A => M[B]): M[B]
  extension [A](a: A)
    def pure: M[A]

type Writer[A] = Tuple2[String, A]

given Functor[Writer] with
  extension [A](fa: Writer[A])
    def map[B](f: A => B): Writer[B] = fa match
      case (str, a) => (str, f(a))

given Monad[Writer] with
  extension [A](ma: Writer[A])
    def flatMap[B](f: A => Writer[B]): Writer[B] = ma match
      case (str, a) => f(a) match
        case (str2, b) => (str ++ str2, b)
  extension [A](a: A)
    def pure: Writer[A] = ("", a)

("sajt", 2).map(_ + 3)

def tell(str: String): Writer[Unit] = (str, ())

val f: Writer[Int] = for
  a <- 2.pure
  _ <- tell("kecske")
  b <- 3.pure
  // _ <- tell("sajt")
yield a + b

("sajt", 2).flatMap(a => ("kecske", 3).map(b => (a + b)))

val x = Some(3)

for
  a <- x
yield a

// Problem 1
case class Product[A, B](a: A, b: B)

given Bifunctor[Product] with
  extension [A, C](fa: Product[A, C])
    def bimap[B, D](f: A => B, g: C => D): Product[B, D] = fa match
      case Product(a, c) => Product(f(a), g(c))

// Problem 2
type MyOption[A] = Either[Const[Unit, A], Identity[A]]

def to[A](a: Option[A]): MyOption[A] = a match
  case None    => Left(Const(()))
  case Some(a) => Right(Identity(a))

def from[A](a: MyOption[A]): Option[A] = a match
  case Left(_)            => None
  case Right(Identity(a)) => Some(a)

// Problem 3
enum PreList[+A, +B]:
  case Nil
  case Const(a: A, b: B)

given Bifunctor[PreList] with
  extension [A, C](fa: PreList[A, C])
    def bimap[B, D](f: A => B, g: C => D): PreList[B, D] = fa match
      case PreList.Const(a, b) => PreList.Const(f(a), g(b))
      case PreList.Nil         => PreList.Nil

// Problem 4
case class K2[C, A, B](c: C)

given [Z]: Bifunctor[[A, C] =>> K2[Z, A, C]] with
  extension [A, C](fa: K2[Z, A, C])
    def bimap[B, D](f: A => B, g: C => D): K2[Z, B, D] = K2(fa.c)

case class Fst[A, B](a: A)

given Bifunctor[Fst] with
  extension [A, C](fa: Fst[A, C])
    def bimap[B, D](f: A => B, g: C => D): Fst[B, D] = Fst(f(fa.a))

case class Snd[A, B](b: B)

given Bifunctor[Snd] with
  extension [A, C](fa: Snd[A, C])
    def bimap[B, D](f: A => B, g: C => D): Snd[B, D] = Snd(g(fa.b))
