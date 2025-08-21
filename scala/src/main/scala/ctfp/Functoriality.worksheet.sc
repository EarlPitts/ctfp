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

// Problem 1
case class Product[A, B](a: A, b: B)

given Bifunctor[Product] with
  extension [A, C](fa: Product[A, C])
    def bimap[B, D](f: A => B, g: C => D): Product[B, D] = fa match
      case Product(a, c) => Product(f(a), g(c))


// Problem 2
type Identity[A] = A
type Const[A,B] = A
type MyOption[A] = Either[Const[Unit,A],Identity[A]]

def to[A](a: Option[A]): MyOption[A] = a match
  case None => Left(())
  case Some(a) => Right(a)

def from[A](a: MyOption[A]): Option[A] = a match
  case Left(_) => None
  case Right(a) => Some(a)

// Problem 3
enum PreList[+A,+B]:
  case Nil
  case Const(a: A, b: B)
import PreList.*

given Bifunctor[PreList] with
  extension [A, C](fa: PreList[A, C])
    def bimap[B, D](f: A => B, g: C => D): PreList[B, D] = fa match
      case Const(a,b) => Const(f(a), g(b))
      case Nil => Nil
