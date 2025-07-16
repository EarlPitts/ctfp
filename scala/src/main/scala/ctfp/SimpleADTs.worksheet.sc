// Product types

// This is basically what we call records in Haskell,
// as we mix the constructor and the selectors together
case class Product[A, B](a: A, b: B)

Product("a", 1)
Tuple2("a", 1)
("a", 1)

// Nested tuples are isomorphic to n-tuples
// To show that two structures are isomorphic, you just need
// a pair of functions that "convert" between them without losing information
def alpha[A, B, C](t: ((A, B), C)): (A, B, C) = t match
  case ((a, b), c) => (a, b, c)

def alphaInv[A, B, C](t: (A, B, C)): ((A, B), C) = t match
  case (a, b, c) => ((a, b), c)

case class Element(name: String, symbol: String, atomicNumber: Int)

// These two are isomorphic
def tupleToElem(e: (String, String, Int)): Element = e match
  case (n, s, a) => Element(n, s, a)
def elemToTuple(e: Element): (String, String, Int) = e match
  case Element(n, s, a) => (n, s, a)

// In scala we just use the field accessors to get the parts
Element("Carbon", "Ca", 6).symbol

// Product with Unit forms a monoid over Set
trait SetMonoid:
  type Id
  type Mult[A,B]

object ProductMonoid extends SetMonoid:
  type Id = Unit
  type Mult[A,B] = (A,B)

// Sum types (coproduct)
import Either.*

enum Either[A,B]:
  case Left(a: A)
  case Right(b: B)
  
// Evidence for commutativity
def comm[A,B]: (Either[A,B] => Either[B,A], Either[B,A] => Either[A,B]) =
  (
    (e: Either[A,B]) => e match
      case Left(a) => Right(a)
      case Right(b) => Left(b),
    (e: Either[B,A]) => e match
      case Left(b) => Right(b)
      case Right(a) => Left(a)
  )

// Coproduct with Void (Nothing) forms a monoid over Set
object CoproductMonoid extends SetMonoid:
  type Id = Nothing
  type Mult[A,B] = Either[A,B]

// Arrow type
type Arrow[A,B] = A => B

val f: Arrow[Int, Int] = _ + 1
val f2: Function1[Int, Int] = _ + 1
