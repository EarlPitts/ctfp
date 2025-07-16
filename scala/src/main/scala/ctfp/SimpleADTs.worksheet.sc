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

// The algebra of types

// Product <=> Multiplication
// Sum     <=> Addition
// Arrow   <=> Exponentiation

// You just take the cardinality of the component types,
// use the operator that corresponds to your type constructor,
// and you got the cardinality of the composite type

// Canonic representation: Products inside Sums

import Tri.*

enum Tri:
  case One
  case Two
  case Three

// 2^3 = 8 possible implementations
def g1: Tri => Boolean = 
  case One => true
  case Two => true
  case Three => true


def g2: Tri => Boolean = 
  case One => false
  case Two => false
  case Three => false

  
def g3: Tri => Boolean = 
  case One => false
  case Two => false
  case Three => true

  
def g4: Tri => Boolean = 
  case One => false
  case Two => true
  case Three => false

  
def g5: Tri => Boolean = 
  case One => true
  case Two => false
  case Three => false

  
def g6: Tri => Boolean = 
  case One => true
  case Two => true
  case Three => false

  
def g7: Tri => Boolean = 
  case One => true
  case Two => false
  case Three => true

  
def g8: Tri => Boolean = 
  case One => false
  case Two => true
  case Three => true

 
// 2 * 2 == 2 + 2
def h: (Boolean, Boolean) => Either[Boolean, Boolean] =
  case (true, true)   =>  Left(true)
  case (true, false)  =>  Left(false)
  case (false, true)  =>  Right(true)
  case (false, false) =>  Right(false)

def hInv: Either[Boolean, Boolean] => (Boolean, Boolean) =
  case Left(true)   =>  (true, true)
  case Left(false)  =>  (true, false)
  case Right(true)  =>  (false, true)
  case Right(false) =>  (false, false)

// Exercises

def ex1[A]: Option[A] => Either[Unit, A] =
  case None => Left(())
  case Some(a) => Right(a)

def ex1Inv[A]: Either[Unit, A] => Option[A] =
  case Left(()) => None
  case Right(a) => Some(a)

// Exercise 2
trait Shape:
  def area: Double

case class Circle(r: Float) extends Shape:
    def area = math.Pi * r * r

case class Rect(d: Float, h: Float) extends Shape:
  def area = d * h

// Exercise 3
// These exercises are about the expression problem
// It tries to point out the difference between OOP
// and functional data definitions

trait BetterShape:
  def area: Double
  def circ: Double

case class Circle2(r: Float) extends BetterShape:
    def area = math.Pi * r * r
    def circ = 2.0 * math.Pi * r

case class Rect2(d: Float, h: Float) extends BetterShape:
  def area = d * h
  def circ = 2.0 * (d * h)

// In case of OOP languages, adding a new method means
// changing every subtype of the parent
// With functional languages, we just add a new function
// and pattern match on the constructors

// Exercise 4
// Adding a new constructor (subtype) in OOP means
// creating a new datatype that extends the parent,
// we don't have to touch existing code
// In functional languages, we have to modify the
// original definition and all the functions that
// operate on it

case class Square(s: Float) extends BetterShape:
  def area = s * s
  def circ = 4.0 * s

// Exercise 5
// Accidentally proved it on line 137
