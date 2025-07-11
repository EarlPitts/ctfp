// Tagged union vs union
import Tagged.*

enum Tagged:
  case A(a: Int)
  case B(b: String)

val x: Int | String = "sajt"
val y: Tagged = B("sajt")

x
y

// We match on the type at runtime
// This is not possible in haskell (modulo exotic types)
// due to type erasure (no runtime type information)
x match {
  case _: Int    => "I'm an Int"
  case _: String => "I'm a String"
}

// We can match on the constructor (which acts like a "tag")
y match {
  case A(a) => "I'm an A"
  case B(b) => "I'm a B"
}

// Exercises
import Either.*

enum Either[A, B]:
  case Left(a: A)
  case Right(b: B)

def i(n: Int): Int = n
def j(b: Boolean): Int = if b then 0 else 1

//      Int
//       ^
//       | m
//       |
// Either[Int,Bool]
//      ^ ^
//   i /   \ j
//    /     \
//  Int    Bool

def m(ib: Either[Int, Boolean]): Int = ib match
  case Left(i)  => i
  case Right(b) => if b then 0 else 1

def betterI = m compose Either.Left[Int, Boolean]
def betterJ = m compose Either.Right[Int, Boolean]

i(3)
betterI(3)

j(true)
betterJ(true)

j(false)
betterJ(false)

// 6
def m(i: Int): Either[Int, Boolean] = if i > 0 then Left(i) else Right(false)

def betterQuestionMarkLeft = m compose i
def betterQuestionMarkRight = m compose j

betterQuestionMarkLeft(2)
betterQuestionMarkRight(true)

// 7
def i2(n: Int): Int = if n < 0 then n else n + 2
def j2(b: Boolean): Int = if b then 0 else 1

def m2(ib: Either[Int, Boolean]): Int = ib match
  case Left(n) => if n < 0 then n else n - 2
  case Right(b) => if b then 0 else 1

def betterI2 = m2 compose Either.Left[Int, Boolean]
def betterJ2 = m2 compose Either.Right[Int, Boolean]

betterI2(3)
betterJ2(true)
