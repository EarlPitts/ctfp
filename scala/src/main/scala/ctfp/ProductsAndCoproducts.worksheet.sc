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

