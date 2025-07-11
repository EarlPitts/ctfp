import Either.*

enum Either[A,B]:
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
  case Left(i) => i
  case Right(b) => if b then 0 else 1
