// Function Types

// In the category of sets (Set),
// hom-sets are internal (they
// themselves are just sets)

type Z[A,B] = Function1[A,B]

// We can represent function application
// with a morphism from the product of
// functions and their inputs to the outputs
def ap[A,B]: Tuple2[Z[A,B],A] => B = f => f match
  case (f, a) => f(a)

// Note: you cannot define the function
// type without the product type

def succ: Int => Int = _ + 1

ap((succ, 0)) // ap(succ, 0) also works


def g2: Tuple2[Int, Int] => Int = t => t._2 // Identity
// def g2: Tuple2[Int, Int] => Int = t => t._1 // Const

def g: Tuple2[Int => Int, Int] => Int = t => t._1(t._2)

def h: Int => (Int => Int) = _ => _ + 1
