import collection.mutable.Map
import collection.immutable.Map as ImmMap
import scala.util.Random

import cats.*
import cats.implicits.*
import cats.data.State

def clock: Long = System.currentTimeMillis()
extension [A](a: => A)
  def t: A =
    val before = clock
    val res = a
    val after = clock
    val duration = after - before
    println(s"took $duration")
    res

def fibo(n: Int): Int =
  def go(n: Int, acc1: Int, acc2: Int): Int =
    n match
      case 0 => acc1
      case 1 => acc2
      case _ => go(n - 1, acc2, acc1 + acc2)
  go(n, 1, 1)

// Prblem 1
def memoize[A, B]: (A => B) => (A => B) = f =>
  val seen: Map[A, B] = Map.empty
  a =>
    seen.get(a) match
      case None =>
        val b = f(a)
        seen.put(a, b)
        b
      case Some(value) => value

val memoizedFibo = memoize(fibo)

fibo(100000000).t
fibo(100000000).t

memoizedFibo(100000000).t
memoizedFibo(100000000).t

memoizedFibo(100000001).t
memoizedFibo(100000001).t

// Problem 2
val memoizedRand = memoize(Random.nextInt)

memoizedRand(10)
memoizedRand(10)
memoizedRand(10)
memoizedRand(10)
memoizedRand(10)

// Problem 3
val memoizedSeededRand =
  memoize((n: Int) => (seed: Long) => Random(seed).nextInt(n))

def fineClock: Long = System.nanoTime()

memoizedSeededRand(10)(fineClock)
memoizedSeededRand(10)(fineClock)
memoizedSeededRand(10)(fineClock)
memoizedSeededRand(10)(fineClock)
memoizedSeededRand(10)(fineClock)

// BONUS
// Pure alternative of sequencing random
val rands: State[Long, (Int, Int, Int)] = for
  fst <- State.get.map(memoizedSeededRand(10))
  _ <- State.modify[Long](_ + 1)
  snd <- State.get.map(memoizedSeededRand(10))
  _ <- State.modify[Long](_ + 1)
  thrd <- State.get.map(memoizedSeededRand(10))
yield (fst, snd, thrd)

rands.runA(fineClock).value

// Pure memoizer (modulo printing duratino :) )
def pureMemoize[A, B]: (A => B) => (A => State[ImmMap[A, B], B]) = f =>
  a =>
    State.get[ImmMap[A, B]].flatMap { seen =>
      seen.get(a) match
        case None =>
          val b = f(a).t
          State.modify[ImmMap[A, B]](_.updated(a, b)).as(b)
        case Some(value) => State.pure(value.t)
    }

val pureMemoizedFibo = pureMemoize(fibo)

val mem: State[ImmMap[Int, Int], (Int, Int)] = for
  fst <- pureMemoizedFibo(100000000)
  snd <- pureMemoizedFibo(100000000)
yield (fst, snd)

mem.run(ImmMap.empty).value

// Problem 5

// Function => Exponential type
// f: a -> b <=> b^a

val b1 = Function.const(true)
val b2 = Function.const(false)
val b3 = identity
val b4: Boolean => Boolean = !_
