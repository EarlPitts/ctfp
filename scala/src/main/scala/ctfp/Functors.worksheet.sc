import cats.*
import cats.implicits.*

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

// Collapsing functors: 
// Embedding functors: 
// TODO Const functor, Id functor, embedding functor?

// In programming we usually refer to
// *Endofunctors* when talking about functors
// (Mapping Set to Set)

import Maybe.*

enum Maybe[+A]:
  case Nothing
  case Just(a: A)

// If we want to show that Maybe is a functor,
// we have to *provide some evidence* in the form
// of a *Typeclass instance*

object Maybe:
  given Functor[Maybe] with
    def map[A, B](fa: Maybe[A])(f: A => B): Maybe[B] = fa match
      case Nothing => Nothing
      case Just(a) => Just(f(a))

// Mapping types: Maybe: A => Maybe A
// Mapping morphisms: map: (A => B) => (Maybe A => Maybe B)
// You can think of this as *lifting* the function into
// some context/structure

// Our implementation has to obey rules! (check FunctorLawsSpec)

// Equational Reasoning
