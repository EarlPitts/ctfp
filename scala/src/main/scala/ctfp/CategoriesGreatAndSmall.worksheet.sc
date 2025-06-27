import cats._
import cats.implicits._

// Problem 3
val allMonoid = new Monoid[Boolean]:
  def combine(x: Boolean, y: Boolean): Boolean = x && y
  def empty: Boolean = true

val anyMonoid = new Monoid[Boolean]:
  def combine(x: Boolean, y: Boolean): Boolean = x || y
  def empty: Boolean = false

case class All(getAll: Boolean) extends AnyRef
case class Any(getAll: Boolean) extends AnyRef

given Monoid[All] with
  def combine(x: All, y: All): All = All(x.getAll && y.getAll)
  def empty: All = All(true)

given Monoid[Any] with
  def combine(x: Any, y: Any): Any = Any(x.getAll || y.getAll)
  def empty: Any = Any(false)

Any(true) |+| Any(false)
All(true) |+| All(false)
