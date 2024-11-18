-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

inductive Weekday where
  | sunday -- : Weekday (this is optional)
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

#check Weekday.sunday
#check Weekday.monday

open Weekday
#check sunday
#check monday
#eval tuesday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3

-- set_option pp.all true
#print numberOfDay -- ... numberOfDay.match_1
-- #print numberOfDay.match_1 -- ... Weekday.casesOn ... -- does not work with Repr
#print Weekday.casesOn -- ... Weekday.rec ...
#check @Weekday.rec

namespace Weekday -- useful to have namespace same name as data type
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday
example : next (previous tuesday) = tuesday := rfl

def next_previous_1 (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- tactics version of the same proof
def next_previous_2 (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

namespace Exercises
-- Try defining other operations on the natural numbers, such as multiplication,
-- the predecessor function (with pred 0 = 0), truncated subtraction
-- (with n - m = 0 when m is greater than or equal to n), and exponentiation.
-- Then try proving some of their basic properties,
-- building on the theorems we have already proved.
-- Since many of these are already defined in Lean's core library,
-- you should work within a namespace named Hidden, or something like that,
-- in order to avoid name clashes.

-- Define some operations on lists, like a length function or the reverse function.
-- Prove some properties, such as the following:
-- a. length (s ++ t) = length s + length t
-- b. length (reverse t) = length t
-- c. reverse (reverse t) = t

-- Define an inductive data type consisting of terms
-- built up from the following constructors:
--     const n, a constant denoting the natural number n
--     var n, a variable, numbered n
--     plus s t, denoting the sum of s and t
--     times s t, denoting the product of s and t

-- Recursively define a function that evaluates any such term with respect
-- to an assignment of values to the variables.

-- Similarly, define the type of propositional formulas, as well as
-- functions on the type of such formulas: an evaluation function,
-- functions that measure the complexity of a formula,
-- and a function that substitutes another formula for a given variable.
end Exercises
