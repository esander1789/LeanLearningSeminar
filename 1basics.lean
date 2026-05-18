import MIL.Common

-- Here's next easiest thing after Hello World: Evaluation in lean.

#check 2+2
#eval 2+2

-- Here is our first proof.
-- We can use the `rfl` tactic to prove things that are true by definition. 'rfl' stands for "reflexivity of equality".

example : 2+2=4 := by rfl

-- Another tactic  is `norm_num` which can evaluate numerical expressions and prove equalities between them.

example : 2+2=4 := by norm_num

-- Create a function and use it to evaluation some expressions.

def f (x:Nat) := x+5 -- add 5 to x
#eval f 6

def double (x : Nat) : Nat := x+x
#eval double 5
#eval double 3  + double 3
#eval double (3+9)

-- Create a new function that gives us recursion.

def dotwice (f: Nat -> Nat) (x:Nat) : Nat := f (f x)
#eval dotwice double 7

-- Composition of functions is also possible.

def square (x:Nat) : Nat := x*x
#eval dotwice double (square 3)
#eval dotwice square (double 3)

-- Here's something crazy that should warn you about typing of numbers!

#eval 2/4

#eval (2:Rat)/(4:Rat) -- Explicit typing is important!

#eval Rat.sqrt (4: Rat)
