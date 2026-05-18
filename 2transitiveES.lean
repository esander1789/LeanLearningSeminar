import MIL.Common

-- A bunch of examples where transitivity directly implies a result.
-- Example is a theorem without the name.

example  (x y z : ℝ) (h1: x = y) (h2: y = z) :  x = z := by
apply Eq.trans -- built in equal transitivity
apply h1
apply h2

example (x y z : ℚ) (h1: x ≤ y) (h2: y ≤ z): x ≤ z := by
apply le_trans -- built in le transitivity
apply h1
apply h2


example (x y z : ℚ) (h1: x ≤ y) (h2: y ≤ z): x ≤ z := by
linarith  -- linear arithmetic tactic, can solve inequalities like this

-- Not a direct consequence of transitivity, but still a consequence of the same axioms.

example (x y z : ℚ) (h1: x ≤ y) (h2: y < z): x < z := by
linarith

-- But let's see if we can do it without the magic of `linarith`.

example (x y z : ℚ) (h1: x ≤ y) (h2: y < z): x < z := by
apply lt_of_le_of_lt -- built in transitivity for le and lt That is le plus < implies <
apply h1
apply h2

example (x y z : ℚ) (h1: x < y) (h2: y ≤ z): x < z := by
apply lt_of_lt_of_le -- built in transitivity for lt followed by  le That is  le plus < implies <
apply h1
apply h2
