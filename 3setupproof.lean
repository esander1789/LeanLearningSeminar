import MIL.Common

example
(x y : ℕ)
(h₁ : Prime x)
(h₂ : ¬Even x) -- Note that this means "not even"
(h₃ : y > x) : y ≥ 4 := by
sorry -- This is a placeholder for a proof that we haven't written yet. It allows us to write the statement of the theorem without proving it right now.

theorem nextprime -- could also write as a theorem instead of example. The difference is that the theorem will be added to the library of theorems and can be used in later proofs, while an example is just a standalone statement that we are proving for practice.
(x y : ℕ)
(h₁ : Prime x)
(h₂ : ¬Even x) -- Note that this means "not even"
(h₃ : y > x) : y ≥ 4 := by
sorry -- This is a placeholder for a proof that we haven't written yet. It allows us to write the statement of the theorem without proving it right now.
