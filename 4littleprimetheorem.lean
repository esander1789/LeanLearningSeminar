import MIL.Common
import Mathlib

example
(x y : ℕ)
(h₁ : Nat.Prime x)
(h₂ : ¬Even x)
(h₃ : y > x) : y ≥ 4 := by
  have hxne2 : x ≠ 2 := by
    intro hx
    rw [hx] at h₂
    exact h₂ ⟨1,rfl⟩
  have hx2: 2 ≤ x := by
    apply Nat.Prime.two_le
    apply h₁
  have hx3: 3 ≤ x := by
    apply Nat.lt_of_le_of_ne hx2 (Ne.symm hxne2)
  have : 3 < y:= by
      apply lt_of_le_of_lt
      apply hx3
      apply h₃
  linarith

-- Me and the AI worked our way through this. In the course of it, I had to check out the individual steps as their own theorems, listed below. Takeaways: 1. Express everything as < and not >. Since all the built in theorems work this way. 2. Often the AI has a little bit of mistakes in the names of the built-in theorems. 3. It really matters how you indent in  Lean4!

theorem not_even_not_two (x : ℕ) (h : ¬Even x) : x ≠ 2 := by
  intro hx
  rw [hx] at h
  exact h ⟨1, rfl⟩  -- Apply the definition of even to the first case (i.e. 2*1).

theorem prime_ge_two
(x : ℕ) (hp : Nat.Prime x) : 2 ≤ x := by
apply Nat.Prime.two_le
apply hp
