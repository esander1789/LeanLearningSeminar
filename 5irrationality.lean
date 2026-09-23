import MIL.Common
import Mathlib
-- I want to prove that 2 is irrational. It is not clear if I could do this without already knowing a proof. But anyway, I will reformulate the irrationality of 2 in the statement of the theorem.

-- in setting it up, you can check the meaning of built in theorems with #print
#print Nat.Coprime
#print Nat.gcd

-- here is the setup.

theorem two_irrationala (x y : ℕ ) (h₁: Nat.Coprime x y)  : x^2 ≠ 2 * y^2  := by
sorry

-- Before the proof, a simple illustration of the intro tactic in a contradiction proof.

example (x y : ℕ ) (h:x ≠ y) : 2*x ≠ 2*y := by
intro eq -- this is the intro tactic, which takes the assumption that 2*x = 2*y and gives it a name (eq) so we can refer to it later.
have : x = y := by
  exact Nat.mul_left_cancel (by norm_num) eq -- the first is the cancelation theorem, the second shows that 2 ≠ 0, and the third is the assumption that 2*x = 2*y.
contradiction

-- Now I  prove the sqrt(2) theorem and use proof by contradiction.
-- This proof is most likely not maximally efficient.
-- below the proof I have put in my scratch work, so you can see the workflow.

theorem two_irrationalb (x y : ℕ ) (h₁: Nat.Coprime x y)  : x^2 ≠ 2 * y^2  := by
intro sqr_eq -- naming the contrary assumption: x^2 = 2*y^2.
have x2even : 2 ∣ x^2 := by
  have right : 2 ∣ 2 * y^2 := dvd_mul_right 2 (y^2)
  rwa [← sqr_eq] at right
have xeven : 2 ∣ x := by
  apply Nat.Prime.dvd_of_dvd_pow
  apply Nat.prime_two
  apply x2even
have x4 : 4 ∣ x^2 := by
    obtain ⟨k, hk⟩ := xeven -- unpacks h: witness k and equation x = 2*k
    exact ⟨k^2, by rw[hk]; ring⟩ -- rewrites the goal using hk. The ring tactic simplifies the algebraic expression.
have yeven : 2 ∣ y := by
  obtain ⟨k, hk⟩ := x4
  have ye1: 4 * k = 2 * y ^ 2 := by
    rwa [← hk]
  have ye2: 2 * k  = y ^ 2 := by
    have ye2a: 2*(2 * k) = 2 * y ^ 2 := by
      rw [← ye1]
      ring
    have ye2b : 2*k = y^2 := by
      exact Nat.mul_left_cancel (by norm_num) ye2a
    apply ye2b
  have ye3 : 2 ∣ y ^ 2 := by
    exact ⟨k, ye2.symm⟩
  have ye4:  2 ∣ y := by
    apply Nat.Prime.dvd_of_dvd_pow
    apply Nat.prime_two
    apply ye3
  exact ye4
have xyfactor : 2 ∣ Nat.gcd x y := by
  apply Nat.dvd_gcd
  apply xeven
  apply yeven
have xynotcoprime : ¬Nat.Coprime x y := by
  intro xycoprime
  have : 2 ∣ 1 := by
    rw [← xycoprime]
    exact xyfactor
  contradiction
contradiction


-- I have left my scratch work here so you can see the workflow.
-- in the course of stepping through the sqrt 2 proof, I had to check out individual steps.
-- Also AI was always at my side helping out. (In this situation, AI should not be considered as cheating.)

example (x y : ℕ) (h : x^2 = 2 * y^2) : 2 ∣ x^2 := by
  have right : 2 ∣ 2 * y^2 := dvd_mul_right 2 (y^2)
  rwa [← h] at right

example (x : ℕ) (h : 2 ∣ x) : 4 ∣ x^2 := by
  obtain ⟨k, hk⟩ := h -- unpacks h into a witness k and equation x = 2*k
  exact ⟨k^2, by rw[hk]; ring⟩ -- rewrites the goal using hk. The ring tactic simplifies the algebraic expression.
