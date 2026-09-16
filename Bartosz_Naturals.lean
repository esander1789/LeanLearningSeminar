-- this says the following: members of type N can be constructed
-- in two ways,
---- either 'zero' with no additional data is a member of N
---- or given n : N, succ n is a member of N
inductive N where
  | zero : N
  | succ : N → N

#check N.succ N.succ

-- such definition allows for pattern matching
def add (a b : N) : N :=
  match b with
  | N.zero => a
  | N.succ b' => N.succ (add a b')

#check add (N.succ N.zero) (N.succ (N.succ (N.zero)))
#eval add (N.succ N.zero) (N.succ (N.succ (N.zero)))

-- handy notation
instance : OfNat N 0 where
  ofNat := N.zero

instance : OfNat N 1 where
  ofNat := N.succ (0 : N)

instance : OfNat N 2 where
  ofNat := N.succ (1 : N)

instance : OfNat N 3 where
  ofNat := N.succ (2 : N)

instance : OfNat N 4 where
  ofNat := N.succ (3 : N)

-- our first theorem
theorem two_plus_two : (add 2 2 = 4) := by rfl
-- theorems are types. A proof of theorem T is a member of the type T
-- This is Curry Howard isomorphism

-- see the C++ example



#check Eq.refl (0 : N)

---------- let's see what the logical operators really are -----

#print And
inductive MyAnd (p q : Prop) : Prop where
  | intro : p → q → MyAnd p q
theorem MyAnd.left {p q : Prop} (h : MyAnd p q) : p :=
  match h with
  | MyAnd.intro hp _ => hp

theorem MyAnd.right {p q : Prop} (h : MyAnd p q) : q :=
  match h with
  | MyAnd.intro _ hq => hq

theorem MyAndCommutative {p q : Prop} (a : MyAnd p q) :
  MyAnd q p := MyAnd.intro a.right a.left

#print Or
inductive MyOr (p q : Prop) : Prop where
  | left  : p → MyOr p q
  | right : q → MyOr p q

theorem MyOrCommutative {p q : Prop} (a : MyOr p q) : MyOr q p :=
  match a with
  | MyOr.left hp  => MyOr.right hp
  | MyOr.right hq => MyOr.left hq

-- code with real Or and And is similar
-- https://github.com/leanprover/lean4/blob/86c6347c75e39ec18c40e25ed2143b71a6e04a0a/src/Init/Prelude.lean#L673-L675

---------- double negation  and modus ponens -------------------

theorem modusPonens (p q : Prop) (a : p) (f : p → q) : q :=
  f a

-- what are the False and True types under the hood?
#print True
inductive myTrue
  | intro
-- a Proposition with a constructor not requiring any data:
-- we can produce it for free,
-- i.e (under Curry-Howard), everything implies True
theorem impliesTrue (p : Prop) : p → True := by
  intro a
  exact True.intro
-- version with plain lambda expressions
theorem impliesTrue' (p : Prop) : p → True :=
  fun (_ : p) => True.intro
-- so, this proof is the constant function!

#print False
inductive myFalse
-- a Proposition with noconstructors,
-- we cannot produce it. Hence, when we consider
-- all the cases a : False might be, it is zero cases.
-- i.e, (under Curry-Howard), False implies everything,
-- as "the proof is done in every case"
#print False
theorem impliedBy (p : Prop) : False → p := by
  intro a
  cases a
-- version with plain lambda expressions
theorem impliedBy' (p : Prop) : False → p :=
  fun (a : False) => nomatch a -- i.e match with empty arms

-- then the double negative is a function application
theorem doubleNegative (p : Prop) (a : p) : ¬ (¬ p) := by
  unfold Not
  intro not_p
  exact not_p a

theorem doubleNegative' (p : Prop) (a : p) : ¬ (¬ p) :=
  fun (not_p : p → False) => not_p a

theorem p_and_not_p (p : Prop) (hp : p) (hneg : ¬ p) : False := by
  unfold Not at hneg
  exact hneg hp

#check p_and_not_p
---------- proof irrelevance first time -----------------------

-- This cannot be proven n C++ : we do not have Dependent Types,
-- i.e. types depending on values of other types in C++.
-- type of add_zero is a dependent type
theorem add_zero (n : N) : add n 0 = n := by rfl
#check add_zero


#print add_zero

-- not every proof is by reflexivity!!!
theorem zero_add (n : N) : add 0 n = n := by
  induction n with
    | zero => rfl
    | succ m zero_add_m =>
      unfold add
      rw [zero_add_m]

#print zero_add
theorem two_plus_two' : (add 2 2 = 4) := by
  rw [<- add_zero 4]
  rfl

theorem does_not_matter : (two_plus_two = two_plus_two') := by apply @proof_irrel

#check does_not_matter
#check @proof_irrel

-- we say that p : Prop is contractible :D
theorem does_not_matter' : (two_plus_two = two_plus_two') := by rfl

theorem does_not_matter_does_not_matter :
  (does_not_matter = does_not_matter') := by apply @proof_irrel

#check does_not_matter_does_not_matter

---------- define pred, but how --------------------------------
-- this is ultimately bad
def badPred (n : N) : N :=
  match n with
    | 0 => 0
    | N.succ m => m

-- this is better
-- the Option is already declared
-- inductive Option (α : Type) where
--   | some (a : α)
--   | none

def maybePred (n : N) : Option N :=
  match n with
  | N.zero => Option.none
  | N.succ m => Option.some m

-- why bother if we know EXACTLY when the predecessor exists ? --

theorem nz_is_succ (n : N) (nz : n ≠ 0) : exists (m : N), n = N.succ m := by
  cases n with
    | zero =>
      exfalso
      exact nz rfl
    | succ m =>
      exact ⟨m, rfl ⟩

theorem succ_is_nz (n : N) : N.succ n ≠ 0 := by
  intro false
  cases false

def PositiveN : Type := { n : N // n ≠ 0 }

notation "N+" => PositiveN

def pred (n : N+) : N :=
  match n with
  | ⟨N.zero, h⟩ => False.elim (h rfl)
  | ⟨N.succ m, _⟩ => m

def succ (n : N) : N+ := ⟨N.succ n, succ_is_nz n ⟩

-- theorem succ_pred (n : N+) : succ (pred n) = n := by rfl
theorem succ_pred (n : N+) : succ (pred n) = n := by
  rcases n with ⟨n, nz⟩
  cases n with
    | zero =>
      -- unfold pred
      exfalso
      -- simp at nz
      exact nz rfl
    | succ m =>
      unfold pred
      unfold succ
      simp
      -- here we compare two proofs. they are equal
      -- by proof irrelevance
      rfl

-- handy notation
instance : OfNat N+ 1 where
  ofNat := ⟨(1 : N), succ_is_nz (0 : N)⟩
instance : OfNat N+ 2 where
  ofNat := ⟨(2 : N), succ_is_nz (1 : N)⟩
instance : OfNat N+ 3 where
  ofNat := ⟨(3 : N), succ_is_nz (2 : N)⟩
instance : OfNat N+ 4 where
  ofNat := ⟨(4 : N), succ_is_nz (3 : N)⟩

#eval add 2 2
