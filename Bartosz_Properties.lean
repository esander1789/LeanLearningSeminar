import Mathlib

inductive Snake (α : Type) where
  | dead
  | head (a : α) (s : Snake α)

def isSorted {α : Type} [LinearOrder α] (s : Snake α) : Prop :=
  match s with
  | Snake.dead => True
  | Snake.head _ Snake.dead => True
  | Snake.head a (Snake.head b t) =>
    a ≤ b ∧ isSorted (Snake.head b t)

def SortedSnake (α : Type) [LinearOrder α] : Type :=
  {s : Snake α // isSorted s}

#check SortedSnake

def insertFirst {α : Type} [LinearOrder α] (a : α) : Snake α → Snake α
  | Snake.dead => Snake.head a Snake.dead
  | Snake.head x t =>
    if a ≤ x then
      Snake.head a (Snake.head x t)
    else
      Snake.head x (insertFirst a t)

def insertionSort {α : Type} [LinearOrder α] : Snake α → Snake α
  | Snake.dead => Snake.dead
  | Snake.head a t => insertFirst a (insertionSort t)

lemma isSortedTail {α : Type} [LinearOrder α] (a : α)
  (s : Snake α) (srt : isSorted (Snake.head a s)) : isSorted s := by
 cases s with
 | dead => tauto
 | head b t => 
  simp [isSorted] at srt
  exact srt.right

lemma insertAfterHead {α : Type} [LinearOrder α]
 (a b : α) (s : Snake α) (srt : isSorted (Snake.head b s))
 (le_ab : a ≤ b) : isSorted (Snake.head a (Snake.head b s)) := by
  cases s with
  | dead => { simp only [isSorted, and_true]; assumption}
  | head c t => {
   simp only [isSorted]
   simp [isSorted] at srt
   -- tauto -- automatically, or manually below
   constructor
   · exact le_ab
   · constructor
     · exact srt.left
     · exact srt.right
  }

lemma insertIntoUnknown {α : Type} [LinearOrder α]
 (a b : α) (s : Snake α) (srt : isSorted (insertFirst b s))
 (le_ab : a ≤ b) : isSorted (Snake.head a (insertFirst b s)) := by
  sorry

lemma isSortedInsert {α : Type} [LinearOrder α]
 (a : α) (s : Snake α) (srt_s : isSorted s) : isSorted (insertFirst a s) := by
  induction s with
   | dead => {
    unfold isSorted
    unfold insertFirst
    simp
   }
   | head b t ih => {
    dsimp [insertFirst]
    split_ifs with le_ab -- compare a with b
    {
      apply insertAfterHead a b t srt_s le_ab
    }
    {
      have srt_t : isSorted t :=
       by apply isSortedTail b t srt_s
      apply ih at srt_t
      have le_ba : b ≤ a := by sorry
      apply insertIntoUnknown b a t srt_t le_ba
    }
   }

theorem isSortedInsertionSort {α : Type} [LinearOrder α]
 (s : Snake α) : isSorted (insertionSort s) := by
  induction s with
  | dead => tauto
  | head b t ih =>
   simp only [insertionSort]
   apply isSortedInsert b _ ih
