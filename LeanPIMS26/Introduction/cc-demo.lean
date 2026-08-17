import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Char

def split {α : Type*} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest => (a :: (split rest).1, b :: (split rest).2)

theorem length_split_fst_le {α : Type*} (l : List α) : (split l).1.length ≤ l.length := by
  fun_induction split l with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest ih => simp; omega

theorem length_split_snd_le {α : Type*} (l : List α) : (split l).2.length ≤ l.length := by
  fun_induction split l with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest ih => simp; omega

def merge {α : Type*} [LinearOrder α] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

def mergeSort {α : Type*} [LinearOrder α] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    merge (mergeSort (split (a :: b :: rest)).1) (mergeSort (split (a :: b :: rest)).2)
termination_by l => l.length
decreasing_by
  · have := length_split_fst_le rest
    simp [split]
    omega
  · have := length_split_snd_le rest
    simp [split]
    omega

#eval mergeSort [5, 3, 8, 1, 9, 2, 7]
#eval mergeSort [(-4 : Int), 7, 0, -11, 3]
#eval mergeSort ["pear", "apple", "orange", "fig"]
#eval mergeSort ['z', 'a', 'q', 'm']

inductive Sorted {α : Type*} [LE α] : List α → Prop where
  | nil : Sorted []
  | single (a : α) : Sorted [a]
  | cons {a b : α} {l : List α} : a ≤ b → Sorted (b :: l) → Sorted (a :: b :: l)

theorem Sorted.tail {α : Type*} [LE α] {x : α} {l : List α} (h : Sorted (x :: l)) :
    Sorted l := by
  cases h with
  | single => exact .nil
  | cons _ h => exact h

theorem Sorted.le_head? {α : Type*} [LE α] {x : α} {l : List α} (h : Sorted (x :: l)) :
    ∀ z ∈ l.head?, x ≤ z := by
  cases h with
  | single => simp
  | cons hab _ => simpa using hab

theorem sorted_cons_of_le_head? {α : Type*} [LE α] {x : α} {l : List α}
    (hl : Sorted l) (hx : ∀ z ∈ l.head?, x ≤ z) : Sorted (x :: l) := by
  cases hl with
  | nil => exact .single x
  | single a => exact .cons (by simpa using hx) (.single a)
  | cons hab h => exact .cons (by simpa using hx) (.cons hab h)

theorem le_head?_merge {α : Type*} [LinearOrder α] {a : α} {xs ys : List α}
    (hxs : ∀ z ∈ xs.head?, a ≤ z) (hys : ∀ z ∈ ys.head?, a ≤ z) :
    ∀ z ∈ (merge xs ys).head?, a ≤ z := by
  revert hxs hys
  fun_induction merge xs ys with
  | case1 ys => exact fun _ h => h
  | case2 x xs => exact fun h _ => h
  | case3 x xs y ys h ih => intro h₁ _; simpa using h₁
  | case4 x xs y ys h ih => intro _ h₂; simpa using h₂

theorem sorted_merge {α : Type*} [LinearOrder α] {xs ys : List α}
    (hx : Sorted xs) (hy : Sorted ys) : Sorted (merge xs ys) := by
  revert hx hy
  fun_induction merge xs ys with
  | case1 ys => exact fun _ hy => hy
  | case2 x xs => exact fun hx _ => hx
  | case3 x xs y ys h ih =>
    intro hx hy
    refine sorted_cons_of_le_head? (ih hx.tail hy) ?_
    exact le_head?_merge hx.le_head? (by simpa using h)
  | case4 x xs y ys h ih =>
    intro hx hy
    refine sorted_cons_of_le_head? (ih hx hy.tail) ?_
    exact le_head?_merge (by simpa using (le_total x y).resolve_left h) hy.le_head?

theorem sorted_mergeSort {α : Type*} [LinearOrder α] (l : List α) : Sorted (mergeSort l) := by
  fun_induction mergeSort l with
  | case1 => exact .nil
  | case2 a => exact .single a
  | case3 a b rest ih₁ ih₂ => exact sorted_merge ih₁ ih₂
