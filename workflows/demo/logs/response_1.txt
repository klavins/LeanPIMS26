import Mathlib.Data.List.Basic
import Mathlib.Tactic

variable {α : Type*} [LinearOrder α]

def merge : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (a, b) := split rest
    (x :: a, y :: b)

theorem split_length_fst (l : List α) : (split l).1.length ≤ l.length := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y rest ih =>
    simp only [split]
    have := ih
    omega

theorem split_length_snd (l : List α) : (split l).2.length ≤ l.length := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y rest ih =>
    simp only [split]
    have := ih
    omega

theorem split_length_fst_lt (x y : α) (rest : List α) :
    (split (x :: y :: rest)).1.length < (x :: y :: rest).length := by
  simp only [split]
  have := split_length_fst rest
  simp
  omega

theorem split_length_snd_lt (x y : α) (rest : List α) :
    (split (x :: y :: rest)).2.length < (x :: y :: rest).length := by
  simp only [split]
  have := split_length_snd rest
  simp
  omega

def mergeSort : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    let (a, b) := split (x :: y :: rest)
    merge (mergeSort a) (mergeSort b)
termination_by l => l.length
decreasing_by
  · simp_wf
    exact split_length_fst_lt x y rest
  · simp_wf
    exact split_length_snd_lt x y rest

def Sorted : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ Sorted (y :: rest)

theorem sorted_cons {x : α} {l : List α} :
    Sorted (x :: l) ↔ (∀ y ∈ l, x ≤ y) ∧ Sorted l := by
  induction l with
  | nil => simp [Sorted]
  | cons y ys ih =>
    simp only [Sorted]
    constructor
    · rintro ⟨hxy, hsorted⟩
      rw [ih] at hsorted
      refine ⟨?_, hsorted.2⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hxy
      · exact le_trans hxy (hsorted.1 z hz)
    · rintro ⟨hall, hsorted⟩
      refine ⟨hall y (by simp), ?_⟩
      rw [ih]
      exact ⟨fun z hz => hall z (by simp [hz]), hsorted⟩

theorem merge_mem {x : α} {xs ys : List α} :
    x ∈ merge xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction xs, ys using merge.induct with
  | case1 ys => simp [merge]
  | case2 xs => simp [merge]
  | case3 a xs b ys hab ih =>
    simp only [merge, if_pos hab, List.mem_cons, ih]
    tauto
  | case4 a xs b ys hab ih =>
    simp only [merge, if_neg hab, List.mem_cons, ih]
    tauto

theorem merge_sorted {xs ys : List α} (hxs : Sorted xs) (hys : Sorted ys) :
    Sorted (merge xs ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simpa [merge]
  | case2 xs => simpa [merge]
  | case3 a xs b ys hab ih =>
    simp only [merge, if_pos hab]
    rw [sorted_cons]
    rw [sorted_cons] at hxs
    constructor
    · intro z hz
      rw [merge_mem] at hz
      rcases hz with hz | hz
      · exact hxs.1 z hz
      · simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hab
        · rw [sorted_cons] at hys
          exact le_trans hab (hys.1 z hz)
    · exact ih hxs.2 hys
  | case4 a xs b ys hab ih =>
    simp only [merge, if_neg hab]
    rw [sorted_cons]
    rw [sorted_cons] at hys
    constructor
    · intro z hz
      rw [merge_mem] at hz
      rcases hz with hz | hz
      · simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact le_of_not_le hab
        · rw [sorted_cons] at hxs
          exact le_trans (le_of_not_le hab) (hxs.1 z hz)
      · exact hys.1 z hz
    · exact ih hxs hys.2

theorem mergeSort_sorted (l : List α) : Sorted (mergeSort l) := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort, Sorted]
  | case2 x => simp [mergeSort, Sorted]
  | case3 x y rest ih1 ih2 =>
    rw [mergeSort]
    exact merge_sorted ih1 ih2