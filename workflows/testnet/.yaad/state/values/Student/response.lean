prelude

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

inductive Eq {α : Type} (a : α) : α → Type where
  | refl : Eq a a

def add : Nat → Nat → Nat
  | n, Nat.zero => n
  | n, Nat.succ m => Nat.succ (add n m)

notation:65 a " + " b => add a b
notation:50 a " = " b => Eq a b

def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one

notation "1" => one
notation "2" => two

theorem one_plus_one_equals_two : 1 + 1 = 2 := Eq.refl