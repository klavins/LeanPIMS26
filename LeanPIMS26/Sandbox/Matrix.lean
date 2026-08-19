import Mathlib

def M2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,2;3,4]

variable (ρ : ℝ)

def M3 : Matrix (Fin 40) (Fin 40) ℝ :=
  ρ • 1

def M4 := Matrix.fromBlocks M3 0 M3 M3
