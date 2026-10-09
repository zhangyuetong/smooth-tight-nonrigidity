import Mathlib.Logic.Basic

/-! Compatibility with the theorem name used by OpenAI's Lean 4.34.1 source.
This is the ordinary if-positive rule, proved without additional axioms.
No upstream mathematical statement or proof is replaced.
-/
open Classical in
theorem ite_eq_left {α : Sort*} {p : Prop} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

open Classical in
theorem dite_eq_left {α : Sort*} {p : Prop} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
