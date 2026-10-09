import Mathlib.Logic.Basic

/-! Version aliases preserve the decidability instance of each upstream use. -/
theorem ite_eq_left_decidable {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

theorem ite_eq_right_decidable {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h

theorem dite_eq_left_decidable {α : Sort*} {p : Prop} [Decidable p]
    {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h

theorem dite_eq_right_decidable {α : Sort*} {p : Prop} [Decidable p]
    {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
