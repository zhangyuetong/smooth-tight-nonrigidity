import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Algebraic and connectedness ingredients for the positive-curvature orientation
argument. These declarations make no geometric or tightness assumptions. -/
namespace TightVer401
noncomputable section
open Set Matrix

/-- A real symmetric two-by-two matrix with positive determinant has nonzero trace. -/
theorem real_two_matrix_trace_ne_zero_of_det_pos
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hsymm : B.IsSymm)
    (hdet : 0 < B.det) : B.trace ≠ 0 := by
  intro hzero
  have hoff : B 1 0 = B 0 1 := hsymm.apply 0 1
  rw [Matrix.trace_fin_two] at hzero
  have hdiag : B 1 1 = -(B 0 0) := by linarith
  rw [Matrix.det_fin_two, hoff, hdiag] at hdet
  nlinarith [sq_nonneg (B 0 0), sq_nonneg (B 0 1)]

/-- Continuity of a matrix family gives continuity of its actual trace. -/
theorem real_two_matrix_continuousOn_trace
    {A : Type*} [TopologicalSpace A] {s : Set A}
    (B : A → Matrix (Fin 2) (Fin 2) ℝ) (hB : ContinuousOn B s) :
    ContinuousOn (fun x => (B x).trace) s := by
  have h00 : ContinuousOn (fun x => B x 0 0) s :=
    (continuous_apply 0).comp_continuousOn
      ((continuous_apply 0).comp_continuousOn hB)
  have h11 : ContinuousOn (fun x => B x 1 1) s :=
    (continuous_apply 1).comp_continuousOn
      ((continuous_apply 1).comp_continuousOn hB)
  convert! h00.add h11 using 1
  funext x
  exact Matrix.trace_fin_two (B x)

/-- A continuous nonvanishing scalar has the same positive sign at all points of
one preconnected set. -/
theorem preconnected_scalar_pos_iff_of_ne_zero
    {A : Type*} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s)
    (f : A → ℝ) (hf : ContinuousOn f s) (hne : ∀ x ∈ s, f x ≠ 0)
    {x y : A} (hx : x ∈ s) (hy : y ∈ s) : 0 < f x ↔ 0 < f y := by
  have hforward : ∀ a ∈ s, ∀ b ∈ s, 0 < f a → 0 < f b := by
    intro a ha b hb hpos
    by_contra hnotpos
    have hle : f b ≤ 0 := le_of_not_gt hnotpos
    obtain ⟨z, hz, hzero⟩ := hs.intermediate_value hb ha hf
      (show (0 : ℝ) ∈ Icc (f b) (f a) from ⟨hle, hpos.le⟩)
    exact hne z hz hzero
  exact ⟨hforward x hx y hy, hforward y hy x hx⟩

/-- On a preconnected set of real symmetric positive-determinant matrices,
trace positivity is independent of the chosen point. -/
theorem real_two_matrix_trace_pos_iff_on_preconnected
    {A : Type*} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s)
    (B : A → Matrix (Fin 2) (Fin 2) ℝ) (hB : ContinuousOn B s)
    (hsymm : ∀ x ∈ s, (B x).IsSymm) (hdet : ∀ x ∈ s, 0 < (B x).det)
    {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
    0 < (B x).trace ↔ 0 < (B y).trace := by
  exact preconnected_scalar_pos_iff_of_ne_zero hs (fun x => (B x).trace)
    (real_two_matrix_continuousOn_trace B hB)
    (fun x hx => real_two_matrix_trace_ne_zero_of_det_pos (B x) (hsymm x hx) (hdet x hx))
    hx hy

/-- The sign of the trace is constant on an entire nonempty preconnected
positive-determinant symmetric matrix family. -/
theorem real_two_matrix_trace_sign_constant
    {A : Type*} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s)
    (B : A → Matrix (Fin 2) (Fin 2) ℝ) (hB : ContinuousOn B s)
    (hsymm : ∀ x ∈ s, (B x).IsSymm) (hdet : ∀ x ∈ s, 0 < (B x).det)
    (p : A) (hp : p ∈ s) :
    (∀ x ∈ s, 0 < (B x).trace) ∨ (∀ x ∈ s, (B x).trace < 0) := by
  have hne : ∀ x ∈ s, (B x).trace ≠ 0 := fun x hx =>
    real_two_matrix_trace_ne_zero_of_det_pos (B x) (hsymm x hx) (hdet x hx)
  rcases lt_or_gt_of_ne (hne p hp) with hneg | hpos
  · right
    intro x hx
    have hiff := real_two_matrix_trace_pos_iff_on_preconnected hs B hB hsymm hdet hx hp
    have hnotpos : ¬ 0 < (B x).trace := fun h => (not_lt_of_gt hneg) (hiff.mp h)
    exact lt_of_le_of_ne (le_of_not_gt hnotpos) (hne x hx)
  · left
    intro x hx
    exact (real_two_matrix_trace_pos_iff_on_preconnected hs B hB hsymm hdet hp hx).mp hpos

/-- In even dimension two, matrix negation preserves the determinant. -/
theorem real_two_matrix_det_neg (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (-B).det = B.det := by
  simp [Matrix.det_neg]

/-- Negative semidefiniteness and nondegeneracy force strictly positive
 determinant in dimension two. -/
theorem real_two_matrix_det_pos_of_neg_posSemidef_of_ne_zero
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hneg : (-B).PosSemidef)
    (hne : B.det ≠ 0) : 0 < B.det := by
  have hnonneg : 0 ≤ B.det := by
    simpa only [real_two_matrix_det_neg] using hneg.det_nonneg
  exact lt_of_le_of_ne hnonneg hne.symm

end
end TightVer401

