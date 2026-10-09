import TightVer401.QuadraticRadialFillingGradientJordan
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Actual target nesting from a bounded Jordan boundary. The identity-map
maximum principle is applied on the target disk, so no regularity of its
Schoenflies homeomorphism is assumed. -/
namespace TightVer401
noncomputable section
open Set Metric Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Pointwise

/-- A genuine bounded Jordan boundary controls its whole filled closed disk. -/
theorem quadraticRadialFilling_closedDisk_subset_ball
    (Γ : ℂ ≃ₜ ℂ) {B C : ℝ}
    (hboundary : Γ '' sphere (0 : ℂ) 1 ⊆ ball (0 : ℂ) B) (hBC : B < C) :
    Γ '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) C := by
  let Ω : Set ℂ := Γ '' ball (0 : ℂ) 1
  have hclosure : closure Ω = Γ '' closedBall (0 : ℂ) 1 := by
    dsimp [Ω]
    rw [← Γ.image_closure, closure_ball _ one_ne_zero]
  have hfrontier : frontier Ω = Γ '' sphere (0 : ℂ) 1 := by
    dsimp [Ω]
    rw [← Γ.image_frontier, frontier_ball _ one_ne_zero]
  have hcompact : IsCompact (closure Ω) := by
    rw [hclosure]
    exact (isCompact_closedBall (0 : ℂ) 1).image Γ.continuous
  have hbound : ∀ z ∈ frontier Ω, ‖(id : ℂ → ℂ) z‖ ≤ B := by
    intro z hz
    have hb := hboundary (hfrontier ▸ hz)
    exact (show ‖z‖ < B by simpa only [mem_ball, dist_zero_right] using hb).le
  intro z hz
  have hn : ‖z‖ ≤ B := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcompact.isBounded.subset subset_closure)
    (differentiable_id.diffContOnCl : DiffContOnCl ℂ (id : ℂ → ℂ) Ω)
    hbound (hclosure.symm ▸ hz)
  simpa only [mem_ball, dist_zero_right] using hn.trans_lt hBC

/-- An actual homeomorphism filling of the round gradient image circle. -/
def quadraticRadialFillingRoundFilling (C : ℝ) (hC : 0 < C) : ℂ ≃ₜ ℂ :=
  Homeomorph.smulOfNeZero C hC.ne'

theorem quadraticRadialFillingRoundFilling_ball (C : ℝ) (hC : 0 < C) :
    quadraticRadialFillingRoundFilling C hC '' ball (0 : ℂ) 1 = ball (0 : ℂ) C := by
  change (fun z : ℂ => C • z) '' ball (0 : ℂ) 1 = ball (0 : ℂ) C
  rw [image_smul, smul_unitBall_of_pos hC]

theorem quadraticRadialFillingRoundFilling_sphere (C : ℝ) (hC : 0 < C) :
    quadraticRadialFillingRoundFilling C hC '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) C := by
  change (fun z : ℂ => C • z) '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) C
  rw [image_smul, smul_sphere' hC.ne', smul_zero, Real.norm_of_nonneg hC.le, mul_one]

/-- The strict nesting is inside a genuine specified round filling. -/
theorem quadraticRadialFilling_closedDisk_nested_round
    (Γ : ℂ ≃ₜ ℂ) {B C : ℝ} (hC : 0 < C)
    (hboundary : Γ '' sphere (0 : ℂ) 1 ⊆ ball (0 : ℂ) B) (hBC : B < C) :
    Γ '' closedBall (0 : ℂ) 1 ⊆
      quadraticRadialFillingRoundFilling C hC '' ball (0 : ℂ) 1 := by
  rw [quadraticRadialFillingRoundFilling_ball]
  exact quadraticRadialFilling_closedDisk_subset_ball Γ hboundary hBC

/-- Convert the actual Cartesian gradient bound into strict nesting of its
Schoenflies disk inside the larger actual round gradient image. -/
theorem quadraticRadialFillingGradient_closedDisk_nested_round
    {F : Coord → ℝ} {S B C : ℝ} {Γ : ℂ ≃ₜ ℂ} (hC : 0 < C)
    (hboundary : range (quadraticRadialFillingGradientComplexTrace F S) =
      Γ '' sphere (0 : ℂ) 1)
    (hbound : ∀ s, planarRadius (quadraticRadialFillingGradientTrace F S s) < B)
    (hBC : B < C) :
    Γ '' closedBall (0 : ℂ) 1 ⊆
      quadraticRadialFillingRoundFilling C hC '' ball (0 : ℂ) 1 := by
  apply quadraticRadialFilling_closedDisk_nested_round Γ hC _ hBC
  rw [← hboundary]
  rintro z ⟨s,rfl⟩
  rw [mem_ball, dist_zero_right]
  change ‖angularDescentComplex (quadraticRadialFillingGradientTrace F S s)‖ < B
  rw [angularDescentComplex_norm]
  exact hbound s

end
end TightVer401
