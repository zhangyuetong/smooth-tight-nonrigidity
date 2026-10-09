import OAI.Geometry.IsometricImmersion.Calculus.CoordinateDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Spatial coordinate derivatives of a genuinely joint parameter family.
The definition uses the actual joint Frechet derivative; the affine-slice
chain rule identifies it with OpenAI's actual coordinate partial. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spatial partial of the actual jointly defined parameter family. -/
def bandBendingParameterCoordPartial (i : Fin 2) (f : ℝ × Coord → V)
    (z : ℝ × Coord) : V :=
  fderiv ℝ f z (0, Pi.single i 1)

/-- Actual affine-slice chain rule; differentiability at the joint point suffices. -/
theorem bandBendingParameterCoordPartial_eq_slice {f : ℝ × Coord → V}
    {a : ℝ} {p : Coord} (hf : DifferentiableAt ℝ f (a, p)) (i : Fin 2) :
    bandBendingParameterCoordPartial i f (a, p) =
      coordPartial i (fun q => f (a, q)) p := by
  have hs : HasFDerivAt (fun q : Coord => (a, q))
      (ContinuousLinearMap.inr ℝ ℝ Coord) p := hasFDerivAt_prodMk_right a p
  have hc : HasFDerivAt (fun q : Coord => f (a, q))
      ((fderiv ℝ f (a, p)).comp (ContinuousLinearMap.inr ℝ ℝ Coord)) p := by
    simpa only [Function.comp_def] using hf.hasFDerivAt.comp p hs
  unfold bandBendingParameterCoordPartial coordPartial
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Open joint-domain smoothness supplies the actual derivative correspondence. -/
theorem bandBendingParameterCoordPartial_eq_slice_on {f : ℝ × Coord → V}
    {W : Set (ℝ × Coord)} (hf : ContDiffOn ℝ ∞ f W) (hW : IsOpen W)
    {a : ℝ} {p : Coord} (hp : (a, p) ∈ W) (i : Fin 2) :
    bandBendingParameterCoordPartial i f (a, p) =
      coordPartial i (fun q => f (a, q)) p :=
  bandBendingParameterCoordPartial_eq_slice
    (((hf (a, p) hp).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)) i

/-- Joint smoothness of the actual spatial partial on an open joint domain. -/
theorem bandBendingParameterCoordPartial_contDiffOn {f : ℝ × Coord → V}
    {W : Set (ℝ × Coord)} (hf : ContDiffOn ℝ ∞ f W) (hW : IsOpen W)
    (i : Fin 2) : ContDiffOn ℝ ∞ (bandBendingParameterCoordPartial i f) W := by
  exact (hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const

/-- Direct smoothness for the family of OpenAI slice coordinate partials. -/
theorem bandBending_sliceCoordPartial_contDiffOn {f : ℝ × Coord → V}
    {W : Set (ℝ × Coord)} (hf : ContDiffOn ℝ ∞ f W) (hW : IsOpen W)
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => coordPartial i (fun q => f (z.1, q)) z.2) W := by
  apply (bandBendingParameterCoordPartial_contDiffOn hf hW i).congr
  intro z hz
  exact (bandBendingParameterCoordPartial_eq_slice_on hf hW hz i).symm

end
end TightVer401

