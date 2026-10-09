import TightVer401.SeamCoordinateChain
import TightVer401.SeamNormalStrip

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff

def seamCoordProd : Coord ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => ℝ)
def seamComplexCoord : ℂ ≃L[ℝ] Coord := Complex.equivRealProdCLM.trans seamCoordProd.symm

def seamNormalCoordinates (γ : ℝ → ℂ) (p : Coord) : Coord :=
  seamComplexCoord (seamCurveNormalStrip γ (seamCoordProd p))

theorem seamComplexCoord_apply (z : ℂ) : seamComplexCoord z=![z.re,z.im] := by
  ext i
  fin_cases i <;> rfl

theorem seamNormalCoordinates_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (seamNormalCoordinates γ) :=
  seamComplexCoord.contDiff.comp ((seamCurveNormalStrip_contDiff hγ).comp seamCoordProd.contDiff)

theorem seamNormalCoordinates_central (γ : ℝ → ℂ) (s : ℝ) :
    seamNormalCoordinates γ (![s,0])=seamComplexCoord (γ s) := by
  simp [seamNormalCoordinates,seamCoordProd,seamCurveNormalStrip]

theorem seamNormalCoordinates_fderiv {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (s : ℝ) (v : Coord) :
    fderiv ℝ (seamNormalCoordinates γ) (![s,0]) v =
      seamComplexCoord (v 0 • deriv γ s+v 1 • (Complex.I*deriv γ s)) := by
  have hd₀ := ((seamCurveNormalStrip_contDiff hγ).differentiable (by simp) (s,0)).hasFDerivAt
  have hd₁ := hd₀.comp (![s,0] : Coord) seamCoordProd.hasFDerivAt
  have hd := seamComplexCoord.hasFDerivAt.comp (![s,0] : Coord) hd₁
  have hd' := hd.congr_of_eventuallyEq (f₁ := seamNormalCoordinates γ)
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hd'.fderiv]
  change seamComplexCoord (fderiv ℝ (seamCurveNormalStrip γ) (s,0) (seamCoordProd v))=_
  rw [seamCurveNormalStrip_fderiv hγ]
  rfl

theorem seamNormalCoordinates_jacobian {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (s : ℝ) :
    (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,0])).det=‖deriv γ s‖^2 := by
  have hc (a i : Fin 2) : seamCoordinateJacobian (seamNormalCoordinates γ) (![s,0]) a i =
      (seamComplexCoord ((Pi.single i (1 : ℝ) : Coord) 0 • deriv γ s+
        (Pi.single i (1 : ℝ) : Coord) 1 • (Complex.I*deriv γ s))) a := by
    unfold seamCoordinateJacobian
    rw [seam_coordPartial_component (seamNormalCoordinates_contDiff hγ)]
    change (fderiv ℝ (seamNormalCoordinates γ) (![s,0]) (Pi.single i 1)) a=_
    rw [seamNormalCoordinates_fderiv hγ]
  rw [Matrix.det_fin_two]
  simp [hc,seamComplexCoord_apply,Complex.mul_re,Complex.mul_im]
  rw [Complex.sq_norm,Complex.normSq_apply]

theorem seamNormalCoordinates_regular {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (s : ℝ) (hs : deriv γ s ≠ 0) :
    (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,0])).det ≠ 0 := by
  rw [seamNormalCoordinates_jacobian hγ]
  exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hs))

end
end TightVer401
