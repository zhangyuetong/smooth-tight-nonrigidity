import TightVer401.SeamCoordinateChain
import TightVer401.SmoothingFlatPatch

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def smoothingSeamShift (L : ℝ) (p : Coord) : Coord := (![p 0+L,p 1])

theorem smoothingSeamShift_contDiff (L : ℝ) : ContDiff ℝ ∞ (smoothingSeamShift L) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [smoothingSeamShift] <;> fun_prop

theorem smoothingSeamShift_hasFDerivAt (L : ℝ) (p : Coord) :
    HasFDerivAt (smoothingSeamShift L) (ContinuousLinearMap.id ℝ Coord) p := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) p).add_const (![L,0] : Coord)
  apply hd.congr_of_eventuallyEq (f₁ := smoothingSeamShift L)
  exact Eventually.of_forall (fun q => by ext i; fin_cases i <;> simp [smoothingSeamShift])

theorem smoothingSeamShift_partial (L : ℝ) (p : Coord) (i a : Fin 2) :
    coordPartial i (fun q => smoothingSeamShift L q a) p=if a=i then 1 else 0 := by
  rw [seam_coordPartial_component (smoothingSeamShift_contDiff L)]
  change (fderiv ℝ (smoothingSeamShift L) p (Pi.single i 1)) a=if a=i then 1 else 0
  rw [(smoothingSeamShift_hasFDerivAt L p).fderiv]
  fin_cases i <;> fin_cases a <;> simp

theorem smoothing_seam_partial_periodic {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (p : Coord) (i : Fin 2) :
    coordPartial i F (smoothingSeamShift L p)=coordPartial i F p := by
  have he : (fun q => F (smoothingSeamShift L q))=F := funext hperiod
  have hc := congrArg (fun f : Coord → ℝ => coordPartial i f p) he
  rw [seam_coordPartial_comp hF (smoothingSeamShift_contDiff L)] at hc
  simp only [Fin.sum_univ_two,smoothingSeamShift_partial] at hc
  fin_cases i <;> simpa using hc

theorem smoothing_seam_hessian_periodic {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (p : Coord) (i j : Fin 2) :
    planarHessian F (smoothingSeamShift L p) i j=planarHessian F p i j :=
  smoothing_seam_partial_periodic (smoothing_partial_contDiff hF j) L
    (fun q => smoothing_seam_partial_periodic hF L hperiod q j) p i

theorem smoothingFlatRemainder_periodic {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D)
    (L : ℝ) (hperiod : ∀ p, D (smoothingSeamShift L p)=D p) (p : Coord) :
    smoothingFlatRemainder D (smoothingSeamShift L p)=smoothingFlatRemainder D p := by
  unfold smoothingFlatRemainder
  apply intervalIntegral.integral_congr
  intro u _
  change (1-u)*planarHessian D (![smoothingSeamShift L p 0,u*smoothingSeamShift L p 1]) 1 1 =
    (1-u)*planarHessian D (![p 0,u*p 1]) 1 1
  have he : (![smoothingSeamShift L p 0,u*smoothingSeamShift L p 1] : Coord)=
      smoothingSeamShift L (![p 0,u*p 1]) := by
    ext i
    fin_cases i <;> rfl
  rw [he,smoothing_seam_hessian_periodic hD L hperiod]

/-- Closed seams retain the actual periodicity of both original potentials. -/
theorem smoothingFlatPatch_periodic {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (L : ℝ)
    (hperiodF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hperiodG : ∀ p, G (smoothingSeamShift L p)=G p)
    (δ : ℝ) (hδ : 0 < δ) (h : ℝ) (p : Coord) :
    smoothingFlatPatch F G δ hδ h (smoothingSeamShift L p)=smoothingFlatPatch F G δ hδ h p := by
  have hD : ∀ q, (F-G) (smoothingSeamShift L q)=(F-G) q := by
    intro q
    change F (smoothingSeamShift L q)-G (smoothingSeamShift L q)=F q-G q
    rw [hperiodF,hperiodG]
  unfold smoothingFlatPatch smoothingNormalModel
  rw [hperiodG,smoothingFlatRemainder_periodic (D := F-G) (hF.sub hG) L hD]
  rfl

end
end TightVer401
