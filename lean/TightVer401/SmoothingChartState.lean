import TightVer401.SeamChartContinuity
import TightVer401.SmoothingFlatCore

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise

def smoothingChartHessianState (Φ : Coord → Coord) (G R : Coord → ℝ)
    (q : Fin 5 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  smoothingHessianState G R q i j -
    ∑ k : Fin 2, seamChartConnection Φ k i j (![q 0,q 1])*
      (coordPartial k G (![q 0,q 1])+(if k=1 then q 4 else 0)*R (![q 0,q 1])+
        q 3*coordPartial k R (![q 0,q 1]))

theorem smoothingChartHessianState_continuousAt {Φ : Coord → Coord} {G R : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R)
    (q : Fin 5 → ℝ) (hJ : (seamCoordinateJacobian Φ (![q 0,q 1])).det ≠ 0) :
    ContinuousAt (smoothingChartHessianState Φ G R) q := by
  have hp : Continuous (fun z : Fin 5 → ℝ => (![z 0,z 1] : Coord)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hc := (smoothingHessianState_continuous hG hR).continuousAt (x := q)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hraw : ContinuousAt (fun z => smoothingHessianState G R z i j) q :=
    (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hc)
  have hΓ (k : Fin 2) : ContinuousAt (fun z : Fin 5 → ℝ =>
      seamChartConnection Φ k i j (![z 0,z 1])) q :=
    (seamChartConnection_continuousAt (p := (![q 0,q 1] : Coord)) hΦ hJ k i j).comp
      (f := fun z : Fin 5 → ℝ => (![z 0,z 1] : Coord)) hp.continuousAt
  have hg (k : Fin 2) : Continuous (fun z : Fin 5 → ℝ =>
      coordPartial k G (![z 0,z 1])+(if k=1 then z 4 else 0)*R (![z 0,z 1])+
        z 3*coordPartial k R (![z 0,z 1])) := by
    have hG₁ := (smoothing_partial_contDiff hG k).continuous.comp hp
    have hR₁ := (smoothing_partial_contDiff hR k).continuous.comp hp
    have hR₀ := hR.continuous.comp hp
    have hi : Continuous (fun z : Fin 5 → ℝ => if k=1 then z 4 else 0) := by
      split_ifs <;> fun_prop
    exact (hG₁.add (hi.mul hR₀)).add ((continuous_apply 3).mul hR₁)
  change ContinuousAt (fun z => smoothingHessianState G R z i j-
    ∑ k : Fin 2, seamChartConnection Φ k i j (![z 0,z 1])*
      (coordPartial k G (![z 0,z 1])+(if k=1 then z 4 else 0)*R (![z 0,z 1])+
        z 3*coordPartial k R (![z 0,z 1]))) q
  simp only [Fin.sum_univ_two]
  exact hraw.sub (((hΓ 0).mul (hg 0).continuousAt).add ((hΓ 1).mul (hg 1).continuousAt))

theorem smoothingChartHessianState_model {Φ : Coord → Coord} {G R : Coord → ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R)
    (s t : ℝ) :
    smoothingChartHessianState Φ G R (![s,t,deriv (deriv f) t/2,f t,deriv f t]) =
      seamCorrectedHessian Φ (smoothingNormalModel f G R) (![s,t]) := by
  have htwo (x : ℝ) : 2*(x/2)=x := by ring
  ext i j
  unfold smoothingChartHessianState seamCorrectedHessian smoothingHessianState
  rw [smoothingNormalModel_hessian hf hG hR]
  simp [smoothingNormalModel_partial hf hG hR,htwo]

theorem seamChartConnection_symm {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ)
    (p : Coord) (k i j : Fin 2) : seamChartConnection Φ k i j p=seamChartConnection Φ k j i p := by
  have he : (fun a : Fin 2 => planarHessian (fun q => Φ q a) p i j)=
      fun a => planarHessian (fun q => Φ q a) p j i := by
    funext a
    exact planarHessian_symm ((contDiff_apply ℝ ℝ a).comp hΦ).contDiffOn isOpen_univ (Set.mem_univ p) i j
  unfold seamChartConnection
  rw [he]

theorem seamCorrectedHessian_symm {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) (p : Coord) (i j : Fin 2) :
    seamCorrectedHessian Φ F p i j=seamCorrectedHessian Φ F p j i := by
  unfold seamCorrectedHessian
  rw [planarHessian_symm hF.contDiffOn isOpen_univ (Set.mem_univ p) i j]
  simp only [seamChartConnection_symm hΦ p]

end
end TightVer401
