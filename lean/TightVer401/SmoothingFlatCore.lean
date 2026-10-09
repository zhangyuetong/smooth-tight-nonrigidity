import TightVer401.SmoothingModelBounds
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

def smoothingHessianState (G R : Coord → ℝ) (q : Fin 5 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => planarHessian G (![q 0,q 1]) i j +
    seamSecondJet 0 0 (2*q 2) i j * R (![q 0,q 1]) +
    (if j = 1 then q 4 else 0) * coordPartial i R (![q 0,q 1]) +
    (if i = 1 then q 4 else 0) * coordPartial j R (![q 0,q 1]) +
    q 3 * planarHessian R (![q 0,q 1]) i j

theorem smoothingHessianState_continuous {G R : Coord → ℝ}
    (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) : Continuous (smoothingHessianState G R) := by
  have hp : ContDiff ℝ ∞ (fun q : Fin 5 → ℝ => (![q 0,q 1] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hG₂ := (smoothing_partial_contDiff (smoothing_partial_contDiff hG j) i).continuous.comp hp.continuous
  have hR₂ := (smoothing_partial_contDiff (smoothing_partial_contDiff hR j) i).continuous.comp hp.continuous
  have hR₀ := hR.continuous.comp hp.continuous
  have hRᵢ := (smoothing_partial_contDiff hR i).continuous.comp hp.continuous
  have hRⱼ := (smoothing_partial_contDiff hR j).continuous.comp hp.continuous
  change Continuous (fun q : Fin 5 → ℝ => coordPartial i (coordPartial j G) (![q 0,q 1]) +
    seamSecondJet 0 0 (2*q 2) i j * R (![q 0,q 1]) +
    (if j = 1 then q 4 else 0) * coordPartial i R (![q 0,q 1]) +
    (if i = 1 then q 4 else 0) * coordPartial j R (![q 0,q 1]) +
    q 3 * coordPartial i (coordPartial j R) (![q 0,q 1]))
  have hc : Continuous (fun q : Fin 5 → ℝ => seamSecondJet 0 0 (2*q 2) i j) := by
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> fun_prop
  have hci : Continuous (fun q : Fin 5 → ℝ => if i = 1 then q 4 else 0) := by
    split_ifs <;> fun_prop
  have hcj : Continuous (fun q : Fin 5 → ℝ => if j = 1 then q 4 else 0) := by
    split_ifs <;> fun_prop
  exact ((((hG₂.add (hc.mul hR₀)).add (hcj.mul hRᵢ)).add (hci.mul hRⱼ)).add
    ((continuous_apply 3).mul hR₂))

theorem smoothingHessianState_profile {G R : Coord → ℝ}
    (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) (δ : ℝ) (hδ : 0 < δ) (s t : ℝ) :
    smoothingHessianState G R (![s,t,smoothingNormalCDF δ hδ t,
      smoothingNormalProfile δ hδ t,deriv (smoothingNormalProfile δ hδ) t]) =
      planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G R) (![s,t]) := by
  ext i j
  rw [smoothingNormalModel_hessian (smoothingNormalProfile_contDiff δ hδ) hG hR,
    smoothingNormalProfile_second_deriv]
  simp [smoothingHessianState]

/-- A genuine uniform saddle neighborhood for the constructed smooth model.
The segment hypothesis is discharged from actual endpoint jets in the next bridge. -/
theorem smoothingNormalModel_compact_core {G R : Coord → ℝ}
    (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) {K : Set ℝ} (hK : IsCompact K)
    (hsegment : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1,
      (smoothingHessianState G R (![s,0,θ,0,0])).det < 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ s ∈ K, ∀ t : ℝ, |t| ≤ δ →
      (planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G R) (![s,t])).det < 0 := by
  let center : ℝ × ℝ → (Fin 5 → ℝ) := fun z => (![z.1,0,z.2,0,0])
  have hc : Continuous center := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [center] <;> fun_prop
  let S := center '' (K ×ˢ Icc (0 : ℝ) 1)
  have hS : IsCompact S := (hK.prod isCompact_Icc).image hc
  let O : Set (Fin 5 → ℝ) := {q | (smoothingHessianState G R q).det < 0}
  have hO : IsOpen O := (smoothingHessianState_continuous hG hR).matrix_det.isOpen_preimage _ isOpen_Iio
  have hSO : S ⊆ O := by
    rintro q ⟨⟨s,θ⟩, hz, rfl⟩
    exact hsegment s hz.1 θ hz.2
  obtain ⟨ε,hε,hinc⟩ := hS.exists_thickening_subset_open hO hSO
  refine ⟨min 1 (ε/8), lt_min zero_lt_one (by positivity), fun δ hδ hsmall s hs t ht => ?_⟩
  have hd₁ : δ < 1 := hsmall.trans_le (min_le_left _ _)
  have hd₂ : 4*δ < ε := by
    have : δ < ε/8 := hsmall.trans_le (min_le_right _ _)
    linarith
  obtain ⟨hq,hd⟩ := smoothingNormalProfile_central_bounds δ hδ ht
  have hqε : |smoothingNormalProfile δ hδ t| < ε := by
    nlinarith [sq_nonneg δ]
  have hdε : |deriv (smoothingNormalProfile δ hδ) t| < ε := hd.trans_lt hd₂
  have htε : |t| < ε := ht.trans_lt (by linarith)
  let θ := smoothingNormalCDF δ hδ t
  let q : Fin 5 → ℝ := (![s,t,θ,smoothingNormalProfile δ hδ t,deriv (smoothingNormalProfile δ hδ) t])
  have hdist : dist q (center (s,θ)) < ε := by
    rw [dist_eq_norm]
    apply (pi_norm_lt_iff hε).mpr
    intro i
    fin_cases i
    · simpa [q,center] using hε
    · simpa [q,center,Real.norm_eq_abs] using htε
    · simpa [q,center] using hε
    · simpa [q,center,Real.norm_eq_abs] using hqε
    · simpa [q,center,Real.norm_eq_abs] using hdε
  have hqin : q ∈ O := hinc (Metric.mem_thickening_iff.mpr
    ⟨center (s,θ), ⟨(s,θ),⟨hs,smoothingNormalCDF_bounds δ hδ t⟩,rfl⟩,hdist⟩)
  change (smoothingHessianState G R q).det < 0 at hqin
  simpa only [q,θ,smoothingHessianState_profile hG hR] using hqin

end
end TightVer401
