import TightVer401.RuledVectorNecessity
import TightVer401.RuledKernelRepresentation
import TightVer401.BandCutoff

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem supported_ruled_vector_has_profile {L b lower upper cb : ℝ}
    (d : PeriodicRuledFrame L) {Y : Coord → Ambient} {W : ℝ → ℝ}
    (hY : ContDiff ℝ ∞ Y) (hlower : 0 < lower) (hupper : 0 < upper) (hub : upper < b)
    (hstrain : ∀ p : Coord, 0 < p 1 → ∀ i j : Fin 2, strain (ruledMap d.γ d.E) Y p i j = 0)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ p 1 ∧ p 1 ≤ upper)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s) (hW0 : W 0 = 0)
    (hattained : ∃ s, 1 / (ruledRho d.τ s * b) - W s = cb) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ioi cb ∧
      ∀ p : Coord, 0 < p 1 → Y p = ruledProfileField d.k d.τ (ruledRho d.τ) W F d.T d.n p := by
  have he := supported_ruled_vector_reduction_global d hY hlower
    (fun q hq => hstrain q hq 1 1) (fun q hq => (hsupport q hq).1)
  have hα := frameCoefficient_contDiff hY d.smooth_T
  have hβ := frameCoefficient_contDiff hY d.smooth_n
  have hlo (q : Coord) (hq : q 1 < lower) : Y q = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => (not_le.mpr hq) (hsupport q hs).1)
  have hhi (q : Coord) (hq : upper < q 1) : Y q = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => (not_le.mpr hq) (hsupport q hs).2)
  obtain ⟨F, hFs, hFc, hbounds, hrep⟩ := supported_ruled_bending_has_profile
    d.deriv_γ d.deriv_E d.deriv_T d.deriv_n d.smooth_k d.smooth_τ d.torsion_ne_zero
    (fun q _ => hα.contDiffAt) (fun q _ => hβ.contDiffAt) d.orthonormal
    (by simpa only [← he] using hstrain) hlower hupper
    (by simpa only [← he] using hlo) (by simpa only [← he] using hhi) hW hW0
  refine ⟨F, hFs, hFc, profile_support_above_attained_cutoff hattained ?_, ?_⟩
  · intro s c hc
    exact strict_band_cutoff_of_upper_support
      (fun t => ruledRho_pos (d.torsion_ne_zero t)) hupper hub
      (fun t c hc => (hbounds t hc).1) s c hc
  · simpa only [← he] using hrep

end
end TightVer401
