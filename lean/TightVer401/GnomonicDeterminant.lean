import TightVer401.GnomonicMetric
import TightVer401.GnomonicTensor
import TightVer401.PlanarTrace

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold Matrix

theorem gnomonicSupport_endomorphism_det {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    {p : Coord} (hp : gnomonicPoint p ∈ Ω) :
    (sphereSupportEndomorphism (inducedMetric planarUnitNormal)
      (fun p => H (gnomonicPoint p)) p).det =
        planarWeight p ^ 4 * (planarHessian (gnomonicPotential H) p).det := by
  unfold sphereSupportEndomorphism
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, gnomonicSupport_tensor hH hΩ hp,
    Matrix.det_smul, gnomonic_inducedMetric_det]
  simp only [Fintype.card_fin, Ring.inverse_eq_inv]
  field_simp [ne_of_gt (planarWeight_pos p)]

theorem gnomonicSupport_saddle_iff {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    {p : Coord} (hp : gnomonicPoint p ∈ Ω) :
    (sphereSupportEndomorphism (inducedMetric planarUnitNormal)
      (fun p => H (gnomonicPoint p)) p).det < 0 ↔
        (planarHessian (gnomonicPotential H) p).det < 0 := by
  rw [gnomonicSupport_endomorphism_det hH hΩ hp]
  have hw : 0 < planarWeight p ^ 4 := pow_pos (planarWeight_pos p) 4
  simp [mul_neg_iff, hw, not_lt_of_ge hw.le]

theorem gnomonicSupport_trace_tangent {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    {p : ℝ → Coord} {t : ℝ} (ht : gnomonicPoint (p t) ∈ Ω)
    (hp : DifferentiableAt ℝ p t) :
    deriv p t ⬝ᵥ (sphereSupportTensor (inducedMetric planarUnitNormal)
      (fun p => H (gnomonicPoint p)) (p t) *ᵥ deriv p t) =
    (deriv p t ⬝ᵥ deriv (fun s => planarGradient (gnomonicPotential H) (p s)) t) /
      planarWeight (p t) := by
  have hV := hΩ.preimage gnomonicPoint_contMDiff.continuous
  rw [gnomonicSupport_tensor hH hΩ ht,
    planarTrace_gradient_deriv (gnomonicPotential_contDiffOn hH) hV ht hp]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

end
end TightVer401
