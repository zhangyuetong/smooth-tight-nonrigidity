import TightVer401.ExitPositiveGraphFermiEmbedding
import TightVer401.ExitPositiveGraphFermiRegularity

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_exitPositiveGraph_embedded {ζ : ℝ → Ambient}
    {ℓ M N : Coord → ℝ} {a b : ℝ → ℝ} {U : Set Coord} {P η : ℝ}
    (hP : 0 < P) (hη : 0 < η)
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζL.lift)
    (hb : ContDiff ℝ ∞ b) (hbp : Function.Periodic b P)
    (hU : IsOpen U) (hℓ : ContDiffOn ℝ ∞ ℓ U)
    (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hℓp : ∀ t, Function.Periodic (fun r => ℓ ![r, t]) P)
    (hMp : ∀ t, Function.Periodic (fun r => M ![r, t]) P)
    (hNp : ∀ t, Function.Periodic (fun r => N ![r, t]) P)
    (hm : exitGraphMean P b ≠ 0)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, ℓ ![r, 0] = 0)
    (hMr : ∀ r ∈ Icc (0 : ℝ) P, M ![r, 0] = a r)
    (ha : ∀ r ∈ Icc (0 : ℝ) P, 0 < a r)
    (hℓt : ∀ r ∈ Icc (0 : ℝ) P, coordPartial 1 ℓ ![r, 0] = -2 * a r * b r) :
    letI : Fact (0 < P) := ⟨hP⟩
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < η ∧ δ * exitGraphMean P b < 0 ∧
      Topology.IsEmbedding (fermiNativeSphereGraph hζ hζL hunit hspeed
        (exitPositiveGraphProfile_periodic hP hb hbp) δ) ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fermiNativeSphereGraph hζ hζL hunit hspeed
        (exitPositiveGraphProfile_periodic hP hb hbp) δ) ∧
      (∀ r, deriv (fermiNormalMap ζ ∘ exitGraphCurve (exitPositiveGraphProfile P b) δ) r ≠ 0) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve (exitPositiveGraphProfile P b) δ r ∈ U) ∧
      ∀ r, 0 < dotProduct (deriv (exitGraphCurve (exitPositiveGraphProfile P b) δ) r)
        (!![ℓ (exitGraphCurve (exitPositiveGraphProfile P b) δ r),
          M (exitGraphCurve (exitPositiveGraphProfile P b) δ r);
          M (exitGraphCurve (exitPositiveGraphProfile P b) δ r),
          N (exitGraphCurve (exitPositiveGraphProfile P b) δ r)] *ᵥ
          deriv (exitGraphCurve (exitPositiveGraphProfile P b) δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  have hv := exitPositiveGraphProfile_contDiff (P := P) hb
  have hvL := exitPositiveGraphProfile_periodic hP hb hbp
  obtain ⟨ρ, hρ, he⟩ := fermiNativeSphereGraph_exists_embedding_radius hζ hζL hunit hspeed hi hv hvL
  obtain ⟨τ, hτ, hr⟩ := fermiGraph_exists_regular_radius hP hζ hζL hv hvL hunit hspeed
  obtain ⟨δ, hd, hdsmall, hsign, hdom, hpos⟩ :=
    exists_exitPositiveGraph_arbitrarily_small hP (lt_min hη (lt_min hρ hτ)) hb hbp
      hU hℓ hM hN hℓp hMp hNp hm hseam hzero hMr ha hℓt
  have hdη : |δ| < η := lt_of_lt_of_le hdsmall (min_le_left _ _)
  have hdρ : |δ| < ρ := lt_of_lt_of_le hdsmall
    ((min_le_right _ _).trans (min_le_left _ _))
  have hdτ : |δ| < τ := lt_of_lt_of_le hdsmall
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hd, hdη, hsign, he δ hdρ,
    fermiNativeSphereGraph_contMDiff hζ hζL hunit hspeed hv hvL δ,
    fun r => (hr δ hdτ r).2, hdom, ?_⟩
  intro r
  rw [← exitGraphQuadratic_actual_tangent hv δ r]
  exact hpos r

end
end TightVer401
