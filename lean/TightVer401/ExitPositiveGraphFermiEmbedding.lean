import TightVer401.ExitPositiveGraphFermiTube
import TightVer401.SphereCharts

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem fermiNativeMap_norm {L : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (p : AddCircle L × ℝ) : ‖fermiNativeMap ζ hζ hζL p‖ = 1 := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
  have he : fermiNativeMap ζ hζ hζL p = fermiNormalMap ζ ![r, p.2] := by
    simp only [fermiNativeMap, ← hr, Function.Periodic.lift_coe, fermiNormalMap,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hi := fermiNormalMap_unit hζ hunit hspeed (![r, p.2] : Coord)
  rw [← he, real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (fermiNativeMap ζ hζ hζL p)]

def fermiNativeSphereMap {L : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (p : AddCircle L × ℝ) : RoundSphere :=
  ⟨fermiNativeMap ζ hζ hζL p, by simpa using fermiNativeMap_norm hζ hζL hunit hspeed p⟩

theorem fermiNativeSphereMap_contMDiff {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞
      (fermiNativeSphereMap hζ hζL hunit hspeed) := by
  exact (fermiNativeMap_contMDiff hζ hζL).codRestrict_sphere
    (fun p => by simpa using fermiNativeMap_norm hζ hζL hunit hspeed p)

def fermiNativeGraph {L : ℝ} {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hζL : Function.Periodic ζ L) {v : ℝ → ℝ} (hvL : Function.Periodic v L)
    (δ : ℝ) (q : AddCircle L) : Ambient :=
  fermiNativeMap ζ hζ hζL (q, δ * hvL.lift q)

theorem fermiNativeGraph_coe {L : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    {v : ℝ → ℝ} (hvL : Function.Periodic v L) (δ r : ℝ) :
    fermiNativeGraph hζ hζL hvL δ (periodProjection L r) =
      fermiNormalMap ζ ![r, δ * v r] := by
  simp only [fermiNativeGraph, fermiNativeMap, periodicLift_coe, fermiNormalMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem fermiNativeGraph_contMDiff {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) (δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ (fermiNativeGraph hζ hζL hvL δ) := by
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : AddCircle L => (q, δ * hvL.lift q)) :=
    contMDiff_id.prodMk (contMDiff_const.mul (periodicLift_contMDiff hv hvL))
  exact (fermiNativeMap_contMDiff hζ hζL).comp hg

def fermiNativeSphereGraph {L : ℝ} {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {v : ℝ → ℝ} (hvL : Function.Periodic v L) (δ : ℝ) (q : AddCircle L) : RoundSphere :=
  fermiNativeSphereMap hζ hζL hunit hspeed (q, δ * hvL.lift q)

theorem fermiNativeSphereGraph_contMDiff {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) (δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fermiNativeSphereGraph hζ hζL hunit hspeed hvL δ) := by
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : AddCircle L => (q, δ * hvL.lift q)) :=
    contMDiff_id.prodMk (contMDiff_const.mul (periodicLift_contMDiff hv hvL))
  exact (fermiNativeSphereMap_contMDiff hζ hζL hunit hspeed).comp hg

theorem fermiNativeGraph_exists_embedding_radius {L : ℝ} [Fact (0 < L)]
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζL.lift)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) :
    ∃ ρ > 0, ∀ δ : ℝ, |δ| < ρ → Topology.IsEmbedding (fermiNativeGraph hζ hζL hvL δ) := by
  obtain ⟨ε, hε, hinj, _⟩ := fermiNativeMap_exists_thin_embedded_strip hζ hζL hunit hspeed hi
  have hc : Continuous hvL.lift := (periodicLift_contMDiff hv hvL).continuous
  obtain ⟨q₀, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.abs.continuousOn
  let K := |hvL.lift q₀| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hb (q : AddCircle L) : |hvL.lift q| < K := by
    have hh := hmax (mem_univ q)
    change |hvL.lift q| ≤ |hvL.lift q₀| at hh
    dsimp [K]
    linarith
  refine ⟨ε / K, div_pos hε hK, fun δ hδ => ?_⟩
  have hm (q : AddCircle L) : (q, δ * hvL.lift q) ∈ univ ×ˢ Icc (-ε) ε := by
    have hd : |δ| * K < ε := (lt_div_iff₀ hK).mp hδ
    have ha : |δ * hvL.lift q| < ε := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hb q).le (abs_nonneg δ)) hd
    exact ⟨mem_univ q, (abs_le.mp ha.le)⟩
  have hiG : Function.Injective (fermiNativeGraph hζ hζL hvL δ) := by
    intro q s he
    exact congrArg Prod.fst (hinj (hm q) (hm s) he)
  exact ((fermiNativeGraph_contMDiff hζ hζL hv hvL δ).continuous.isClosedEmbedding hiG).isEmbedding

theorem fermiNativeSphereGraph_exists_embedding_radius {L : ℝ} [Fact (0 < L)]
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζL.lift)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) :
    ∃ ρ > 0, ∀ δ : ℝ, |δ| < ρ →
      Topology.IsEmbedding (fermiNativeSphereGraph hζ hζL hunit hspeed hvL δ) := by
  obtain ⟨ρ, hρ, he⟩ := fermiNativeGraph_exists_embedding_radius hζ hζL hunit hspeed hi hv hvL
  refine ⟨ρ, hρ, fun δ hδ => ?_⟩
  exact (he δ hδ).codRestrict (Metric.sphere (0 : Ambient) 1)
    (fun q => (fermiNativeSphereMap hζ hζL hunit hspeed (q, δ * hvL.lift q)).property)

end
end TightVer401
