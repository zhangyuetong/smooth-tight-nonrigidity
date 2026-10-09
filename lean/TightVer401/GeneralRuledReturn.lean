import TightVer401.GeneralRuledGeometry
import TightVer401.RiccatiUniqueness

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def generalRuledLinearCoefficient (c e : ℝ → Ambient) : ℝ → ℝ :=
  generalRuledQ₁ (deriv c) e (deriv e) (deriv (deriv c)) (deriv (deriv e))

def generalRuledQuadraticCoefficient (c e : ℝ → Ambient) : ℝ → ℝ :=
  generalRuledQ₂ (deriv c) e (deriv e) (deriv (deriv e))

def generalRuledTrajectory (c e : ℝ → Ambient) (u : ℝ) : ℝ → ℝ :=
  riccatiTrajectory (riccatiA (generalRuledLinearCoefficient c e))
    (riccatiV (generalRuledLinearCoefficient c e) (generalRuledQuadraticCoefficient c e)) u

def generalRuledReturn (c e : ℝ → Ambient) (L : ℝ) : ℝ → ℝ :=
  mobiusReturn (Real.exp (riccatiA (generalRuledLinearCoefficient c e) L))
    (riccatiV (generalRuledLinearCoefficient c e) (generalRuledQuadraticCoefficient c e) L)

theorem general_ruled_flow_over_period {c e : ℝ → Ambient}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0)
    (hcentral : ∀ s, secondFundamental (ruledMap c e)
      (generalRuledNormal (deriv c) e (deriv e) (![s, 0] : Coord)) (![s, 0] : Coord) 0 0 = 0)
    (L : ℝ) :
    ∃ δ > 0, ∀ x : ℝ, |x| < δ →
      generalRuledTrajectory c e x 0 = x ∧
      (∀ t ∈ Icc 0 L, HasDerivAt (generalRuledTrajectory c e x)
        (generalRuledLinearCoefficient c e t * generalRuledTrajectory c e x t +
          generalRuledQuadraticCoefficient c e t * (generalRuledTrajectory c e x t)^2) t) ∧
      (∀ t ∈ Icc 0 L,
        let p : Coord := ![t, generalRuledTrajectory c e x t]
        let v : Coord := deriv (fun r => (![r, generalRuledTrajectory c e x r] : Coord)) t
        dotProduct v ((secondFundamental (ruledMap c e)
          (generalRuledNormal (deriv c) e (deriv e) p) p).mulVec v) = 0) ∧
      generalRuledTrajectory c e x L = generalRuledReturn c e L x := by
  obtain ⟨h₁, h₂⟩ := general_ruled_actual_coefficients_contDiff hc he hδ
  obtain ⟨δ, hδpos, hflow⟩ := riccati_flow_over_period L h₁ h₂
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  obtain ⟨hinitial, hd, hreturn⟩ := hflow x hx
  refine ⟨hinitial, hd, ?_, hreturn⟩
  intro t ht
  dsimp only
  have hd' : HasDerivAt (generalRuledTrajectory c e x)
      (generalRuledLinearCoefficient c e t * generalRuledTrajectory c e x t +
        generalRuledQuadraticCoefficient c e t * (generalRuledTrajectory c e x t)^2) t := hd t ht
  rw [(ruled_graph_hasDerivAt hd').deriv]
  exact (general_ruled_actual_riccati hc he hδ hcentral _ _).mpr rfl

theorem general_ruled_return_of_asymptotic_curve {c e : ℝ → Ambient} {L : ℝ}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0)
    (hcentral : ∀ s, secondFundamental (ruledMap c e)
      (generalRuledNormal (deriv c) e (deriv e) (![s, 0] : Coord)) (![s, 0] : Coord) 0 0 = 0)
    (hL : 0 ≤ L) :
    ∃ δ > 0, ∀ u : ℝ → ℝ, |u 0| < δ →
      (∀ t ∈ Icc 0 L, HasDerivAt u (deriv u t) t) →
      (∀ t ∈ Icc 0 L,
        let p : Coord := ![t, u t]
        let v : Coord := deriv (fun r => (![r, u r] : Coord)) t
        dotProduct v ((secondFundamental (ruledMap c e)
          (generalRuledNormal (deriv c) e (deriv e) p) p).mulVec v) = 0) →
      u L = generalRuledReturn c e L (u 0) := by
  obtain ⟨δ, hδpos, hflow⟩ := general_ruled_flow_over_period hc he hδ hcentral L
  refine ⟨δ, hδpos, fun u hu hud hasym => ?_⟩
  obtain ⟨hinitial, htd, _, hreturn⟩ := hflow (u 0) hu
  obtain ⟨h₁, h₂⟩ := general_ruled_actual_coefficients_contDiff hc he hδ
  have hud' : ∀ t ∈ Icc 0 L, HasDerivAt u
      (generalRuledLinearCoefficient c e t * u t + generalRuledQuadraticCoefficient c e t * (u t)^2) t := by
    intro t ht
    have h := hasym t ht
    dsimp only at h
    rw [(ruled_graph_hasDerivAt (hud t ht)).deriv] at h
    have heq := (general_ruled_actual_riccati hc he hδ hcentral _ _).mp h
    simpa only [heq, Matrix.cons_val_zero, Matrix.cons_val_one,
      generalRuledLinearCoefficient, generalRuledQuadraticCoefficient] using hud t ht
  have heq := riccati_solutions_unique hL h₁.continuous.continuousOn h₂.continuous.continuousOn
    (HasDerivAt.continuousOn hud') (HasDerivAt.continuousOn htd) hud' htd hinitial.symm
  exact (heq ⟨hL, le_rfl⟩).trans hreturn

theorem general_ruled_return_identity_iff (c e : ℝ → Ambient) (L : ℝ) :
    ((generalRuledReturn c e L =ᶠ[𝓝 0] (fun u => u)) ↔
      Real.exp (riccatiA (generalRuledLinearCoefficient c e) L) = 1 ∧
        riccatiV (generalRuledLinearCoefficient c e) (generalRuledQuadraticCoefficient c e) L = 0) ∧
    ((generalRuledReturn c e L =ᶠ[𝓝 0] (fun u => u)) ↔
      deriv (generalRuledReturn c e L) 0 = 1 ∧ deriv (deriv (generalRuledReturn c e L)) 0 = 0) := by
  refine ⟨mobiusReturn_identity_germ_iff _ _, ?_⟩
  exact (mobiusReturn_identity_germ_iff _ _).trans (mobiusReturn_two_jet_criterion _ _).symm

end
end TightVer401
