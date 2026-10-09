import TightVer401.GeneralRuledPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem generalRuledDelta_eq_det (c₁ e e₁ : ℝ → Ambient) (s : ℝ) :
    generalRuledDelta c₁ e e₁ s =
      Matrix.det ![fun i => c₁ s i, fun i => e s i, fun i => e₁ s i] :=
  ambientCross_triple_det _ _ _

theorem general_ruled_contDiff {c e : ℝ → Ambient}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e) : ContDiff ℝ ∞ (ruledMap c e) := by
  have ht : ContDiff ℝ ∞ (fun p : Coord => p 0) := contDiff_apply ℝ ℝ 0
  have hu : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ 1
  exact (hc.comp ht).add (hu.smul (he.comp ht))

theorem general_ruled_central_numerator_zero {c e c₁ e₁ c₂ e₂ : ℝ → Ambient} {s : ℝ}
    (hc : ∀ t, HasDerivAt c (c₁ t) t) (he : ∀ t, HasDerivAt e (e₁ t) t)
    (hc₁ : HasDerivAt c₁ (c₂ s) s) (he₁ : HasDerivAt e₁ (e₂ s) s)
    (hδ : generalRuledDelta c₁ e e₁ s ≠ 0)
    (hcentral : secondFundamental (ruledMap c e)
      (generalRuledNormal c₁ e e₁ (![s, 0] : Coord)) (![s, 0] : Coord) 0 0 = 0) :
    inner ℝ (c₂ s) (ambientCross (c₁ s) (e s)) = 0 := by
  have h := (general_ruled_second_forms (p := (![s, 0] : Coord)) hc he hc₁ he₁).1
  have hn : ‖generalRuledCross c₁ e e₁ (![s, 0] : Coord)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (general_ruled_cross_ne_zero hδ)
  rw [hcentral] at h
  have hz := (div_eq_zero_iff).mp h.symm
  have heq := hz.resolve_right hn
  simpa only [generalRuledCross, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, add_zero] using heq

theorem general_ruled_actual_riccati {c e : ℝ → Ambient}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0)
    (hcentral : ∀ s, secondFundamental (ruledMap c e)
      (generalRuledNormal (deriv c) e (deriv e) (![s, 0] : Coord)) (![s, 0] : Coord) 0 0 = 0)
    (p : Coord) (w : ℝ) :
    dotProduct (![1, w] : Coord)
      ((secondFundamental (ruledMap c e) (generalRuledNormal (deriv c) e (deriv e) p) p).mulVec ![1, w]) = 0 ↔
      w = generalRuledQ₁ (deriv c) e (deriv e) (deriv (deriv c)) (deriv (deriv e)) (p 0) * p 1 +
        generalRuledQ₂ (deriv c) e (deriv e) (deriv (deriv e)) (p 0) * (p 1)^2 := by
  have hc₁ := (contDiff_infty_iff_deriv.mp hc).2
  have he₁ := (contDiff_infty_iff_deriv.mp he).2
  have hcd := fun s => (hc.differentiable (by simp) s).hasDerivAt
  have hed := fun s => (he.differentiable (by simp) s).hasDerivAt
  have hc₁d := (hc₁.differentiable (by simp) (p 0)).hasDerivAt
  have he₁d := (he₁.differentiable (by simp) (p 0)).hasDerivAt
  have hz := general_ruled_central_numerator_zero hcd hed hc₁d he₁d (hδ (p 0)) (hcentral (p 0))
  rw [general_ruled_asymptotic_slope hcd hed hc₁d he₁d
    (general_ruled_contDiff hc he) (hδ (p 0)), general_ruled_q_polynomial hz]

theorem general_ruled_actual_coefficients_contDiff {c e : ℝ → Ambient}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0) :
    ContDiff ℝ ∞ (generalRuledQ₁ (deriv c) e (deriv e) (deriv (deriv c)) (deriv (deriv e))) ∧
    ContDiff ℝ ∞ (generalRuledQ₂ (deriv c) e (deriv e) (deriv (deriv e))) := by
  have hc₁ := (contDiff_infty_iff_deriv.mp hc).2
  have he₁ := (contDiff_infty_iff_deriv.mp he).2
  exact general_ruled_coefficients_contDiff hc₁ he he₁
    (contDiff_infty_iff_deriv.mp hc₁).2 (contDiff_infty_iff_deriv.mp he₁).2 hδ

end
end TightVer401
