import TightVer401.AmbientCross
import TightVer401.ScalarCoordinateCalculus

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

theorem general_ruled_partial {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0))
    (he : HasDerivAt e (e₁ (p 0)) (p 0)) (i : Fin 2) :
    coordPartial i (ruledMap c e) p =
      ((Pi.single i (1 : ℝ) : Coord) 0) • (c₁ (p 0) + p 1 • e₁ (p 0)) +
      ((Pi.single i (1 : ℝ) : Coord) 1) • e (p 0) := by
  have hcc := hc.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hec := he.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hu := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have h := hcc.add (hu.smul hec)
  change HasFDerivAt (ruledMap c e) _ p at h
  rw [coordPartial, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, Function.comp_apply]
  module

theorem general_ruled_partial_t {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0))
    (he : HasDerivAt e (e₁ (p 0)) (p 0)) :
    coordPartial 0 (ruledMap c e) p = c₁ (p 0) + p 1 • e₁ (p 0) := by
  simpa using general_ruled_partial hc he 0

theorem general_ruled_partial_u {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0))
    (he : HasDerivAt e (e₁ (p 0)) (p 0)) :
    coordPartial 1 (ruledMap c e) p = e (p 0) := by
  simpa using general_ruled_partial hc he 1

theorem general_ruled_second_tt {c e c₁ e₁ c₂ e₂ : ℝ → Ambient} {p : Coord}
    (hc : ∀ s, HasDerivAt c (c₁ s) s) (he : ∀ s, HasDerivAt e (e₁ s) s)
    (hc₁ : HasDerivAt c₁ (c₂ (p 0)) (p 0))
    (he₁ : HasDerivAt e₁ (e₂ (p 0)) (p 0)) :
    coordPartial 0 (coordPartial 0 (ruledMap c e)) p = c₂ (p 0) + p 1 • e₂ (p 0) := by
  have hpartial : coordPartial 0 (ruledMap c e) = ruledMap c₁ e₁ :=
    funext (fun q => general_ruled_partial_t (hc (q 0)) (he (q 0)))
  rw [hpartial]
  exact general_ruled_partial_t hc₁ he₁

theorem general_ruled_second_tu {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : ∀ s, HasDerivAt c (c₁ s) s) (he : ∀ s, HasDerivAt e (e₁ s) s) :
    coordPartial 0 (coordPartial 1 (ruledMap c e)) p = e₁ (p 0) ∧
    coordPartial 1 (coordPartial 1 (ruledMap c e)) p = 0 := by
  have hpartial : coordPartial 1 (ruledMap c e) = fun q => e (q 0) :=
    funext (fun q => general_ruled_partial_u (hc (q 0)) (he (q 0)))
  rw [hpartial]
  constructor <;> simp [coordPartial_curve (he (p 0))]

def generalRuledCross (c₁ e e₁ : ℝ → Ambient) (p : Coord) : Ambient :=
  ambientCross (c₁ (p 0) + p 1 • e₁ (p 0)) (e (p 0))

def generalRuledDelta (c₁ e e₁ : ℝ → Ambient) (s : ℝ) : ℝ :=
  inner ℝ (e₁ s) (ambientCross (c₁ s) (e s))

theorem general_ruled_mixed_numerator (c₁ e e₁ : ℝ → Ambient) (p : Coord) :
    inner ℝ (e₁ (p 0)) (generalRuledCross c₁ e e₁ p) = generalRuledDelta c₁ e e₁ (p 0) := by
  simp only [generalRuledCross, ambientCross_add_left, ambientCross_smul_left,
    inner_add_right, real_inner_smul_right, ambientCross_orthogonal_left,
    mul_zero, add_zero, generalRuledDelta]

theorem general_ruled_cross_ne_zero {c₁ e e₁ : ℝ → Ambient} {p : Coord}
    (hδ : generalRuledDelta c₁ e e₁ (p 0) ≠ 0) : generalRuledCross c₁ e e₁ p ≠ 0 :=
  ambientCross_ne_zero_of_triple (c := e₁ (p 0))
    (by change inner ℝ (e₁ (p 0)) (generalRuledCross c₁ e e₁ p) ≠ 0
        rw [general_ruled_mixed_numerator]; exact hδ)

end
end TightVer401
