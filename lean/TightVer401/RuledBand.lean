import TightVer401.GaussBridge
import Mathlib.Tactic.Module

/-! Actual coordinate differential and induced metric of the principal-normal
ruled band. A frame input is expressed by its ordinary inner products and
derivative equations, not by assumed fundamental forms. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def ruledMap (γ E : ℝ → Ambient) : Coord → Ambient :=
  fun p => γ (p 0) + p 1 • E (p 0)

def IsOrthonormalFrame (T E n : Ambient) : Prop :=
  inner ℝ T T = 1 ∧ inner ℝ E E = 1 ∧ inner ℝ n n = 1 ∧
  inner ℝ T E = 0 ∧ inner ℝ T n = 0 ∧ inner ℝ E n = 0

theorem coordPartial_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c : ℝ → V} {c' : V} {p : Coord} (hc : HasDerivAt c c' (p 0)) (i : Fin 2) :
    coordPartial i (fun q : Coord => c (q 0)) p = ((Pi.single i (1 : ℝ) : Coord) 0) • c' := by
  have h := hc.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  change fderiv ℝ (c ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ))
    p (Pi.single i 1) = _
  rw [h.fderiv]
  simp

theorem ruled_partial {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (i : Fin 2) :
    coordPartial i (ruledMap γ E) p =
      ((Pi.single i (1 : ℝ) : Coord) 0) • ((1 - k (p 0) * p 1) • T (p 0) +
        (τ (p 0) * p 1) • n (p 0)) + ((Pi.single i (1 : ℝ) : Coord) 1) • E (p 0) := by
  have hγc := hγ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hEc := hE.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hu := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have h := hγc.add (hu.smul hEc)
  have heq : (γ ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ) +
      ((ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ) : Coord → ℝ) •
        (E ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ))) = ruledMap γ E := rfl
  rw [heq] at h
  rw [coordPartial, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, Function.comp_apply]
  module

theorem ruled_partial_s {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0)) :
    coordPartial 0 (ruledMap γ E) p =
      (1 - k (p 0) * p 1) • T (p 0) + (τ (p 0) * p 1) • n (p 0) := by
  simpa using ruled_partial hγ hE 0

theorem ruled_partial_u {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0)) :
    coordPartial 1 (ruledMap γ E) p = E (p 0) := by
  simpa using ruled_partial hγ hE 1

def ruledEnergy (k τ u : ℝ) : ℝ := (1 - k * u)^2 + τ^2 * u^2

theorem ruledEnergy_pos {k τ u : ℝ} (hτ : τ ≠ 0) : 0 < ruledEnergy k τ u := by
  by_cases hu : u = 0
  · simp [ruledEnergy, hu]
  · have h := sq_pos_of_ne_zero (mul_ne_zero hτ hu)
    have h₁ := sq_nonneg (1 - k * u)
    unfold ruledEnergy
    nlinarith [h, h₁]

theorem ruled_metric_entries {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    inducedMetric (ruledMap γ E) p 0 0 = ruledEnergy (k (p 0)) (τ (p 0)) (p 1) ∧
    inducedMetric (ruledMap γ E) p 0 1 = 0 ∧
    inducedMetric (ruledMap γ E) p 1 0 = 0 ∧
    inducedMetric (ruledMap γ E) p 1 1 = 1 := by
  rcases hf with ⟨hTT, hEE, hnn, hTE, hTn, hEn⟩
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  have hnE : inner ℝ (n (p 0)) (E (p 0)) = 0 := by rw [real_inner_comm, hEn]
  have hET : inner ℝ (E (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTE]
  simp only [inducedMetric, ruled_partial_s hγ hE, ruled_partial_u hγ hE,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hTT, hEE, hnn, hTE, hTn, hEn, hnT, hnE, hET, mul_zero, mul_one,
    add_zero, zero_add, ruledEnergy]
  constructor
  · ring
  · simp

theorem ruled_metric_det {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    (inducedMetric (ruledMap γ E) p).det = ruledEnergy (k (p 0)) (τ (p 0)) (p 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := ruled_metric_entries hγ hE hf
  simp [Matrix.det_fin_two, h00, h01, h10, h11]

end
end TightVer401
