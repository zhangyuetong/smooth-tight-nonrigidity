import TightVer401.PeriodicComplexJordan
import Mathlib.Algebra.Group.Int.Units

/-! Pure deck-period algebra and interval injectivity for actual circle lifts.
No degree, winding, embedding, or local inverse conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set Function

/-- Iteration of an actual affine deck period, including negative integers. -/
theorem quadraticRadialFilling_lift_add_int_mul
    {D : ℝ → ℝ} {P B : ℝ} (hP : P ≠ 0)
    (hD : ∀ s, D (s + P) = D s + B) (k : ℤ) (s : ℝ) :
    D (s + (k : ℝ) * P) = D s + (k : ℝ) * B := by
  let E : ℝ → ℝ := fun t => D t - (B / P) * t
  have hratio : (B / P) * P = B := div_mul_cancel₀ B hP
  have hE : Function.Periodic E P := by
    intro t
    dsimp [E]
    rw [hD t]
    calc
      D t + B - B / P * (t + P) =
          D t - B / P * t + (B - (B / P) * P) := by ring
      _ = D t - B / P * t := by rw [hratio]; ring
  have he := hE.int_mul k s
  change D (s + (k : ℝ) * P) - (B / P) * (s + (k : ℝ) * P) =
    D s - (B / P) * s at he
  have hlin : (B / P) * (s + (k : ℝ) * P) =
      (B / P) * s + (k : ℝ) * B := by
    calc
      (B / P) * (s + (k : ℝ) * P) =
          (B / P) * s + (k : ℝ) * ((B / P) * P) := by ring
      _ = (B / P) * s + (k : ℝ) * B := by rw [hratio]
  rw [hlin] at he
  linarith

/-- Actual composition and actual unit direction increment force deck multiplicity one. -/
theorem quadraticRadialFilling_lift_multiplicity_product
    {U D φ : ℝ → ℝ} {L c : ℝ} {k d : ℤ}
    (hU : ∀ t, U (t + L) = U t + (2 * Real.pi) * (k : ℝ))
    (hD : ∀ s, D (s + 2 * Real.pi) = D s + (2 * Real.pi) * (d : ℝ))
    (hφ : ∀ t, φ t = D (U t) + c)
    (hturn : φ L = φ 0 + 2 * Real.pi) : k * d = 1 := by
  have hUL : U L = U 0 + (k : ℝ) * (2 * Real.pi) := by
    simpa only [zero_add, mul_comm] using hU 0
  have hDL := quadraticRadialFilling_lift_add_int_mul
    Real.two_pi_pos.ne' hD k (U 0)
  have hinc : φ L = φ 0 + (k : ℝ) * ((2 * Real.pi) * (d : ℝ)) := by
    rw [hφ L, hφ 0, hUL, hDL]
    ring
  have he : (2 * Real.pi) * ((k : ℝ) * (d : ℝ)) = (2 * Real.pi) * 1 := by
    calc
      (2 * Real.pi) * ((k : ℝ) * (d : ℝ)) =
          (k : ℝ) * ((2 * Real.pi) * (d : ℝ)) := by ring
      _ = 2 * Real.pi := by linarith [hinc, hturn]
      _ = (2 * Real.pi) * 1 := by ring
  have hreal : (k : ℝ) * (d : ℝ) = 1 := mul_left_cancel₀ Real.two_pi_pos.ne' he
  exact_mod_cast hreal

/-- Both signs are derived from the actual product, rather than supplied winding values. -/
theorem quadraticRadialFilling_lift_multiplicity_units
    {k d : ℤ} (hkd : k * d = 1) :
    (k = 1 ∧ d = 1) ∨ (k = -1 ∧ d = -1) :=
  Int.eq_one_or_neg_one_of_mul_eq_one' hkd

/-- A monotone actual real lift with one unit endpoint increment projects injectively. -/
theorem quadraticRadialFilling_circle_exp_lift_injOn
    {U : ℝ → ℝ} {L A : ℝ} (hL : 0 < L)
    (hmono : StrictMono U ∨ StrictAnti U)
    (hend : U L = U 0 + A) (hA : |A| = 2 * Real.pi) :
    InjOn (fun t => Circle.exp (U t)) (Ico 0 L) := by
  rcases hmono with hm | hm
  · have ha : 0 < A := by
      have hh := hm hL
      rw [hend] at hh
      linarith
    have hstep : A = 2 * Real.pi := by rwa [abs_of_pos ha] at hA
    have hmem {t : ℝ} (ht : t ∈ Ico 0 L) :
        U t ∈ Ico (U 0) (U 0 + 2 * Real.pi) := by
      refine ⟨hm.monotone ht.1, ?_⟩
      simpa only [hend, hstep] using hm ht.2
    intro s hs t ht he
    apply hm.injective
    exact Circle.exp_injOn_Ico (a := U 0) (b := U 0 + 2 * Real.pi)
      (by simp) (hmem hs) (hmem ht) he
  · have ha : A < 0 := by
      have hh := hm hL
      rw [hend] at hh
      linarith
    have hstep : -A = 2 * Real.pi := by rwa [abs_of_neg ha] at hA
    have hmem {t : ℝ} (ht : t ∈ Ico 0 L) : U t ∈ Ioc (U L) (U 0) := by
      exact ⟨hm ht.2, hm.antitone ht.1⟩
    intro s hs t ht he
    apply hm.injective
    exact Circle.exp_injOn_Ioc (a := U L) (b := U 0)
      (by rw [hend]; linarith [hstep]) (hmem hs) (hmem ht) he

/-- Transfer the actual lift's interval injection through an ordinary injective circle map. -/
theorem quadraticRadialFilling_trace_injOn_of_unit_lift
    {V : Type*} {γ : ℝ → V} {Γ : Circle → V} {U : ℝ → ℝ} {L A : ℝ}
    (hL : 0 < L) (hmono : StrictMono U ∨ StrictAnti U)
    (hend : U L = U 0 + A) (hA : |A| = 2 * Real.pi)
    (hΓ : Injective Γ) (hγ : ∀ t, γ t = Γ (Circle.exp (U t))) :
    InjOn γ (Ico 0 L) := by
  intro s hs t ht he
  apply quadraticRadialFilling_circle_exp_lift_injOn hL hmono hend hA hs ht
  apply hΓ
  rw [← hγ s, ← hγ t]
  exact he

/-- The composition increment first derives unit deck multiplicity, then actual trace injection. -/
theorem quadraticRadialFilling_trace_injOn_of_lift_composition
    {V : Type*} {γ : ℝ → V} {Γ : Circle → V}
    {U D φ : ℝ → ℝ} {L c : ℝ} {k d : ℤ}
    (hL : 0 < L) (hmono : StrictMono U ∨ StrictAnti U)
    (hU : ∀ t, U (t + L) = U t + (2 * Real.pi) * (k : ℝ))
    (hD : ∀ s, D (s + 2 * Real.pi) = D s + (2 * Real.pi) * (d : ℝ))
    (hφ : ∀ t, φ t = D (U t) + c)
    (hturn : φ L = φ 0 + 2 * Real.pi)
    (hΓ : Injective Γ) (hγ : ∀ t, γ t = Γ (Circle.exp (U t))) :
    InjOn γ (Ico 0 L) := by
  have hkd := quadraticRadialFilling_lift_multiplicity_product hU hD hφ hturn
  have hsign := Int.eq_one_or_neg_one_of_mul_eq_one hkd
  have hA : |(2 * Real.pi) * (k : ℝ)| = 2 * Real.pi := by
    rcases hsign with hk | hk
    · rw [hk]
      simp [abs_of_pos Real.two_pi_pos]
    · rw [hk]
      simp [abs_of_pos Real.two_pi_pos]
  exact quadraticRadialFilling_trace_injOn_of_unit_lift hL hmono
    (by simpa only [zero_add] using hU 0) hA hΓ hγ

end
end TightVer401
