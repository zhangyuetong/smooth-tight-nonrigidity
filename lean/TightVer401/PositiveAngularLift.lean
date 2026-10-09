import TightVer401.PeriodicComplexJordan
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TightVer401
noncomputable section
open Set Function
open scoped ContDiff Topology

theorem positiveAngularLift_injOn {φ : ℝ → ℝ}
    (hpos : ∀ t, 0 < deriv φ t)
    (hshift : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) :
    InjOn (fun t => Complex.exp ((φ t : ℂ) * Complex.I)) (Ico 0 (2 * Real.pi)) := by
  have hm : StrictMono φ := strictMono_of_deriv_pos hpos
  have hbound : φ (2 * Real.pi) = φ 0 + 2 * Real.pi := by
    simpa only [zero_add] using hshift 0
  have hmem {t : ℝ} (ht : t ∈ Ico 0 (2 * Real.pi)) :
      φ t ∈ Ico (φ 0) (φ 0 + 2 * Real.pi) := by
    exact ⟨hm.monotone ht.1, (hm ht.2).trans_eq hbound⟩
  intro s hs t ht he
  apply hm.injective
  apply Circle.exp_injOn_Ico (a := φ 0) (b := φ 0 + 2 * Real.pi) (by simp)
    (hmem hs) (hmem ht)
  exact Subtype.ext he

theorem positiveAngularLift_periodic {φ : ℝ → ℝ}
    (hshift : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) :
    Function.Periodic (fun t => Complex.exp ((φ t : ℂ) * Complex.I)) (2 * Real.pi) := by
  intro t
  change Complex.exp ((φ (t + 2 * Real.pi) : ℂ) * Complex.I) =
    Complex.exp ((φ t : ℂ) * Complex.I)
  rw [hshift t]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
    add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem curve_injOn_of_positiveAngularLift {V : Type*} {f : ℝ → V}
    {A : V → ℂ} {φ : ℝ → ℝ}
    (hangle : ∀ t, A (f t) = Complex.exp ((φ t : ℂ) * Complex.I))
    (hpos : ∀ t, 0 < deriv φ t)
    (hshift : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) :
    InjOn f (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht he
  apply positiveAngularLift_injOn hpos hshift hs ht
  change Complex.exp ((φ s : ℂ) * Complex.I) = Complex.exp ((φ t : ℂ) * Complex.I)
  rw [← hangle s, ← hangle t, he]

theorem periodicComplexCurve_isJordanCurve_of_positiveAngularLift {f : ℝ → ℂ}
    {A : ℂ → ℂ} {φ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2 * Real.pi))
    (hangle : ∀ t, A (f t) = Complex.exp ((φ t : ℂ) * Complex.I))
    (hpos : ∀ t, 0 < deriv φ t)
    (hshift : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) :
    Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ f)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  exact periodicComplexCurve_isJordanCurve hf hp
    (curve_injOn_of_positiveAngularLift hangle hpos hshift)

end
end TightVer401
