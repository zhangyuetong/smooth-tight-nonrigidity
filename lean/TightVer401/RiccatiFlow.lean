import TightVer401.RiccatiTransport
import TightVer401.RuledFlow

/-! The two Riccati primitives are actual OpenAI interval integrals. Their
explicit flow exists for small initial data over a full compact circuit,
including the zero solution. -/
namespace TightVer401
noncomputable section
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def riccatiA (q₁ : ℝ → ℝ) : ℝ → ℝ := rawPrimitive q₁

def riccatiV (q₁ q₂ : ℝ → ℝ) : ℝ → ℝ :=
  rawPrimitive (fun t => q₂ t * Real.exp (riccatiA q₁ t))

def riccatiTrajectory (A V : ℝ → ℝ) (u : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (A t) * u / (1 - u * V t)

theorem riccatiA_hasDerivAt {q₁ : ℝ → ℝ} (h₁ : Continuous q₁) (t : ℝ) :
    HasDerivAt (riccatiA q₁) (q₁ t) t := rawPrimitive_hasDerivAt h₁ t

theorem riccatiA_contDiff {q₁ : ℝ → ℝ} (h₁ : ContDiff ℝ ∞ q₁) :
    ContDiff ℝ ∞ (riccatiA q₁) := rawPrimitive_contDiff h₁

theorem riccatiV_contDiff {q₁ q₂ : ℝ → ℝ}
    (h₁ : ContDiff ℝ ∞ q₁) (h₂ : ContDiff ℝ ∞ q₂) :
    ContDiff ℝ ∞ (riccatiV q₁ q₂) :=
  rawPrimitive_contDiff (h₂.mul (riccatiA_contDiff h₁).exp)

theorem riccatiV_hasDerivAt {q₁ q₂ : ℝ → ℝ}
    (h₁ : ContDiff ℝ ∞ q₁) (h₂ : ContDiff ℝ ∞ q₂) (t : ℝ) :
    HasDerivAt (riccatiV q₁ q₂) (q₂ t * Real.exp (riccatiA q₁ t)) t :=
  rawPrimitive_hasDerivAt (h₂.mul (riccatiA_contDiff h₁).exp).continuous t

theorem riccatiA_zero (q₁ : ℝ → ℝ) : riccatiA q₁ 0 = 0 := by
  simp [riccatiA, rawPrimitive]

theorem riccatiV_zero (q₁ q₂ : ℝ → ℝ) : riccatiV q₁ q₂ 0 = 0 := by
  simp [riccatiV, rawPrimitive]

theorem riccatiTrajectory_initial {A V : ℝ → ℝ} (hA : A 0 = 0) (hV : V 0 = 0)
    (u : ℝ) : riccatiTrajectory A V u 0 = u := by
  simp [riccatiTrajectory, hA, hV]

theorem riccatiTrajectory_central (A V : ℝ → ℝ) (t : ℝ) :
    riccatiTrajectory A V 0 t = 0 := by simp [riccatiTrajectory]

theorem riccatiTrajectory_hasDerivAt {A V : ℝ → ℝ} {u t q₁ q₂ : ℝ}
    (hA : HasDerivAt A q₁ t) (hV : HasDerivAt V (q₂ * Real.exp (A t)) t)
    (hd : 1 - u * V t ≠ 0) :
    HasDerivAt (riccatiTrajectory A V u)
      (q₁ * riccatiTrajectory A V u t + q₂ * (riccatiTrajectory A V u t)^2) t := by
  have hn := hA.exp.mul_const u
  have hden := (hV.const_mul u).const_sub 1
  convert! hn.fun_div hden hd using 1
  dsimp only [riccatiTrajectory]
  field_simp
  <;> ring

theorem riccatiTrajectory_return (A V : ℝ → ℝ) (u L : ℝ) :
    riccatiTrajectory A V u L = mobiusReturn (Real.exp (A L)) (V L) u := by
  dsimp only [riccatiTrajectory, mobiusReturn]
  rw [mul_comm u (V L)]

theorem riccati_flow_over_period {q₁ q₂ : ℝ → ℝ} (L : ℝ)
    (h₁ : ContDiff ℝ ∞ q₁) (h₂ : ContDiff ℝ ∞ q₂) :
    ∃ δ > 0, ∀ u : ℝ, |u| < δ →
      riccatiTrajectory (riccatiA q₁) (riccatiV q₁ q₂) u 0 = u ∧
      (∀ t ∈ Set.Icc 0 L, HasDerivAt
        (riccatiTrajectory (riccatiA q₁) (riccatiV q₁ q₂) u)
        (q₁ t * riccatiTrajectory (riccatiA q₁) (riccatiV q₁ q₂) u t +
          q₂ t * (riccatiTrajectory (riccatiA q₁) (riccatiV q₁ q₂) u t)^2) t) ∧
      riccatiTrajectory (riccatiA q₁) (riccatiV q₁ q₂) u L =
        mobiusReturn (Real.exp (riccatiA q₁ L))
          (∫ t in 0..L, q₂ t * Real.exp (riccatiA q₁ t)) u := by
  obtain ⟨δ, hδ, hd⟩ := principalTrajectory_uniform_denominator
    (ρ := fun _ => 1) (W := fun t => -riccatiV q₁ q₂ t) (s := 0)
    isCompact_Icc (riccatiV_contDiff h₁ h₂).continuous.neg.continuousOn
  refine ⟨δ, hδ, fun u hu => ⟨riccatiTrajectory_initial
    (riccatiA_zero q₁) (riccatiV_zero q₁ q₂) u, ?_, ?_⟩⟩
  · intro t ht
    have hpos := hd u hu t ht
    simp only [riccatiV_zero, neg_zero, sub_zero, one_mul, mul_neg]
      at hpos
    have hden : 1 - u * riccatiV q₁ q₂ t ≠ 0 := by
      linarith
    exact riccatiTrajectory_hasDerivAt (riccatiA_hasDerivAt h₁.continuous t)
      (riccatiV_hasDerivAt h₁ h₂ t) hden
  · exact riccatiTrajectory_return _ _ u L

end
end TightVer401
