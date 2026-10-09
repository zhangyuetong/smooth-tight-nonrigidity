import TightVer401.ConcaveJetJoinControl

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def jetAffineMomentVector (x : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, x]

theorem jetAffineMomentVector_contDiff : ContDiff ℝ ∞ jetAffineMomentVector := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

theorem jetAffineMoment_coordinates {h : ℝ → ℝ} (A B : ℝ)
    (hi : IntervalIntegrable (fun x => h x • jetAffineMomentVector x) volume A B) :
    (jetAccelerationMoment A B jetAffineMomentVector h) 0 = (∫ x in A..B, h x) ∧
      (jetAccelerationMoment A B jetAffineMomentVector h) 1 = (∫ x in A..B, x * h x) := by
  have he (i : Fin 2) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).intervalIntegral_comp_comm hi
  constructor
  · have h₀ := he 0
    change (∫ x in A..B, h x * jetAffineMomentVector x 0) =
      (jetAccelerationMoment A B jetAffineMomentVector h) 0 at h₀
    simpa [jetAffineMomentVector] using h₀.symm
  · have h₁ := he 1
    change (∫ x in A..B, h x * jetAffineMomentVector x 1) =
      (jetAccelerationMoment A B jetAffineMomentVector h) 1 at h₁
    simpa [jetAffineMomentVector, mul_comm] using h₁.symm

theorem jetAffineMoment_eq_iff {h k : ℝ → ℝ} (A B : ℝ)
    (hh : IntervalIntegrable (fun x => h x • jetAffineMomentVector x) volume A B)
    (hk : IntervalIntegrable (fun x => k x • jetAffineMomentVector x) volume A B) :
    jetAccelerationMoment A B jetAffineMomentVector h = jetAccelerationMoment A B jetAffineMomentVector k ↔
      (∫ x in A..B, h x) = (∫ x in A..B, k x) ∧
        (∫ x in A..B, x * h x) = (∫ x in A..B, x * k x) := by
  obtain ⟨h₀, h₁⟩ := jetAffineMoment_coordinates A B hh
  obtain ⟨k₀, k₁⟩ := jetAffineMoment_coordinates A B hk
  constructor
  · intro he
    exact ⟨h₀.symm.trans ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) he).trans k₀),
      h₁.symm.trans ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) he).trans k₁)⟩
  · rintro ⟨he₀, he₁⟩
    ext i
    fin_cases i
    · exact h₀.trans (he₀.trans k₀.symm)
    · exact h₁.trans (he₁.trans k₁.symm)

end
end TightVer401
