import TightVer401.ReturnMap

/-! Actual first and second derivatives of the two-parameter ruled return.
This implements the two-jet test, separately from its geometric ODE inputs. -/
namespace TightVer401
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def mobiusReturn (μ ν u : ℝ) : ℝ := μ * u / (1 - ν * u)

theorem mobiusReturn_hasDerivAt (μ ν u : ℝ) (h : 1 - ν * u ≠ 0) :
    HasDerivAt (mobiusReturn μ ν) (μ / (1 - ν * u)^2) u := by
  have hn : HasDerivAt (fun x : ℝ => μ * x) μ u := hasDerivAt_const_mul μ
  have hd : HasDerivAt (fun x : ℝ => 1 - ν * x) (-ν) u := by
    have h : HasDerivAt (fun x : ℝ => 1 + (-ν) * x) (-ν) u :=
      (hasDerivAt_const_mul (-ν)).const_add 1
    convert! h using 1
    funext x
    ring
  convert! hn.fun_div hd h using 1
  field_simp
  <;> ring

theorem mobiusReturn_first_jet (μ ν : ℝ) : deriv (mobiusReturn μ ν) 0 = μ := by
  simpa using (mobiusReturn_hasDerivAt μ ν 0 (by simp)).deriv

theorem mobiusReturn_hasSecondDerivAt (μ ν : ℝ) :
    HasDerivAt (deriv (mobiusReturn μ ν)) (2 * μ * ν) 0 := by
  have hd : HasDerivAt (fun u : ℝ => 1 - ν * u) (-ν) 0 := by
    have h : HasDerivAt (fun x : ℝ => 1 + (-ν) * x) (-ν) 0 :=
      (hasDerivAt_const_mul (-ν)).const_add 1
    convert! h using 1
    funext x
    ring
  have he : ∀ᶠ u in 𝓝 (0 : ℝ), 1 - ν * u ≠ 0 :=
    hd.continuousAt.eventually_ne (by simp)
  have hEq : deriv (mobiusReturn μ ν) =ᶠ[𝓝 0]
      (fun u => μ / (1 - ν * u)^2) := by
    filter_upwards [he] with u hu
    exact (mobiusReturn_hasDerivAt μ ν u hu).deriv
  have hformula : HasDerivAt (fun u : ℝ => μ / (1 - ν * u)^2) (2 * μ * ν) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) μ).fun_div (hd.pow 2) (by simp) using 1
    simp
    <;> ring
  exact hformula.congr_of_eventuallyEq hEq

theorem mobiusReturn_second_jet (μ ν : ℝ) :
    deriv (deriv (mobiusReturn μ ν)) 0 = 2 * μ * ν :=
  (mobiusReturn_hasSecondDerivAt μ ν).deriv

theorem mobiusReturn_two_jet_criterion (μ ν : ℝ) :
    (deriv (mobiusReturn μ ν) 0 = 1 ∧ deriv (deriv (mobiusReturn μ ν)) 0 = 0) ↔
    μ = 1 ∧ ν = 0 := by
  rw [mobiusReturn_first_jet, mobiusReturn_second_jet]
  constructor
  · rintro ⟨hμ, hν⟩
    refine ⟨hμ, ?_⟩
    rw [hμ] at hν
    linarith
  · rintro ⟨rfl, rfl⟩
    simp

theorem projectiveReturn_second_jet (c : ℝ) :
    deriv (deriv (projectiveReturn c)) 0 = -2 * c := by
  have h : projectiveReturn c = mobiusReturn 1 (-c) := by
    funext u
    simp [projectiveReturn, mobiusReturn]
  rw [h, mobiusReturn_second_jet]
  ring

theorem mobiusReturn_identity_germ_iff (μ ν : ℝ) :
    (mobiusReturn μ ν =ᶠ[𝓝 0] (fun u => u)) ↔ μ = 1 ∧ ν = 0 := by
  constructor
  · intro h
    apply (mobiusReturn_two_jet_criterion μ ν).mp
    exact ⟨by simpa using h.deriv_eq, by simpa using h.deriv.deriv_eq⟩
  · rintro ⟨rfl, rfl⟩
    exact Filter.Eventually.of_forall (fun u => by simp [mobiusReturn])

theorem mobiusReturn_fixed_iff (μ ν u : ℝ) (hu : u ≠ 0) (hd : 1 - ν * u ≠ 0) :
    mobiusReturn μ ν u = u ↔ μ = 1 - ν * u := by
  rw [mobiusReturn, div_eq_iff hd]
  constructor
  · intro h
    apply mul_right_cancel₀ hu
    nlinarith [h]
  · intro h
    rw [h]
    ring

theorem mobiusReturn_identity_of_two_nonzero_fixed_points
    {μ ν u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hdu : 1 - ν * u ≠ 0) (hdv : 1 - ν * v ≠ 0)
    (hfu : mobiusReturn μ ν u = u) (hfv : mobiusReturn μ ν v = v) :
    μ = 1 ∧ ν = 0 := by
  have hμu := (mobiusReturn_fixed_iff μ ν u hu hdu).mp hfu
  have hμv := (mobiusReturn_fixed_iff μ ν v hv hdv).mp hfv
  have hprod : ν * (u - v) = 0 := by nlinarith
  have hν : ν = 0 := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr huv)
  exact ⟨by simpa [hν] using hμu, hν⟩

end
end TightVer401
