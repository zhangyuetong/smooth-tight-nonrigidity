import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual scalar transverse coordinates with the common normalized height
`-h * cos u`. The south and north endpoint maps are regular on actual open
intervals and point to the negative transverse side on `0 < u < π`. -/
namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Topology

def completedSaddleAnnulusSouthTransverse (h μ u : ℝ) : ℝ :=
  -2 * Real.sqrt (h / μ) * Real.sin (u / 2)

def completedSaddleAnnulusNorthTransverse (h μ u : ℝ) : ℝ :=
  -2 * Real.sqrt (h / μ) * Real.cos (u / 2)

theorem completedSaddleAnnulusSouthTransverse_contDiff (h μ : ℝ) :
    ContDiff ℝ ∞ (completedSaddleAnnulusSouthTransverse h μ) := by
  unfold completedSaddleAnnulusSouthTransverse
  exact contDiff_const.mul (contDiff_id.div_const 2).sin

theorem completedSaddleAnnulusNorthTransverse_contDiff (h μ : ℝ) :
    ContDiff ℝ ∞ (completedSaddleAnnulusNorthTransverse h μ) := by
  unfold completedSaddleAnnulusNorthTransverse
  exact contDiff_const.mul (contDiff_id.div_const 2).cos

theorem completedSaddleAnnulusSouthTransverse_hasDerivAt (h μ u : ℝ) :
    HasDerivAt (completedSaddleAnnulusSouthTransverse h μ)
      (-Real.sqrt (h / μ) * Real.cos (u / 2)) u := by
  unfold completedSaddleAnnulusSouthTransverse
  have hd := (((hasDerivAt_id u).div_const 2).sin.const_mul
    (-2 * Real.sqrt (h / μ)))
  have hc : (-2 * Real.sqrt (h / μ)) * (Real.cos (u / 2) * (1 / 2)) =
      -Real.sqrt (h / μ) * Real.cos (u / 2) := by ring
  simpa only [id_eq, hc] using hd

theorem completedSaddleAnnulusNorthTransverse_hasDerivAt (h μ u : ℝ) :
    HasDerivAt (completedSaddleAnnulusNorthTransverse h μ)
      (Real.sqrt (h / μ) * Real.sin (u / 2)) u := by
  unfold completedSaddleAnnulusNorthTransverse
  have hd := (((hasDerivAt_id u).div_const 2).cos.const_mul
    (-2 * Real.sqrt (h / μ)))
  have hc : (-2 * Real.sqrt (h / μ)) * (-Real.sin (u / 2) * (1 / 2)) =
      Real.sqrt (h / μ) * Real.sin (u / 2) := by ring
  simpa only [id_eq, hc] using hd

/-- The south transverse coordinate is regular throughout an actual open
interval containing its endpoint `u = 0`. -/
theorem completedSaddleAnnulusSouthTransverse_deriv_neg
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (hu : u ∈ Ioo (-Real.pi) Real.pi) :
    deriv (completedSaddleAnnulusSouthTransverse h μ) u < 0 := by
  rw [(completedSaddleAnnulusSouthTransverse_hasDerivAt h μ u).deriv]
  have hs : 0 < Real.sqrt (h / μ) := Real.sqrt_pos.mpr (div_pos hh hμ)
  have hc : 0 < Real.cos (u / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact mul_neg_of_neg_of_pos (by linarith) hc

theorem completedSaddleAnnulusSouthTransverse_deriv_ne_zero
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (hu : u ∈ Ioo (-Real.pi) Real.pi) :
    deriv (completedSaddleAnnulusSouthTransverse h μ) u ≠ 0 :=
  ne_of_lt (completedSaddleAnnulusSouthTransverse_deriv_neg hh hμ hu)

/-- The north transverse coordinate is regular throughout an actual open
interval containing its endpoint `u = π`. -/
theorem completedSaddleAnnulusNorthTransverse_deriv_pos
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (hu : u ∈ Ioo 0 (2 * Real.pi)) :
    0 < deriv (completedSaddleAnnulusNorthTransverse h μ) u := by
  rw [(completedSaddleAnnulusNorthTransverse_hasDerivAt h μ u).deriv]
  have hs : 0 < Real.sqrt (h / μ) := Real.sqrt_pos.mpr (div_pos hh hμ)
  have hsin : 0 < Real.sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])
  exact mul_pos hs hsin

theorem completedSaddleAnnulusNorthTransverse_deriv_ne_zero
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (hu : u ∈ Ioo 0 (2 * Real.pi)) :
    deriv (completedSaddleAnnulusNorthTransverse h μ) u ≠ 0 :=
  ne_of_gt (completedSaddleAnnulusNorthTransverse_deriv_pos hh hμ hu)

@[simp] theorem completedSaddleAnnulusSouthTransverse_zero (h μ : ℝ) :
    completedSaddleAnnulusSouthTransverse h μ 0 = 0 := by
  simp [completedSaddleAnnulusSouthTransverse]

@[simp] theorem completedSaddleAnnulusNorthTransverse_zero (h μ : ℝ) :
    completedSaddleAnnulusNorthTransverse h μ Real.pi = 0 := by
  simp [completedSaddleAnnulusNorthTransverse]

theorem completedSaddleAnnulusSouthTransverse_deriv_zero (h μ : ℝ) :
    deriv (completedSaddleAnnulusSouthTransverse h μ) 0 = -Real.sqrt (h / μ) := by
  rw [(completedSaddleAnnulusSouthTransverse_hasDerivAt h μ 0).deriv]
  simp

theorem completedSaddleAnnulusNorthTransverse_deriv_pi (h μ : ℝ) :
    deriv (completedSaddleAnnulusNorthTransverse h μ) Real.pi = Real.sqrt (h / μ) := by
  rw [(completedSaddleAnnulusNorthTransverse_hasDerivAt h μ Real.pi).deriv]
  simp

private theorem completedSaddleAnnulus_sqrt_scale
    {h μ : ℝ} (hh : 0 < h) (hμ : 0 < μ) :
    μ * (Real.sqrt (h / μ)) ^ 2 = h := by
  rw [Real.sq_sqrt (div_nonneg hh.le hμ.le)]
  exact mul_div_cancel₀ h hμ.ne'

/-- The actual south quadratic height equals the common normalized cosine
height, with the square-root coefficient cancelled from ordinary data. -/
theorem completedSaddleAnnulusSouthTransverse_height
    {h μ : ℝ} (hh : 0 < h) (hμ : 0 < μ) (u : ℝ) :
    -h + μ * (completedSaddleAnnulusSouthTransverse h μ u) ^ 2 / 2 =
      -h * Real.cos u := by
  calc
    _ = -h + 2 * (μ * (Real.sqrt (h / μ)) ^ 2) * (Real.sin (u / 2)) ^ 2 := by
      unfold completedSaddleAnnulusSouthTransverse
      ring
    _ = -h + 2 * h * (Real.sin (u / 2)) ^ 2 := by
      rw [completedSaddleAnnulus_sqrt_scale hh hμ]
    _ = -h * Real.cos u := by
      rw [Real.sin_sq_eq_half_sub]
      have hhalf : 2 * (u / 2) = u := by ring
      rw [hhalf]
      ring

/-- The actual north quadratic height equals the same normalized cosine
height on the actual angular parameter. -/
theorem completedSaddleAnnulusNorthTransverse_height
    {h μ : ℝ} (hh : 0 < h) (hμ : 0 < μ) (u : ℝ) :
    h - μ * (completedSaddleAnnulusNorthTransverse h μ u) ^ 2 / 2 =
      -h * Real.cos u := by
  calc
    _ = h - 2 * (μ * (Real.sqrt (h / μ)) ^ 2) * (Real.cos (u / 2)) ^ 2 := by
      unfold completedSaddleAnnulusNorthTransverse
      ring
    _ = h - 2 * h * (Real.cos (u / 2)) ^ 2 := by
      rw [completedSaddleAnnulus_sqrt_scale hh hμ]
    _ = -h * Real.cos u := by
      rw [Real.cos_sq]
      have hhalf : 2 * (u / 2) = u := by ring
      rw [hhalf]
      ring

/-- The actual south parameter enters the strictly negative transverse
side throughout the interior angular interval. -/
theorem completedSaddleAnnulusSouthTransverse_neg
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ) (hu : u ∈ Ioo 0 Real.pi) :
    completedSaddleAnnulusSouthTransverse h μ u < 0 := by
  have hs : 0 < Real.sqrt (h / μ) := Real.sqrt_pos.mpr (div_pos hh hμ)
  have hsin : 0 < Real.sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1])
      (by linarith [hu.2, Real.pi_pos])
  unfold completedSaddleAnnulusSouthTransverse
  exact mul_neg_of_neg_of_pos (by linarith) hsin

/-- The actual north parameter enters the same strictly negative
transverse side throughout the interior angular interval. -/
theorem completedSaddleAnnulusNorthTransverse_neg
    {h μ u : ℝ} (hh : 0 < h) (hμ : 0 < μ) (hu : u ∈ Ioo 0 Real.pi) :
    completedSaddleAnnulusNorthTransverse h μ u < 0 := by
  have hs : 0 < Real.sqrt (h / μ) := Real.sqrt_pos.mpr (div_pos hh hμ)
  have hc : 0 < Real.cos (u / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2]⟩
  unfold completedSaddleAnnulusNorthTransverse
  exact mul_neg_of_neg_of_pos (by linarith) hc

end
end TightVer401
