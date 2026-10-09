import TightVer401.FermiNormalGeometry
import TightVer401.ScalarCoordinateCalculus

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def fermiProduct (A B : ℝ → ℝ) (p : Coord) := A (p 0) * B (p 1)

theorem fermiProduct_contDiff {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (fermiProduct A B) :=
  (hA.comp (contDiff_apply ℝ ℝ 0)).mul (hB.comp (contDiff_apply ℝ ℝ 1))

theorem fermiProduct_partials {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (p : Coord) :
    coordPartial 0 (fermiProduct A B) p = deriv A (p 0) * B (p 1) ∧
    coordPartial 1 (fermiProduct A B) p = A (p 0) * deriv B (p 1) := by
  have ha := ((hA.differentiable (by simp) (p 0)).hasDerivAt.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hb := ((hB.differentiable (by simp) (p 1)).hasDerivAt.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hd := ha.mul hb
  have he : ((A ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ)) *
      (B ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ))) = fermiProduct A B := rfl
  rw [he] at hd
  constructor
  · change fderiv ℝ (fermiProduct A B) p (Pi.single 0 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, mul_comm]
  · change fderiv ℝ (fermiProduct A B) p (Pi.single 1 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply]

theorem fermiProduct_second_partials {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (p : Coord) :
    coordPartial 0 (coordPartial 0 (fermiProduct A B)) p =
      deriv (deriv A) (p 0) * B (p 1) ∧
    coordPartial 0 (coordPartial 1 (fermiProduct A B)) p =
      deriv A (p 0) * deriv B (p 1) ∧
    coordPartial 1 (coordPartial 1 (fermiProduct A B)) p =
      A (p 0) * deriv (deriv B) (p 1) := by
  have h0 : coordPartial 0 (fermiProduct A B) = fermiProduct (deriv A) B :=
    funext fun q => (fermiProduct_partials hA hB q).1
  have h1 : coordPartial 1 (fermiProduct A B) = fermiProduct A (deriv B) :=
    funext fun q => (fermiProduct_partials hA hB q).2
  rw [h0, h1]
  exact ⟨(fermiProduct_partials (contDiff_infty_iff_deriv.mp hA).2 hB p).1,
    (fermiProduct_partials hA (contDiff_infty_iff_deriv.mp hB).2 p).1,
    (fermiProduct_partials hA (contDiff_infty_iff_deriv.mp hB).2 p).2⟩

def fermiQuadraticCutoff (χ : ℝ → ℝ) (t : ℝ) : ℝ := t ^ 2 * χ t

theorem fermiQuadraticCutoff_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fermiQuadraticCutoff χ) := (contDiff_id.pow 2).mul hχ

theorem fermiQuadraticCutoff_hasDerivAt {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (t : ℝ) :
    HasDerivAt (fermiQuadraticCutoff χ) (2 * t * χ t + t ^ 2 * deriv χ t) t := by
  have hd := ((hasDerivAt_id t).pow 2).mul (hχ.differentiable (by simp) t).hasDerivAt
  convert! hd using 1 <;> simp [fermiQuadraticCutoff]

theorem fermiQuadraticCutoff_zero_jets {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    fermiQuadraticCutoff χ 0 = 0 ∧ deriv (fermiQuadraticCutoff χ) 0 = 0 ∧
      deriv (deriv (fermiQuadraticCutoff χ)) 0 = 2 * χ 0 := by
  have he : deriv (fermiQuadraticCutoff χ) =
      (fun t => 2 * t * χ t + t ^ 2 * deriv χ t) :=
    funext fun t => (fermiQuadraticCutoff_hasDerivAt hχ t).deriv
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul
    (hχ.differentiable (by simp) 0).hasDerivAt).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul
        (hχd.differentiable (by simp) 0).hasDerivAt)
  have hfunc : ((fun y : ℝ => 2 * id y) * χ + id ^ 2 * deriv χ) =
      (fun t => 2 * t * χ t + t ^ 2 * deriv χ t) := rfl
  rw [hfunc] at hd
  constructor
  · simp [fermiQuadraticCutoff]
  · constructor
    · rw [he]
      simp
    · rw [he]
      simpa using hd.deriv

theorem fermiProduct_quadraticCutoff_seam {A χ : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hχ : ContDiff ℝ ∞ χ) (r : ℝ) :
    fermiProduct A (fermiQuadraticCutoff χ) ![r,0] = 0 ∧
    coordPartial 0 (fermiProduct A (fermiQuadraticCutoff χ)) ![r,0] = 0 ∧
    coordPartial 1 (fermiProduct A (fermiQuadraticCutoff χ)) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 0 (fermiProduct A (fermiQuadraticCutoff χ))) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 1 (fermiProduct A (fermiQuadraticCutoff χ))) ![r,0] = 0 ∧
    coordPartial 1 (coordPartial 1 (fermiProduct A (fermiQuadraticCutoff χ))) ![r,0] =
      2 * A r * χ 0 := by
  have hB := fermiQuadraticCutoff_contDiff hχ
  have h1 := fermiProduct_partials hA hB (![r,0] : Coord)
  have h2 := fermiProduct_second_partials hA hB (![r,0] : Coord)
  have hj := fermiQuadraticCutoff_zero_jets hχ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h2
  rw [h1.1, h1.2, h2.1, h2.2.1, h2.2.2]
  simp [fermiProduct, hj.1, hj.2.1, hj.2.2, mul_comm, mul_left_comm]

end
end TightVer401
