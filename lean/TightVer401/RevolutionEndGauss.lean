import TightVer401.RevolutionEndCircleSmooth
import TightVer401.RevolutionEndNormalHeight

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

 def revolutionEndCircleNormal (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  (-1 / revolutionWeight (deriv q p.2)) • revolutionCircleRadial p.1 +
    revolutionNormalHeight q p.2 • revolutionAxis

 theorem revolutionEndCircleNormal_representative (q : ℝ → ℝ) (θ z : ℝ) :
    revolutionEndCircleNormal q (periodProjection (2 * Real.pi) θ, z) =
      revolutionEndNormal q (![θ, z] : Coord) := by
  simp [revolutionEndCircleNormal, revolutionCircleRadial_representative,
    revolutionEndNormal, revolutionNormalHeight]

 theorem revolutionEndCircleNormal_height (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) :
    revolutionEndCircleNormal q p 2 = revolutionNormalHeight q p.2 := by
  simp [revolutionEndCircleNormal, revolutionCircleRadial, revolutionAxis]

 theorem revolutionEndCircleNormal_unit (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) :
    inner ℝ (revolutionEndCircleNormal q p) (revolutionEndCircleNormal q p) = 1 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  have he : p = (periodProjection (2 * Real.pi) s, p.2) := Prod.ext hs.symm rfl
  rw [he, revolutionEndCircleNormal_representative]
  exact revolutionEndNormal_unit q _

 theorem revolutionEndCircleNormal_norm (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) :
    ‖revolutionEndCircleNormal q p‖ = 1 := by
  have h := revolutionEndCircleNormal_unit q p
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (revolutionEndCircleNormal q p)]

 theorem revolutionEndCircleNormal_injOn {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z) :
    InjOn (revolutionEndCircleNormal q) {p | H ≤ p.2} := by
  intro p hp s hs heq
  have hheight := congrArg (fun v : Ambient => v 2) heq
  simp only [revolutionEndCircleNormal_height] at hheight
  have hz : p.2 = s.2 := (revolutionNormalHeight_strictMonoOn hq hc).injOn hp hs hheight
  have hw : -1 / revolutionWeight (deriv q p.2) ≠ 0 :=
    div_ne_zero (by norm_num) (ne_of_gt (revolutionWeight_pos _))
  have hcos := congrArg (fun v : Ambient => v 0) heq
  have hsin := congrArg (fun v : Ambient => v 1) heq
  simp only [revolutionEndCircleNormal, revolutionCircleRadial, revolutionAxis,
    PiLp.add_apply, PiLp.smul_apply, WithLp.toLp, WithLp.equiv_symm_apply] at hcos hsin
  change (-1 / revolutionWeight (deriv q p.2)) * Real.Angle.cos p.1 + revolutionNormalHeight q p.2 * 0 =
    (-1 / revolutionWeight (deriv q s.2)) * Real.Angle.cos s.1 + revolutionNormalHeight q s.2 * 0 at hcos
  change (-1 / revolutionWeight (deriv q p.2)) * Real.Angle.sin p.1 + revolutionNormalHeight q p.2 * 0 =
    (-1 / revolutionWeight (deriv q s.2)) * Real.Angle.sin s.1 + revolutionNormalHeight q s.2 * 0 at hsin
  simp only [mul_zero, add_zero] at hcos hsin
  rw [← hz] at hcos hsin
  exact Prod.ext (revolutionAngle_cos_sin_injective ((mul_left_cancel₀ hw) hcos)
    ((mul_left_cancel₀ hw) hsin)) hz

 def revolutionEndGauss (q : ℝ → ℝ) (H : ℝ) (p : AddCircle (2 * Real.pi) × Ici H) :
    Metric.sphere (0 : Ambient) 1 :=
  ⟨revolutionEndCircleNormal q (p.1, p.2.val), by
    simpa using revolutionEndCircleNormal_norm q (p.1, p.2.val)⟩

 theorem revolutionEndGauss_injective {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z) :
    Function.Injective (revolutionEndGauss q H) := by
  intro p s heq
  have h := congrArg Subtype.val heq
  have he := revolutionEndCircleNormal_injOn hq hc p.2.property s.2.property h
  have hf : p.1 = s.1 := congrArg (fun v : AddCircle (2 * Real.pi) × ℝ => v.1) he
  have hz : p.2.val = s.2.val := congrArg (fun v : AddCircle (2 * Real.pi) × ℝ => v.2) he
  exact Prod.ext hf (Subtype.ext hz)

 theorem revolutionEndGauss_north {q : ℝ → ℝ} {H : ℝ}
    (hs : ∀ z ∈ Ici H, 0 < deriv q z) (p : AddCircle (2 * Real.pi) × Ici H) :
    (revolutionEndGauss q H p).val 2 ∈ Ioo (0 : ℝ) 1 := by
  change revolutionEndCircleNormal q (p.1, p.2.val) 2 ∈ Ioo (0 : ℝ) 1
  rw [revolutionEndCircleNormal_height]
  exact revolutionNormalHeight_mem_Ioo (hs _ p.2.property)

end
end TightVer401

