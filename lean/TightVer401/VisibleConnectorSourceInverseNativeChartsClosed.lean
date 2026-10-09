import TightVer401.PeriodCircle
import TightVer401.QuadraticRadialFillingCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

/-! The literal positive native round map, including both closed radial
endpoints. The existing quotient-circle homeomorphism and compactness supply
the closed chart; no global real argument or slit chart is used. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped Topology Matrix

/-- SAME positive quotient-circle phase and literal radius 1+t. -/
def visibleConnectorSourceInverseNativeRound (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × ℝ) : Coord :=
  seamComplexCoord ((1 + p.2) • (AddCircle.toCircle p.1 : ℂ))

theorem visibleConnectorSourceInverse_native_round_representative
    (L : ℝ) [Fact (0 < L)] (s t : ℝ) :
    visibleConnectorSourceInverseNativeRound L (periodProjection L s, t) =
      saddlePolarChart ![1 + t, 2 * Real.pi * s / L] := by
  change seamComplexCoord ((1 + t) • (AddCircle.toCircle (s : AddCircle L) : ℂ)) = _
  rw [AddCircle.toCircle_apply_mk]
  rw [show 2 * Real.pi / L * s = 2 * Real.pi * s / L by ring]
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, Circle.coe_exp, -Complex.ofReal_mul,
    -Complex.ofReal_div,
    saddlePolarChart, Complex.real_smul]

theorem visibleConnectorSourceInverse_native_round_radius
    (L : ℝ) [Fact (0 < L)] (p : AddCircle L × ℝ) (hp : 0 < 1 + p.2) :
    planarRadius (visibleConnectorSourceInverseNativeRound L p) = 1 + p.2 := by
  rw [visibleConnectorSourceInverseNativeRound, quadraticRadialFillingRadius_complex,
    norm_smul, Real.norm_eq_abs, abs_of_pos hp, Circle.norm_coe, mul_one]

theorem visibleConnectorSourceInverse_native_round_continuous
    (L : ℝ) [Fact (0 < L)] : Continuous (visibleConnectorSourceInverseNativeRound L) := by
  exact seamComplexCoord.continuous.comp
    ((continuous_const.add continuous_snd).smul
      (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp continuous_fst)))

/-- Actual closed native round chart. Its forward map is the shared literal
positive map, with height 0 and 1 corresponding to radii 1 and 2. -/
def visibleConnectorSourceInverse_native_round_closure
    (L : ℝ) [hL : Fact (0 < L)] :
    (AddCircle L × Icc (0 : ℝ) 1) ≃ₜ
      ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} := by
  let f : (AddCircle L × Icc (0 : ℝ) 1) →
      ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} := fun p =>
    ⟨visibleConnectorSourceInverseNativeRound L (p.1, p.2), by
      have hPositive : 0 < 1 + (p.2 : ℝ) := by linarith [p.2.property.1]
      change 1 ≤ planarRadius (visibleConnectorSourceInverseNativeRound L (p.1, (p.2 : ℝ))) ∧
        planarRadius (visibleConnectorSourceInverseNativeRound L (p.1, (p.2 : ℝ))) ≤ 2
      rw [visibleConnectorSourceInverse_native_round_radius L _ hPositive]
      constructor <;> linarith [p.2.property.1, p.2.property.2]⟩
  have hf : Continuous f :=
    ((visibleConnectorSourceInverse_native_round_continuous L).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hBij : Bijective f := by
    constructor
    · intro a b he
      have hN : visibleConnectorSourceInverseNativeRound L (a.1, (a.2 : ℝ)) =
          visibleConnectorSourceInverseNativeRound L (b.1, (b.2 : ℝ)) :=
        congrArg Subtype.val he
      have ha : 0 < 1 + (a.2 : ℝ) := by linarith [a.2.property.1]
      have hb : 0 < 1 + (b.2 : ℝ) := by linarith [b.2.property.1]
      have hHeight : (a.2 : ℝ) = (b.2 : ℝ) := by
        have hRadius := congrArg planarRadius hN
        rw [visibleConnectorSourceInverse_native_round_radius L _ ha,
          visibleConnectorSourceInverse_native_round_radius L _ hb] at hRadius
        linarith
      have hComplex : (1 + (a.2 : ℝ)) • (AddCircle.toCircle a.1 : ℂ) =
          (1 + (b.2 : ℝ)) • (AddCircle.toCircle b.1 : ℂ) :=
        seamComplexCoord.injective hN
      have hSmul : (1 + (b.2 : ℝ)) • (AddCircle.toCircle a.1 : ℂ) =
          (1 + (b.2 : ℝ)) • (AddCircle.toCircle b.1 : ℂ) := by
        simpa only [hHeight] using hComplex
      have hPhase : AddCircle.toCircle a.1 = AddCircle.toCircle b.1 :=
        Circle.ext (smul_right_injective ℂ hb.ne' hSmul)
      apply Prod.ext
      · exact AddCircle.injective_toCircle hL.out.ne' hPhase
      · exact Subtype.ext hHeight
    · intro z
      let r : ℝ := planarRadius (z : Coord)
      have hr : 0 < r := lt_of_lt_of_le zero_lt_one z.property.1
      have hNorm : ‖seamComplexCoord.symm (z : Coord)‖ = r := by
        rw [← quadraticRadialFillingRadius_complex, seamComplexCoord.apply_symm_apply]
      let c : Circle := ⟨r⁻¹ • seamComplexCoord.symm (z : Coord), by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hr), hNorm]
        exact inv_mul_cancel₀ hr.ne'⟩
      let q : AddCircle L := (AddCircle.homeomorphCircle hL.out.ne').symm c
      let t : Icc (0 : ℝ) 1 := ⟨r - 1, by
        constructor <;> linarith [z.property.1, z.property.2]⟩
      have hCircle : AddCircle.toCircle q = c := by
        rw [← AddCircle.homeomorphCircle_apply hL.out.ne']
        exact (AddCircle.homeomorphCircle hL.out.ne').apply_symm_apply c
      refine ⟨(q, t), Subtype.ext ?_⟩
      change seamComplexCoord ((1 + (r - 1)) • (AddCircle.toCircle q : ℂ)) = (z : Coord)
      rw [hCircle]
      change seamComplexCoord ((1 + (r - 1)) • (r⁻¹ • seamComplexCoord.symm (z : Coord))) = _
      rw [show 1 + (r - 1) = r by ring, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        seamComplexCoord.apply_symm_apply]
  let B := Equiv.ofBijective f hBij
  have hB : Continuous B := hf
  exact hB.homeoOfEquivCompactToT2

@[simp] theorem visibleConnectorSourceInverse_native_round_closure_apply
    (L : ℝ) [Fact (0 < L)] (p : AddCircle L × Icc (0 : ℝ) 1) :
    (visibleConnectorSourceInverse_native_round_closure L p : Coord) =
      visibleConnectorSourceInverseNativeRound L (p.1, (p.2 : ℝ)) := rfl

end
end TightVer401
