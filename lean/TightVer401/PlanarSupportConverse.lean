import TightVer401.PlanarSupportSecondForm

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace

/-- The potential associated to the unnormalized upper-hemisphere normal. -/
def planarPotential (X : Coord → Ambient) (p : Coord) : ℝ :=
  inner ℝ (X p) (planarNormalNumerator p)

theorem planarPotential_eq_coordinates (X : Coord → Ambient) (p : Coord) :
    planarPotential X p = X p 0 * p 0 + X p 1 * p 1 + X p 2 := by
  simp [planarPotential, planarNormalNumerator, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem planarPotential_contDiffOn {X : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) : ContDiffOn ℝ ∞ (planarPotential X) U :=
  hX.inner ℝ planarNormalNumerator_contDiff.contDiffOn

theorem planarPotential_eq_weight_height (X : Coord → Ambient) (p : Coord) :
    planarPotential X p = planarWeight p * inner ℝ (X p) (planarUnitNormal p) := by
  rw [planarUnitNormal_eq_smul, real_inner_smul_right, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (planarWeight_pos p)), one_mul]
  rfl

theorem planarPotential_normal_height (X : Coord → Ambient) (p : Coord) :
    inner ℝ (X p) (planarUnitNormal p) = planarPotential X p / planarWeight p := by
  rw [planarUnitNormal_eq_smul, real_inner_smul_right]
  simp [planarPotential, div_eq_mul_inv, mul_comm]

theorem planarPotential_coordPartial {X : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hn : IsUnitNormalAt X (planarUnitNormal p) p) (i : Fin 2) :
    coordPartial i (planarPotential X) p = X p (Fin.castSucc i) := by
  have hdX := ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdP : DifferentiableAt ℝ planarNormalNumerator p :=
    planarNormalNumerator_contDiff.contDiffAt.differentiableAt (by simp)
  have horth : inner ℝ (coordPartial i X p) (planarNormalNumerator p) = 0 := by
    have hn' := hn.2 (Pi.single i 1)
    change inner ℝ (coordPartial i X p) (planarUnitNormal p) = 0 at hn'
    rw [planarUnitNormal_eq_smul, real_inner_smul_right] at hn'
    exact (mul_eq_zero.mp hn').resolve_left (inv_ne_zero (ne_of_gt (planarWeight_pos p)))
  change coordPartial i (fun q => inner ℝ (X q) (planarNormalNumerator q)) p = _
  rw [coordPartial_inner hdX hdP, horth, add_zero, planarNormalNumerator_coordPartial]
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_succ]

theorem planarSupportMap_converse_local {X : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U)
    (hn : ∀ p ∈ U, IsUnitNormalAt X (planarUnitNormal p) p) :
    EqOn X (planarSupportMap (planarPotential X)) U := by
  intro p hp
  have h0 := planarPotential_coordPartial hX hU hp (hn p hp) 0
  have h1 := planarPotential_coordPartial hX hU hp (hn p hp) 1
  ext j
  fin_cases j
  · simpa [planarSupportMap] using h0.symm
  · simpa [planarSupportMap] using h1.symm
  · change X p 2 = planarPotential X p -
      p 0 * coordPartial 0 (planarPotential X) p -
      p 1 * coordPartial 1 (planarPotential X) p
    simp only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
    rw [h0, h1, planarPotential_eq_coordinates]
    ring

end
end TightVer401
