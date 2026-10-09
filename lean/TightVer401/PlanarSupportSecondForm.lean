import TightVer401.PlanarSupportForms

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace

theorem planarSupportMap_contDiffOn {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (planarSupportMap G) U := by
  have ha := partial_contDiffOn hG hU 0
  have hb := partial_contDiffOn hG hU 1
  have hD := (hG.sub ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).contDiff.contDiffOn.mul ha)).sub
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).contDiff.contDiffOn.mul hb)
  have hΦ : ContDiffOn ℝ ∞ (fun z : Coord =>
      ![coordPartial 0 G z, coordPartial 1 G z,
        G z - z 0 * coordPartial 0 G z - z 1 * coordPartial 1 G z]) U := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact ha
    · exact hb
    · exact hD
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp_contDiffOn hΦ

theorem planarHessian_symm {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (i j : Fin 2) : planarHessian G p i j = planarHessian G p j i :=
  coordPartial_comm hG hU hp i j

def planarNormalNumerator (p : Coord) : Ambient := WithLp.toLp 2 ![p 0, p 1, 1]

theorem planarNormalNumerator_contDiff : ContDiff ℝ ∞ planarNormalNumerator := by
  have hΦ : ContDiff ℝ ∞ (fun p : Coord => ![p 0, p 1, (1 : ℝ)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).contDiff
    · exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).contDiff
    · exact contDiff_const
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hΦ

theorem planarNormalNumerator_coordPartial (p : Coord) (i : Fin 2) :
    coordPartial i planarNormalNumerator p = WithLp.toLp 2
      ![(Pi.single i 1 : Coord) 0, (Pi.single i 1 : Coord) 1, 0] := by
  let Φ := fun p : Coord => ![p 0, p 1, (1 : ℝ)]
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hΦ : DifferentiableAt ℝ Φ p := by
    apply differentiableAt_pi.mpr
    intro j
    fin_cases j
    · exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).differentiableAt
    · exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).differentiableAt
    · exact differentiableAt_const _
  have hE := E.toContinuousLinearMap.hasFDerivAt.comp p hΦ.hasFDerivAt
  change HasFDerivAt (fun z => E (Φ z)) _ p at hE
  change fderiv ℝ (fun z => E (Φ z)) p (Pi.single i 1) = _
  rw [hE.fderiv]
  change E (fderiv ℝ Φ p (Pi.single i 1)) = _
  have hd : fderiv ℝ Φ p (Pi.single i 1) =
      ![(Pi.single i 1 : Coord) 0, (Pi.single i 1 : Coord) 1, 0] := by
    rw [fderiv_pi (differentiableAt_pi.mp hΦ)]
    ext j
    fin_cases j
    · change fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ) p
        (Pi.single i 1) = _
      rw [ContinuousLinearMap.fderiv]
      rfl
    · change fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ) p
        (Pi.single i 1) = _
      rw [ContinuousLinearMap.fderiv]
      rfl
    · simp [Φ]
  rw [hd]
  rfl

theorem planarUnitNormal_eq_smul (p : Coord) :
    planarUnitNormal p = (planarWeight p)⁻¹ • planarNormalNumerator p := by
  ext j
  fin_cases j <;> simp [planarUnitNormal, planarNormalNumerator, div_eq_mul_inv, mul_comm]

theorem planarSupportMap_secondFundamental {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    secondFundamental (planarSupportMap G) (planarUnitNormal p) p =
      -(planarWeight p)⁻¹ • planarHessian G p := by
  ext i j
  have hX := planarSupportMap_contDiffOn hG hU
  have hdj := (((partial_contDiffOn hX hU j) p hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdN : DifferentiableAt ℝ planarNormalNumerator p :=
    planarNormalNumerator_contDiff.contDiffAt.differentiableAt (by simp)
  have he : (fun q => inner ℝ (coordPartial j (planarSupportMap G) q)
      (planarNormalNumerator q)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    rw [planarSupportMap_coordPartial hG hU hq j]
    simp only [planarNormalNumerator, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, Fin.sum_univ_succ]
  have hi := coordPartial_eventuallyEq he i
  rw [coordPartial_inner hdj hdN] at hi
  have hz : coordPartial i (fun _ : Coord => (0 : ℝ)) p = 0 := by
    unfold coordPartial
    rw [(hasFDerivAt_const (c := (0 : ℝ)) p).fderiv]
    rfl
  have hpair : inner ℝ (coordPartial j (planarSupportMap G) p)
      (coordPartial i planarNormalNumerator p) = planarHessian G p j i := by
    rw [planarSupportMap_coordPartial hG hU hp j, planarNormalNumerator_coordPartial]
    simp only [EuclideanSpace.inner_toLp_toLp]
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_succ, planarHessian]
  rw [hpair, hz, planarHessian_symm hG hU hp j i] at hi
  have hsecond : inner ℝ (coordPartial i (coordPartial j (planarSupportMap G)) p)
      (planarNormalNumerator p) = -planarHessian G p i j := by linarith
  change inner ℝ (coordPartial i (coordPartial j (planarSupportMap G)) p)
    (planarUnitNormal p) = -(planarWeight p)⁻¹ * planarHessian G p i j
  rw [planarUnitNormal_eq_smul, real_inner_smul_right, hsecond]
  ring

end
end TightVer401
