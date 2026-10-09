import TightVer401.SphereSupportOpenGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def planarSupportMap (G : Coord → ℝ) (p : Coord) : Ambient :=
  WithLp.toLp 2 ![coordPartial 0 G p, coordPartial 1 G p,
    G p - p 0 * coordPartial 0 G p - p 1 * coordPartial 1 G p]

theorem planarSupportMap_coordPartial {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    coordPartial i (planarSupportMap G) p = WithLp.toLp 2
      ![coordPartial i (coordPartial 0 G) p, coordPartial i (coordPartial 1 G) p,
        -p 0 * coordPartial i (coordPartial 0 G) p - p 1 * coordPartial i (coordPartial 1 G) p] := by
  let a := coordPartial 0 G
  let b := coordPartial 1 G
  let D := fun z : Coord => G z - z 0 * a z - z 1 * b z
  let Φ := fun z : Coord => ![a z, b z, D z]
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have ha : ContDiffOn ℝ ∞ a U := partial_contDiffOn hG hU 0
  have hb : ContDiffOn ℝ ∞ b U := partial_contDiffOn hG hU 1
  have hD : ContDiffOn ℝ ∞ D U :=
    (hG.sub ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).contDiff.contDiffOn.mul ha)).sub
      ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).contDiff.contDiffOn.mul hb)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact ha
    · exact hb
    · exact hD
  have hdG := ((hG p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hda := ((ha p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdb := ((hb p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdd := hdG.hasFDerivAt.sub
    ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt.mul hda.hasFDerivAt) |>.sub
      ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt.mul hdb.hasFDerivAt)
  change HasFDerivAt (fun z : Coord => G z - z 0 * a z - z 1 * b z) _ p at hdd
  have hpartD : coordPartial i D p = -p 0 * coordPartial i a p - p 1 * coordPartial i b p := by
    unfold coordPartial
    change fderiv ℝ (fun z : Coord => G z - z 0 * a z - z 1 * b z) p (Pi.single i 1) = _
    rw [hdd.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    fin_cases i <;> simp [Pi.single_apply, a, b, coordPartial] <;> ring
  have hPhiD := ((hΦ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hE := E.toContinuousLinearMap.hasFDerivAt.comp p hPhiD.hasFDerivAt
  change HasFDerivAt (fun z => E (Φ z)) _ p at hE
  have hcoords : coordPartial i Φ p = ![coordPartial i a p, coordPartial i b p, coordPartial i D p] := by
    unfold coordPartial
    rw [fderiv_pi (fun j => (contDiffOn_pi.mp hΦ j p hp).contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by simp))]
    ext j
    fin_cases j <;> rfl
  change fderiv ℝ (fun z => E (Φ z)) p (Pi.single i 1) = _
  rw [hE.fderiv]
  change E (coordPartial i Φ p) = _
  rw [hcoords, hpartD]
  rfl

end
end TightVer401
