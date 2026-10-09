import TightVer401.IdentityBandCentralSupportCartesian
import TightVer401.ThinBandRuledGauss
import TightVer401.RuledSecondForm
import TightVer401.SeamFrameJet

/-! The actual support potential is saddle wherever its smooth source chart
reconstructs the ruled immersion and its actual unit normal. The sign follows
from the ruling and the nonzero mixed second form, without an assumed curvature
transport, inverse differential or framed tensor package. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual raw ruled reconstruction forces the Cartesian Hessian determinant
to be negative. The pullback frame need not be assumed invertible: a negative
framed determinant itself forces the unframed determinant to be negative. -/
theorem identityBandPlanarSupport_saddle_of_raw_reconstruction {L : ℝ}
    (d : PeriodicRuledFrame L) {G : Coord → ℝ} {U V : Set Coord} {P : Coord → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hPU : MapsTo P V U)
    (hrec : EqOn (planarSupportMap G ∘ P) (ruledMap d.γ d.E) V)
    (hnorm : EqOn (planarUnitNormal ∘ P) d.rawGaussMap V)
    {p : Coord} (hp : p ∈ V) : (planarHessian G (P p)).det < 0 := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hN := periodicRuledFrame_rawGaussMap_contDiff d
  have hn : ∀ q ∈ (univ : Set Coord),
      IsUnitNormalAt (ruledMap d.γ d.E) (d.rawGaussMap q) q := by
    intro q _
    exact ruled_isUnitNormal (d.deriv_γ (q 0)) (d.deriv_E (q 0))
      (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))
  have hmixed :
      secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 0 1 =
        d.τ (p 0) / Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) ∧
      secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 1 1 = 0 :=
    ruled_mixed_and_ruling_second_form d.deriv_γ d.deriv_E (d.orthonormal (p 0))
  have hraw10 : inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) p (Pi.single 1 1 : Coord))
      (fderiv ℝ d.rawGaussMap p (Pi.single 0 1 : Coord)) =
      -(d.τ (p 0) / Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1))) := by
    change inner ℝ (coordPartial 1 (ruledMap d.γ d.E) p) (coordPartial 0 d.rawGaussMap p) = _
    rw [real_inner_comm,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hn (mem_univ p) 0 1,
      hmixed.1]
  have hraw11 : inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) p (Pi.single 1 1 : Coord))
      (fderiv ℝ d.rawGaussMap p (Pi.single 1 1 : Coord)) = 0 := by
    change inner ℝ (coordPartial 1 (ruledMap d.γ d.E) p) (coordPartial 1 d.rawGaussMap p) = 0
    rw [real_inner_comm,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hn (mem_univ p) 1 1,
      hmixed.2, neg_zero]
  let u : Coord := fderiv ℝ P p (Pi.single 0 1 : Coord)
  let v : Coord := fderiv ℝ P p (Pi.single 1 1 : Coord)
  let B := seamFramedHessian G (P p) u v
  have hB10 : B 1 0 = dotProduct v ((planarHessian G (P p)).mulVec u) := by
    simp [B, seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have hB11 : B 1 1 = dotProduct v ((planarHessian G (P p)).mulVec v) := by
    simp [B, seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have hquot10 : B 1 0 / planarWeight (P p) =
      -(d.τ (p 0) / Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1))) := by
    rw [hB10]
    exact (identityBand_cartesian_pullback_pairing hG hU hV hP hPU hrec hnorm hp
      (Pi.single 1 1 : Coord) (Pi.single 0 1 : Coord)).symm.trans hraw10
  have hquot11 : B 1 1 / planarWeight (P p) = 0 := by
    rw [hB11]
    exact (identityBand_cartesian_pullback_pairing hG hU hV hP hPU hrec hnorm hp
      (Pi.single 1 1 : Coord) (Pi.single 1 1 : Coord)).symm.trans hraw11
  have hroot : Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (ruledEnergy_pos (d.torsion_ne_zero (p 0)))).ne'
  have hB10ne : B 1 0 ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hquot10
    exact (neg_ne_zero.mpr (div_ne_zero (d.torsion_ne_zero (p 0)) hroot)) hquot10.symm
  have hB11zero : B 1 1 = 0 := by
    have he := congrArg (fun z : ℝ => z * planarWeight (P p)) hquot11
    simpa only [div_mul_cancel₀ _ (planarWeight_pos (P p)).ne', zero_mul] using he
  have hsym : B 0 1 = B 1 0 := seamFramedHessian_symm hG hU (hPU hp) u v 0 1
  have hdetB : B.det < 0 := by
    rw [Matrix.det_fin_two, hB11zero, hsym]
    nlinarith [sq_pos_of_ne_zero hB10ne]
  change (seamFramedHessian G (P p) u v).det < 0 at hdetB
  rw [seamFramedHessian_det] at hdetB
  by_contra hnot
  have hnonneg := mul_nonneg (sq_nonneg (seamFrame u v).det) (le_of_not_gt hnot)
  exact (not_le_of_gt hdetB) hnonneg

end
end TightVer401
