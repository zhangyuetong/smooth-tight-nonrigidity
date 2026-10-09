import TightVer401.VisibleConnectorLocalPotential
import TightVer401.SeamFrameJet

/-! Actual ruled-gradient derivative and Hessian sign for the constructed
connector coordinates. The local potential is constructed in the imported
leaf; visible-angle signs and global annular degree remain applications. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency true

private theorem visibleConnector_coefficients_smooth {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorA p w) ∧ ContDiff ℝ ∞ (visibleConnectorB gamma w) ∧
      ContDiff ℝ ∞ (visibleConnectorC gamma w) := by
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdg := (contDiff_infty_iff_deriv.mp hgamma).2
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  constructor
  · unfold visibleConnectorA visibleConnectorDet
    fun_prop
  constructor
  · unfold visibleConnectorB dotProduct
    simp only [Fin.sum_univ_two]
    fun_prop
  · unfold visibleConnectorC visibleConnectorB visibleConnectorDet dotProduct
    simp only [Fin.sum_univ_two]
    fun_prop

/-- The true transverse derivative of the explicit gradient. -/
theorem visibleConnectorGradient_partial_one {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (q : Coord) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    coordPartial 1 (visibleConnectorGradient p gamma w) q =
      (visibleConnectorA p w (q 0) * visibleConnectorB gamma w (q 0) /
        (visibleConnectorDelta p gamma w q)^2) • visibleConnectorJ (w (q 0)) := by
  obtain ⟨hA, hB, hC⟩ := visibleConnector_coefficients_smooth hp hgamma hw
  have ha := ((hA.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hb := ((hB.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hc := ((hC.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hu := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := q)
  have hn := hu.mul hb
  have hd := ha.add (hu.mul (hb.sub hc))
  change HasFDerivAt (visibleConnectorDelta p gamma w) _ q at hd
  have hinv := (hasDerivAt_inv hDelta).hasFDerivAt.comp q hd
  have hratio := hn.mul hinv
  have hg := ((hgamma.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hj : ContDiff ℝ ∞ (fun s : ℝ => visibleConnectorJ (w s)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun s : ℝ => -(w s 1))
      exact ((contDiff_apply ℝ ℝ (1 : Fin 2)).comp hw).neg
    · change ContDiff ℝ ∞ (fun s : ℝ => w s 0)
      exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp hw
  have hjd := ((hj.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hY := hg.add (hratio.smul hjd)
  change HasFDerivAt (visibleConnectorGradient p gamma w) _ q at hY
  rw [coordPartial, hY.fderiv]
  ext i
  simp [visibleConnectorDelta, ContinuousLinearMap.comp_apply]
  field_simp [hDelta]
  <;> ring <;> simp

/-- Actual Hessian action, obtained by differentiating the actual gradient
identity of a descended local connector potential. -/
theorem visibleConnector_actual_hessian_transverse {G : Coord → ℝ} {U V : Set Coord}
    {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : MapsTo (visibleConnectorSource p w) V U)
    (hgradient : EqOn (planarGradient G ∘ visibleConnectorSource p w)
      (visibleConnectorGradient p gamma w) V)
    {q : Coord} (hq : q ∈ V) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    planarHessian G (visibleConnectorSource p w q) *ᵥ w (q 0) =
      (visibleConnectorA p w (q 0) * visibleConnectorB gamma w (q 0) /
        (visibleConnectorDelta p gamma w q)^2) • visibleConnectorJ (w (q 0)) := by
  have hP := visibleConnectorSource_contDiff hp hw
  have hdP := hP.differentiable (by simp) q
  have hdG := (((planarGradient_contDiffOn hG hU) _ (hmap hq)).contDiffAt
    (hU.mem_nhds (hmap hq))).differentiableAt (by simp)
  have hc := fderiv_comp q hdG hdP
  have he := (hgradient.eventuallyEq_of_mem (hV.mem_nhds hq)).fderiv_eq (𝕜 := ℝ)
  have hv := congrArg (fun L : Coord →L[ℝ] Coord => L (Pi.single 1 1)) hc
  change coordPartial 1 (planarGradient G ∘ visibleConnectorSource p w) q =
    fderiv ℝ (planarGradient G) (visibleConnectorSource p w q)
      (coordPartial 1 (visibleConnectorSource p w) q) at hv
  rw [(visibleConnectorSource_partials hp hw q).2,
    planarGradient_fderiv_apply hG hU (hmap hq)] at hv
  rw [coordPartial, he] at hv
  exact hv.symm.trans (visibleConnectorGradient_partial_one hp hgamma hw q hDelta)

/-- Exact determinant of the actual local Cartesian Hessian. The transverse
null direction is derived above, and symmetry is that of the actual G. -/
theorem visibleConnector_actual_hessian_determinant {G : Coord → ℝ} {U V : Set Coord}
    {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : MapsTo (visibleConnectorSource p w) V U)
    (hgradient : EqOn (planarGradient G ∘ visibleConnectorSource p w)
      (visibleConnectorGradient p gamma w) V)
    {q : Coord} (hq : q ∈ V) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    (planarHessian G (visibleConnectorSource p w q)).det =
      -(visibleConnectorA p w (q 0))^2 * (visibleConnectorB gamma w (q 0))^2 /
        (visibleConnectorDelta p gamma w q)^4 := by
  let v := coordPartial 0 (visibleConnectorSource p w) q
  let z := w (q 0)
  let D := visibleConnectorDelta p gamma w q
  let A := visibleConnectorA p w (q 0)
  let B := visibleConnectorB gamma w (q 0)
  let R := seamFramedHessian G (visibleConnectorSource p w q) v z
  have haction := visibleConnector_actual_hessian_transverse hp hgamma hw hG hU hV
    hmap hgradient hq hDelta
  have hvdet : visibleConnectorDet v z = -D := by
    dsimp [v, z, D]
    rw [← (visibleConnectorSource_partials hp hw q).2]
    exact visibleConnectorSource_actual_determinant hp hw gamma q
  have hjv : v ⬝ᵥ visibleConnectorJ z = D := by
    rw [dotProduct_comm, visibleConnectorJ_dot, hvdet, neg_neg]
  have h11 : R 1 1 = 0 := by
    have hentry : R 1 1 = z ⬝ᵥ (planarHessian G (visibleConnectorSource p w q) *ᵥ z) := by
      simp [R, seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hentry]
    dsimp [z]
    rw [haction, dotProduct_smul, dotProduct_comm (w (q 0)), visibleConnectorJ_dot_self]
    simp
  have h01 : R 0 1 = A * B / D := by
    have hentry : R 0 1 = v ⬝ᵥ (planarHessian G (visibleConnectorSource p w q) *ᵥ z) := by
      simp [R, seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hentry]
    change v ⬝ᵥ (planarHessian G (visibleConnectorSource p w q) *ᵥ w (q 0)) = _
    rw [haction, dotProduct_smul]
    change (A * B / D^2) * (v ⬝ᵥ visibleConnectorJ z) = _
    rw [hjv]
    change visibleConnectorDelta p gamma w q ≠ 0 at hDelta
    dsimp [D]
    field_simp [hDelta]
    <;> ring
  have h10 : R 1 0 = A * B / D := by
    have hs := seamFramedHessian_symm hG hU (hmap hq) v z 1 0
    exact hs.trans h01
  have hdet : R.det = -(A * B / D)^2 := by
    rw [Matrix.det_fin_two, h11, h01, h10]
    ring
  have hframe : (seamFrame v z).det = -D := by
    simpa [seamFrame, Matrix.det_fin_two, visibleConnectorDet, mul_comm] using hvdet
  have hprod := seamFramedHessian_det G (visibleConnectorSource p w q) v z
  change R.det = (seamFrame v z).det^2 * (planarHessian G (visibleConnectorSource p w q)).det at hprod
  rw [hdet, hframe, neg_sq] at hprod
  change (planarHessian G (visibleConnectorSource p w q)).det = -A^2 * B^2 / D^4
  apply (mul_left_cancel₀ (pow_ne_zero 2 hDelta))
  calc
    D^2 * (planarHessian G (visibleConnectorSource p w q)).det = -(A * B / D)^2 := hprod.symm
    _ = D^2 * (-A^2 * B^2 / D^4) := by
      dsimp [D]
      field_simp [hDelta]
      <;> ring

/-- Strict actual saddle sign holds wherever the explicit A,B,Delta are
nonzero, including terminal-coordinate neighborhoods once their signs hold. -/
theorem visibleConnector_actual_hessian_negative {G : Coord → ℝ} {U V : Set Coord}
    {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : MapsTo (visibleConnectorSource p w) V U)
    (hgradient : EqOn (planarGradient G ∘ visibleConnectorSource p w)
      (visibleConnectorGradient p gamma w) V)
    {q : Coord} (hq : q ∈ V) (hDelta : visibleConnectorDelta p gamma w q ≠ 0)
    (hA : visibleConnectorA p w (q 0) ≠ 0) (hB : visibleConnectorB gamma w (q 0) ≠ 0) :
    (planarHessian G (visibleConnectorSource p w q)).det < 0 := by
  rw [visibleConnector_actual_hessian_determinant hp hgamma hw hG hU hV hmap hgradient hq hDelta]
  have hnum : 0 < (visibleConnectorA p w (q 0))^2 * (visibleConnectorB gamma w (q 0))^2 :=
    mul_pos (sq_pos_of_ne_zero hA) (sq_pos_of_ne_zero hB)
  have hden : 0 < (visibleConnectorDelta p gamma w q)^4 := by
    have hh := sq_pos_of_ne_zero (pow_ne_zero 2 hDelta)
    simpa only [← pow_mul] using hh
  exact div_neg_of_neg_of_pos (by nlinarith [hnum]) hden

end
end TightVer401
