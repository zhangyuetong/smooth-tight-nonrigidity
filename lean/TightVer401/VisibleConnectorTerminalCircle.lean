import TightVer401.VisibleConnectorTangentDirection
import TightVer401.VisibleConnectorRuledHessian
import TightVer401.PlanarGradientInverse

/-! Actual manuscript ruling and its circular terminal gradient.
The ordinary direction and coefficient hypotheses are explicit. Choosing the
small angle, proving annular global inverses and retaining the incoming open
germ remain construction steps; none is an assumed connector package. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- The actual ruling is delta minus the radius times the visible direction. -/
def visibleConnectorActualRuling (R : ℝ) (gamma e : ℝ → Coord) (s : ℝ) : Coord :=
  visibleConnectorJ (gamma s) - R • e s

/-- Terminal parameter of the actual ruling, including the seam itself. -/
def visibleConnectorActualTerminalHeight (p gamma w : ℝ → Coord) (s : ℝ) : ℝ :=
  visibleConnectorA p w s / visibleConnectorC gamma w s

theorem visibleConnectorActualRuling_contDiff {R : ℝ} {gamma e : ℝ → Coord}
    (hgamma : ContDiff ℝ ∞ gamma) (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (visibleConnectorActualRuling R gamma e) := by
  have hJ : ContDiff ℝ ∞ (visibleConnectorJ ∘ gamma) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun s => -(gamma s 1))
      simpa only [Function.comp_def] using
        ((contDiff_apply ℝ ℝ (1 : Fin 2)).comp hgamma).neg
    · change ContDiff ℝ ∞ (fun s => gamma s 0)
      simpa only [Function.comp_def] using
        (contDiff_apply ℝ ℝ (0 : Fin 2)).comp hgamma
  have hscale : ContDiff ℝ ∞ (fun s : ℝ => R • e s) :=
    (contDiff_const (c := R)).smul he
  exact hJ.sub hscale

private theorem connector_curve_coordinate_smooth {f : ℝ → Coord}
    (hf : ContDiff ℝ ∞ f) (i : Fin 2) : ContDiff ℝ ∞ (fun s => f s i) := by
  simpa only [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp hf

theorem visibleConnectorA_contDiff {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorA p w) := by
  have hd := (contDiff_infty_iff_deriv.mp hp).2
  exact ((connector_curve_coordinate_smooth hd 0).mul
    (connector_curve_coordinate_smooth hw 1) |>.sub
      ((connector_curve_coordinate_smooth hd 1).mul
        (connector_curve_coordinate_smooth hw 0))).neg

theorem visibleConnectorB_contDiff {gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorB gamma w) := by
  have hd := (contDiff_infty_iff_deriv.mp hg).2
  have hfun : visibleConnectorB gamma w =
      (fun s => deriv gamma s 0 * w s 0 + deriv gamma s 1 * w s 1) := by
    funext s
    simp only [visibleConnectorB,dotProduct,Fin.sum_univ_two]
  rw [hfun]
  exact
    ((connector_curve_coordinate_smooth hd 0).mul (connector_curve_coordinate_smooth hw 0)).add
      ((connector_curve_coordinate_smooth hd 1).mul (connector_curve_coordinate_smooth hw 1))

theorem visibleConnectorC_contDiff {gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorC gamma w) := by
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  exact (visibleConnectorB_contDiff hg hw).add
    (((connector_curve_coordinate_smooth hd 0).mul (connector_curve_coordinate_smooth hw 1)).sub
      ((connector_curve_coordinate_smooth hd 1).mul (connector_curve_coordinate_smooth hw 0)))

/-- The actual terminal parameter is smooth, not a chosen endpoint witness. -/
theorem visibleConnectorActualTerminalHeight_contDiff {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hC : ∀ s, visibleConnectorC gamma w s ≠ 0) :
    ContDiff ℝ ∞ (visibleConnectorActualTerminalHeight p gamma w) :=
  (visibleConnectorA_contDiff hp hw).div (visibleConnectorC_contDiff hg hw) hC

/-- Derivative of the actual quarter-turn, with no angle coordinate assumption. -/
theorem visibleConnectorJ_hasDerivAt {f : ℝ → Coord} {f' : Coord} {s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun t => visibleConnectorJ (f t)) (visibleConnectorJ f') s := by
  let J : Coord →L[ℝ] Coord := ContinuousLinearMap.pi
    (![-(ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)),
        ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)] : Fin 2 → Coord →L[ℝ] ℝ)
  have hJ : (J : Coord → Coord) = visibleConnectorJ := by
    funext v
    ext i
    fin_cases i <;> rfl
  have hd := J.hasFDerivAt.comp_hasDerivAt s hf
  simpa only [hJ,Function.comp_def] using hd

/-- The actual C coefficient factors into angular speed and excess.
The direction derivative is an ordinary actual derivative premise, and can
be supplied by the constructed smooth circle angle. -/
theorem visibleConnector_actual_ruling_C_formula {R : ℝ} {gamma e : ℝ → Coord}
    (hg : ContDiff ℝ ∞ gamma) {s k : ℝ}
    (he : HasDerivAt e (k • visibleConnectorJ (e s)) s)
    (hunit : e s ⬝ᵥ e s = 1) :
    visibleConnectorC gamma (visibleConnectorActualRuling R gamma e) s =
      R*k*(visibleConnectorJ (gamma s) ⬝ᵥ e s - R) := by
  have hd := (visibleConnectorJ_hasDerivAt
    (hg.differentiable (by simp) s).hasDerivAt).sub (he.const_smul R)
  have hw : deriv (visibleConnectorActualRuling R gamma e) s =
      visibleConnectorJ (deriv gamma s) - R • (k • visibleConnectorJ (e s)) := hd.deriv
  unfold visibleConnectorC visibleConnectorB
  rw [hw]
  simp only [visibleConnectorActualRuling,visibleConnectorJ,visibleConnectorDet,
    dotProduct,Fin.sum_univ_two,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one] at hunit ⊢
  linear_combination -(R^2*k)*hunit

/-- The terminal gradient is the actual radius-R rotated direction, and the
Jacobian denominator is positive throughout the closed ruled segment. -/
theorem visibleConnector_actual_ruling_circle_terminal {R : ℝ} (hR : 0 < R)
    {p gamma e : ℝ → Coord} {s : ℝ}
    (he : e s ⬝ᵥ e s = 1)
    (hA : 0 < visibleConnectorA p (visibleConnectorActualRuling R gamma e) s)
    (hB : 0 < visibleConnectorB gamma (visibleConnectorActualRuling R gamma e) s)
    (hC : 0 < visibleConnectorC gamma (visibleConnectorActualRuling R gamma e) s) :
    let w := visibleConnectorActualRuling R gamma e
    let t := visibleConnectorActualTerminalHeight p gamma w s
    0 < t ∧
    (∀ u ∈ Icc (0 : ℝ) t, 0 < visibleConnectorDelta p gamma w ![s,u]) ∧
    visibleConnectorGradient p gamma w ![s,t] = -R • visibleConnectorJ (e s) ∧
    visibleConnectorGradient p gamma w ![s,t] ⬝ᵥ
      visibleConnectorGradient p gamma w ![s,t] = R^2 := by
  dsimp only
  let w := visibleConnectorActualRuling R gamma e
  let A := visibleConnectorA p w s
  let B := visibleConnectorB gamma w s
  let C := visibleConnectorC gamma w s
  let t := visibleConnectorActualTerminalHeight p gamma w s
  have hA' : 0 < A := hA
  have hB' : 0 < B := hB
  have hC' : 0 < C := hC
  have ht : 0 < t := div_pos hA' hC' 
  have hend : visibleConnectorDelta p gamma w ![s,t] = A * B / C := by
    change A + (A / C) * (B-C) = A*B/C
    field_simp [hC'.ne']
    <;> ring
  have hclosed (u : ℝ) (hu : u ∈ Icc (0 : ℝ) t) :
      0 < visibleConnectorDelta p gamma w ![s,u] := by
    have huc : u*C ≤ A := (le_div_iff₀ hC).mp hu.2
    change 0 < A + u*(B-C)
    by_cases hupos : 0 < u
    · have : 0 < u*B := mul_pos hupos hB
      nlinarith
    · have hz : u = 0 := le_antisymm (le_of_not_gt hupos) hu.1
      rw [hz]
      simpa using hA
  have hquot : t * B / visibleConnectorDelta p gamma w ![s,t] = 1 := by
    rw [hend]
    change (A/C)*B/(A*B/C)=1
    field_simp [hA'.ne',hB'.ne',hC'.ne']
  have hg : visibleConnectorGradient p gamma w ![s,t] = -R • visibleConnectorJ (e s) := by
    change gamma s + (t * B / visibleConnectorDelta p gamma w ![s,t]) •
      visibleConnectorJ (w s) = -R • visibleConnectorJ (e s)
    rw [hquot,one_smul]
    change gamma s + visibleConnectorJ (visibleConnectorJ (gamma s) - R • e s) =
      -R • visibleConnectorJ (e s)
    ext i
    fin_cases i <;> simp [visibleConnectorJ] <;> ring
  refine ⟨ht,hclosed,hg,?_⟩
  rw [hg]
  have heJ : visibleConnectorJ (e s) ⬝ᵥ visibleConnectorJ (e s) = 1 := by
    simpa [visibleConnectorJ,dotProduct,Fin.sum_univ_two,add_comm] using he
  simp only [smul_dotProduct,dotProduct_smul,heJ,mul_one]
  ring

/-- At every actual terminal point the constructed local potential is saddle
on an OPEN neighborhood and its actual gradient has an actual smooth local
inverse. This includes the seam; it is not the global whole-circle collar. -/
theorem visibleConnector_exists_actual_terminal_local_saddle
    {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} {p gamma e : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hp : ContDiff ℝ ∞ p)
    (hgamma : ContDiff ℝ ∞ gamma) (he : ContDiff ℝ ∞ e)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hunit : ∀ s, e s ⬝ᵥ e s = 1) (s : ℝ)
    (hA : 0 < visibleConnectorA p (visibleConnectorActualRuling R gamma e) s)
    (hB : 0 < visibleConnectorB gamma (visibleConnectorActualRuling R gamma e) s)
    (hC : 0 < visibleConnectorC gamma (visibleConnectorActualRuling R gamma e) s) :
    let w := visibleConnectorActualRuling R gamma e
    let q := (![s,visibleConnectorActualTerminalHeight p gamma w s] : Coord)
    ∃ (E : OpenPartialHomeomorph Coord Coord) (G : Coord → ℝ) (U : Set Coord),
      q ∈ E.source ∧ (E : Coord → Coord) = visibleConnectorSource p w ∧
      IsOpen U ∧ visibleConnectorSource p w q ∈ U ∧ U ⊆ E.target ∧
      ContDiffOn ℝ ∞ G U ∧
      (∀ y ∈ U, (planarHessian G y).det < 0) ∧
      planarGradient G (visibleConnectorSource p w q) = -R • visibleConnectorJ (e s) ∧
      ∃ H : OpenPartialHomeomorph Coord Coord,
        visibleConnectorSource p w q ∈ H.source ∧ H.source ⊆ U ∧
        (H : Coord → Coord) = planarGradient G ∧
        ContDiffOn ℝ ∞ H.symm H.target := by
  dsimp only
  let w := visibleConnectorActualRuling R gamma e
  let t := visibleConnectorActualTerminalHeight p gamma w s
  let q := (![s,t] : Coord)
  have hw := visibleConnectorActualRuling_contDiff (R := R) hgamma he
  have hc := visibleConnector_actual_ruling_circle_terminal hR (hunit s) hA hB hC
  have hD : 0 < visibleConnectorDelta p gamma w q :=
    hc.2.1 t ⟨hc.1.le,le_rfl⟩
  obtain ⟨E,G,hq,hE,hI,hG,hheight,hgradient⟩ :=
    visibleConnector_exists_local_potential hg hp hgamma hw hvalue q hD.ne'
  have hmaps : MapsTo (visibleConnectorSource p w) E.source E.target := by
    intro r hr
    rw [← hE]
    exact E.map_source hr
  have hpoint : (planarHessian G (visibleConnectorSource p w q)).det < 0 :=
    visibleConnector_actual_hessian_negative hp hgamma hw hG E.open_target E.open_source
      hmaps hgradient hq hD.ne'
      (by change visibleConnectorA p w s ≠ 0; exact hA.ne')
      (by change visibleConnectorB gamma w s ≠ 0; exact hB.ne')
  let U := E.target ∩ (fun y => (planarHessian G y).det) ⁻¹' Iio (0 : ℝ)
  have hU : IsOpen U := (planarHessian_det_contDiffOn hG E.open_target).continuousOn.isOpen_inter_preimage E.open_target isOpen_Iio
  have hpU : visibleConnectorSource p w q ∈ U := ⟨hmaps hq,hpoint⟩
  have hGU : ContDiffOn ℝ ∞ G U := hG.mono inter_subset_left
  obtain ⟨H,hh,hhU,hhF,hhI⟩ := planarGradient_exists_smooth_local_inverse hGU hU
    (fun y hy => hy.2.ne) hpU
  refine ⟨E,G,U,hq,hE,hU,hpU,inter_subset_left,hGU,
    (fun y hy => hy.2),?_,H,hh,hhU,hhF,hhI⟩
  exact (hgradient hq).trans hc.2.2.1

end
end TightVer401
