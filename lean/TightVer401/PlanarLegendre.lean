import TightVer401.PlanarGradientInverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def planarLegendre (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) (y : Coord) : ℝ :=
  e.symm y ⬝ᵥ y - G (e.symm y)

private theorem scalar_fderiv_coordinates (G : Coord → ℝ) (p v : Coord) :
    fderiv ℝ G p v = v 0 * coordPartial 0 G p + v 1 * coordPartial 1 G p := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp [coordPartial]

theorem planarLegendre_contDiffOn {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (planarLegendre G e) e.target := by
  have hx (j : Fin 2) : ContDiffOn ℝ ∞ (fun y => e.symm y j) e.target :=
    (ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).contDiff.comp_contDiffOn hi
  have hy (j : Fin 2) : ContDiffOn ℝ ∞ (fun y : Coord => y j) e.target :=
    (ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).contDiff.contDiffOn
  change ContDiffOn ℝ ∞ (fun y => e.symm y ⬝ᵥ y - G (e.symm y)) e.target
  simp only [dotProduct, Fin.sum_univ_two]
  exact (((hx 0).mul (hy 0)).add ((hx 1).mul (hy 1))).sub
    (hG.comp hi (fun _ hz => e.map_target hz))

theorem planarLegendre_coordPartial {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p) {y : Coord} (hy : y ∈ e.target)
    (i : Fin 2) : coordPartial i (planarLegendre G e) y = e.symm y i := by
  have hdI := ((hi y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hdG := ((hG _ (e.map_target hy)).contDiffAt
    (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
  have hdX (j : Fin 2) :=
    (ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).hasFDerivAt.comp y hdI.hasFDerivAt
  have hdY (j : Fin 2) :=
    (ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hd := (((hdX 0).mul (hdY 0)).add ((hdX 1).mul (hdY 1))).sub
    (hdG.hasFDerivAt.comp y hdI.hasFDerivAt)
  have hgradient : planarGradient G (e.symm y) = y :=
    (heG _ (e.map_target hy)).symm.trans (e.right_inv hy)
  have h0 : coordPartial 0 G (e.symm y) = y 0 := congrFun hgradient 0
  have h1 : coordPartial 1 G (e.symm y) = y 1 := congrFun hgradient 1
  unfold coordPartial
  have hd' := hd.congr_of_eventuallyEq (f₁ := planarLegendre G e)
    (Filter.Eventually.of_forall (fun z => by
      simp [planarLegendre, dotProduct, Fin.sum_univ_two]))
  rw [hd'.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [scalar_fderiv_coordinates, h0, h1]
  fin_cases i <;> simp <;> ring

theorem planarLegendre_gradient {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p) {y : Coord} (hy : y ∈ e.target) :
    planarGradient (planarLegendre G e) y = e.symm y := by
  ext i
  exact planarLegendre_coordPartial e hG hi heG hy i

theorem planarLegendre_hessian {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p) {y : Coord} (hy : y ∈ e.target) :
    planarHessian (planarLegendre G e) y = (planarHessian G (e.symm y))⁻¹ := by
  have hS := planarLegendre_contDiffOn e hG hi
  have hdI := ((hi y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hdP := ((planarGradient_contDiffOn hG e.open_source _ (e.map_target hy)).contDiffAt
    (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
  have hevent : (fun z => planarGradient G (e.symm z)) =ᶠ[𝓝 y] (fun z => z) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact (heG _ (e.map_target hz)).symm.trans (e.right_inv hz)
  have hcomp := hdP.hasFDerivAt.comp y hdI.hasFDerivAt
  have hcompEq : (fderiv ℝ (planarGradient G) (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ Coord := by
    rw [← hcomp.fderiv]
    change fderiv ℝ (fun z => planarGradient G (e.symm z)) y = _
    rw [hevent.fderiv_eq]
    exact (hasFDerivAt_id y).fderiv
  have heventI : planarGradient (planarLegendre G e) =ᶠ[𝓝 y] e.symm := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact planarLegendre_gradient e hG hi heG hz
  have hI (v : Coord) : fderiv ℝ e.symm y v =
      planarHessian (planarLegendre G e) y *ᵥ v := by
    rw [← heventI.fderiv_eq]
    exact planarGradient_fderiv_apply hS e.open_target hy v
  have hmul : planarHessian G (e.symm y) * planarHessian (planarLegendre G e) y = 1 := by
    ext i j
    have hj := congrArg (fun d : Coord →L[ℝ] Coord => d (Pi.single j 1) i) hcompEq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hj
    rw [planarGradient_fderiv_apply hG e.open_source (e.map_target hy), hI,
      Matrix.mulVec_mulVec] at hj
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
      Pi.single_apply] using hj
  exact (Matrix.inv_eq_right_inv hmul).symm

theorem planarLegendre_saddle {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p) {y : Coord} (hy : y ∈ e.target)
    (hneg : (planarHessian G (e.symm y)).det < 0) :
    (planarHessian (planarLegendre G e) y).det < 0 := by
  rw [planarLegendre_hessian e hG hi heG hy, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_lt_zero.mpr hneg

end
end TightVer401
