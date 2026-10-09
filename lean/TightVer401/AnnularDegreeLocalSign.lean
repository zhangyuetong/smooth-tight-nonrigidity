import TightVer401.NativePlanarSchoenflies
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof
import OAI.Analysis.CircleDomains.Sobolev.ArgumentCircleIntegral
import OAI.Analysis.CircleDomains.Topology.JordanExteriors
import OAI.Analysis.CircleDomains.Sobolev.ComplexCoareaJacobian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local disk and actual area-form ingredients for signed preimage
counting. A local inverse chart may be derived from the actual derivative;
its injectivity is used only on one closed interior disk. These lemmas
do not assume any global image or injectivity for the annular map. -/
namespace TightVer401
noncomputable section
open Set Function Metric MeasureTheory
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Recognize the bounded filling of a local disk's image boundary. The
homeomorphism `H` is a Jordan--Schoenflies filling of this boundary; the
image of the interior disk is a conclusion, not a premise. -/
theorem annular_local_image_ball_eq_jordanInterior
    (e : OpenPartialHomeomorph ℂ ℂ) (H : ℂ ≃ₜ ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hsource : closedBall c r ⊆ e.source)
    (hboundary : e '' sphere c r = frontier (jordanInterior H)) :
    e '' ball c r = jordanInterior H := by
  classical
  let U : Set ℂ := e '' ball c r
  have hU : IsOpen U := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hsource)
  have hc : IsCompact (e '' closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn.mono hsource)
  have hcl : closure U = e '' closedBall c r := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono ball_subset_closedBall) hc.isClosed
    · have he : ContinuousOn e (closure (ball c r)) := by
        rw [closure_ball c hr.ne']
        exact e.continuousOn.mono hsource
      simpa only [closure_ball c hr.ne'] using he.image_closure
  have hfront : frontier U = frontier (jordanInterior H) := by
    rw [hU.frontier_eq, hcl]
    change e '' closedBall c r \ e '' ball c r = _
    rw [← (e.injOn.mono hsource).image_sdiff_subset ball_subset_closedBall,
      closedBall_sdiff_ball, hboundary]
  have hUb : Bornology.IsBounded U := hc.isBounded.subset
    (image_mono ball_subset_closedBall)
  have hpair : Pairwise (Disjoint on fun _ : Unit => closure (jordanInterior H)) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  have hinside : U ⊆ jordanInterior H := by
    have h := open_subset_finite_jordanInteriors_of_frontier_subset
      (fun _ : Unit => H) hpair hU hUb
      (by
        intro z hz
        exact mem_iUnion.mpr ⟨(), frontier_subset_closure (hfront ▸ hz)⟩)
      (fun _ z hz => hfront.symm ▸ hz)
    intro z hz
    obtain ⟨_, hi⟩ := mem_iUnion.mp (h hz)
    exact hi
  have hcenter : e c ∈ U := ⟨c, mem_ball_self hr, rfl⟩
  have hcover : jordanInterior H ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hzcl
      have hzf : z ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hzcl, hzU⟩
      have hzH : z ∈ frontier (jordanInterior H) := hfront ▸ hzf
      exact hzH.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hz)
  have hsides := (isConnected_jordanInterior H).isPreconnected.subset_or_subset
    hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)) hcover
  apply Subset.antisymm hinside
  rcases hsides with h | h
  · exact h
  · exact (h (hinside hcenter) (subset_closure hcenter)).elim

/-- Coefficients of the actual pullback of `Re(z) dIm(z)`. -/
def annularAreaPullbackP (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (F z).re * ((fderiv ℝ F z) 1).im

def annularAreaPullbackQ (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (F z).re * ((fderiv ℝ F z) Complex.I).im

/-- The exterior derivative of the actual area pullback is the actual
Frechet derivative determinant. Symmetry of the actual second derivative
cancels the second-order terms. -/
theorem annular_area_pullback_curl {F : ℂ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ ∞ F z) :
    (fderiv ℝ (annularAreaPullbackQ F) z) 1 -
      (fderiv ℝ (annularAreaPullbackP F) z) Complex.I = (fderiv ℝ F z).det := by
  have hFd : HasFDerivAt F (fderiv ℝ F z) z :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1)
      (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).differentiableAt
        (by norm_num)
  have hre := Complex.reCLM.hasFDerivAt.comp z hFd
  have himOne := Complex.imCLM.hasFDerivAt.comp z
    (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const (1 : ℂ) z))
  have himI := Complex.imCLM.hasFDerivAt.comp z
    (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const Complex.I z))
  have hp := hre.mul himOne
  have hq := hre.mul himI
  change HasFDerivAt (fun w => (F w).re * ((fderiv ℝ F w) 1).im) _ z at hp
  change HasFDerivAt (fun w => (F w).re * ((fderiv ℝ F w) Complex.I).im) _ z at hq
  change (fderiv ℝ (fun w => (F w).re * ((fderiv ℝ F w) Complex.I).im) z) 1 -
    (fderiv ℝ (fun w => (F w).re * ((fderiv ℝ F w) 1).im) z) Complex.I = _
  rw [hq.fderiv, hp.fderiv, complex_real_det_columns]
  simp only [_root_.add_apply, _root_.smul_apply, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero,
    zero_add, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul]
  have hs := hF.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide) (1 : ℂ) Complex.I
  rw [hs]
  ring

/-- The actual chain rule identifies the area integral around the image
circuit with the integral of the actual area pullback on the source.
No regularity or injectivity of the image circuit is required here. -/
theorem annular_area_pullback_integral {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ ∞ γ) (hγU : ∀ t, γ t ∈ U) :
    planarFormIntegral (annularAreaPullbackP F) (annularAreaPullbackQ F) γ =
      planarFormIntegral (fun _ => 0) Complex.re (F ∘ γ) := by
  unfold planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  have hFt := (hF.contDiffAt (hU.mem_nhds (hγU t))).differentiableAt (by simp)
  have hγt := hγ.differentiable (by simp) t
  have hder : deriv (F ∘ γ) t = (fderiv ℝ F (γ t)) (deriv γ t) :=
    (hFt.hasFDerivAt.comp_hasDerivAt t hγt.hasDerivAt).deriv
  have him := complexCovector_apply
    (Complex.imCLM.comp (fderiv ℝ F (γ t))) (deriv γ t)
  simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply] at him
  dsimp only [annularAreaPullbackP, annularAreaPullbackQ, comp_apply]
  rw [hder, him]
  ring

theorem annular_area_pullback_contDiffOn {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (annularAreaPullbackP F) U ∧
      ContDiffOn ℝ ∞ (annularAreaPullbackQ F) U := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hre := Complex.reCLM.contDiff.comp_contDiffOn hF
  constructor
  · exact hre.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))))
  · exact hre.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hd.clm_apply (contDiffOn_const (c := Complex.I))))

/-- Green on a source disk identifies the actual oriented area of its
image circuit with the integral of the actual Jacobian. The map is only
required to be smooth near the source disk, and can be arbitrary elsewhere. -/
theorem annular_local_area_integral_eq_jacobian
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (hsource : closedBall c r ⊆ U) :
    planarFormIntegral (fun _ => 0) Complex.re (F ∘ unitCircleParam c r) =
      ∫ z in ball c r, (fderiv ℝ F z).det := by
  have hγ : ContDiff ℝ ∞ (unitCircleParam c r) :=
    (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)
  have hγK (t : ℝ) : unitCircleParam c r t ∈ closedBall c r := by
    apply sphere_subset_closedBall
    simpa only [unitCircleParam, abs_of_pos hr] using
      circleMap_mem_sphere' c r (2 * Real.pi * t)
  have hγU (t : ℝ) : unitCircleParam c r t ∈ U := hsource (hγK t)
  obtain ⟨hP, hQ⟩ := annular_area_pullback_contDiffOn hU hF
  obtain ⟨p, hp, hep, _⟩ := exists_smooth_collar_extension hU isClosed_closedBall
    hsource hP 0
  obtain ⟨q, hq, heq, _⟩ := exists_smooth_collar_extension hU isClosed_closedBall
    hsource hQ 0
  have htrace : planarFormIntegral p q (unitCircleParam c r) =
      planarFormIntegral (annularAreaPullbackP F) (annularAreaPullbackQ F)
        (unitCircleParam c r) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hep.self_of_nhdsSet (hγK t), heq.self_of_nhdsSet (hγK t)]
  calc
    _ = planarFormIntegral (annularAreaPullbackP F) (annularAreaPullbackQ F)
        (unitCircleParam c r) := (annular_area_pullback_integral hU hF _ hγ hγU).symm
    _ = planarFormIntegral p q (unitCircleParam c r) := htrace.symm
    _ = ∫ z in ball c r, (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I :=
      translated_disk_green hp hq c hr
    _ = _ := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro z hz
      change (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I = (fderiv ℝ F z).det
      have hepz := hep.filter_mono (nhds_le_nhdsSet (ball_subset_closedBall hz))
      have heqz := heq.filter_mono (nhds_le_nhdsSet (ball_subset_closedBall hz))
      rw [hepz.fderiv_eq, heqz.fderiv_eq]
      exact annular_area_pullback_curl
        (hF.contDiffAt (hU.mem_nhds (hsource (ball_subset_closedBall hz))))

end
end TightVer401
