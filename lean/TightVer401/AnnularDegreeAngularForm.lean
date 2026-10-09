import TightVer401.AnnularDegreeDefinitions
import OAI.Analysis.CircleDomains.Sobolev.ArgumentCircleIntegral
import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary

/-!
The actual normalized-argument pullback form of a smooth planar map.
Its closedness follows from the proved local-lift differential theorem, and
its boundary integral equals every continuous real lift's actual increment.
No rank or regularity assumption on the image boundary is imposed.
-/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff

/-- Actual smoothness supplies the smooth quotient branches of the pullback. -/
theorem annularArgumentPullback_smoothCircleOn {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y) : SmoothCircleOn (annularArgumentPullback f y) O := by
  intro z hz a ha
  exact (smoothCircleOn_centeredArgument y (f z) (hAvoid z hz) a ha).comp z
    (hf.contDiffAt (hO.mem_nhds hz))

/-- The pullback differential is computed from the actual Frechet derivative. -/
theorem annularArgumentPullback_circleFDeriv {f : ℂ → ℂ} {y z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hAvoid : f z ≠ y) (v : ℂ) :
    circleFDeriv (annularArgumentPullback f y) z v =
      ((fderiv ℝ f z v) / (f z - y)).im / (2 * Real.pi) := by
  change circleFDeriv (centeredArgument y ∘ f) z v = _
  rw [circleFDeriv_comp (isOpen_ne_fun continuous_id continuous_const)
    (smoothCircleOn_centeredArgument y) hf hAvoid]
  exact circleFDeriv_centeredArgument y hAvoid (fderiv ℝ f z v)

theorem annularAngularFormP_contDiffOn {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y) : ContDiffOn ℝ ∞ (annularAngularFormP f y) O :=
  (contDiffOn_circleFDeriv hO (annularArgumentPullback_smoothCircleOn hO hf hAvoid)).clm_apply
    contDiffOn_const

theorem annularAngularFormQ_contDiffOn {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y) : ContDiffOn ℝ ∞ (annularAngularFormQ f y) O :=
  (contDiffOn_circleFDeriv hO (annularArgumentPullback_smoothCircleOn hO hf hAvoid)).clm_apply
    contDiffOn_const

/-- Closedness is derived from local smooth real branches, even where the
actual derivative of the planar map degenerates. -/
theorem annularAngularForm_closed {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y) {z : ℂ} (hz : z ∈ O) :
    (fderiv ℝ (annularAngularFormQ f y) z) 1 =
      (fderiv ℝ (annularAngularFormP f y) z) Complex.I :=
  circleFDeriv_closed_complex hO (annularArgumentPullback_smoothCircleOn hO hf hAvoid) hz

theorem annularAngularForm_curl_zero {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y) {z : ℂ} (hz : z ∈ O) :
    (fderiv ℝ (annularAngularFormQ f y) z) 1 -
      (fderiv ℝ (annularAngularFormP f y) z) Complex.I = 0 :=
  sub_eq_zero.mpr (annularAngularForm_closed hO hf hAvoid hz)

/-- The boundary integral of the actual pullback equals the lift increment
for any smooth source path in the avoiding domain. In particular, the image
of a source loop need not be immersed or regularly parametrized. -/
theorem annularAngularForm_integral_eq_lift {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = normalizedArgument (f (γ t) - y)) :
    planarFormIntegral (annularAngularFormP f y) (annularAngularFormQ f y) γ =
      v 1 - v 0 := by
  unfold annularAngularFormP annularAngularFormQ
  simpa only [circleFormIntegral,
    show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using
    circleFormIntegral_constant_weight hO (annularArgumentPullback_smoothCircleOn hO hf hAvoid)
      (fun _ => 1) γ hγ hγO v hv hproj 1 (fun _ _ => rfl)

/-- A closed source loop gives an integer actual lift increment. -/
theorem annularArgumentPullback_lift_increment_integer {f : ℂ → ℂ} {y : ℂ}
    {γ : ℝ → ℂ} (hClosed : γ 1 = γ 0) (v : ℝ → ℝ)
    (hproj : ∀ t, (v t : UnitAddCircle) = normalizedArgument (f (γ t) - y)) :
    ∃ k : ℤ, v 1 - v 0 = (k : ℝ) := by
  have he : (v 1 : UnitAddCircle) = (v 0 : UnitAddCircle) := by
    rw [hproj 1, hproj 0, hClosed]
  obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int 1 (v 1) (v 0)).mp he
  refine ⟨k, ?_⟩
  rw [mul_one] at hk
  exact sub_eq_iff_eq_add.mpr (hk.trans (add_comm _ _))

/-- Consequently the actual angular integral around any smooth source loop
is integer-valued once expressed by any continuous actual argument lift. -/
theorem annularAngularForm_loop_integral_integer {f : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hAvoid : ∀ z ∈ O, f z ≠ y)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (hClosed : γ 1 = γ 0) (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = normalizedArgument (f (γ t) - y)) :
    ∃ k : ℤ,
      planarFormIntegral (annularAngularFormP f y) (annularAngularFormQ f y) γ = (k : ℝ) := by
  rw [annularAngularForm_integral_eq_lift hO hf hAvoid hγ hγO v hv hproj]
  exact annularArgumentPullback_lift_increment_integer hClosed v hproj

end
end TightVer401

