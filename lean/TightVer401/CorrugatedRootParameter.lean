import TightVer401.CorrugatedRootJoint
import TightVer401.CorrugatedRootExistence

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem corrugatedRootIntegral_hasDerivAt (ε k : ℝ) :
    HasDerivAt (corrugatedRootIntegral ε)
      (-corrugatedCosMoment ε 1 k - 2 * corrugatedCosMoment ε 2 k) k := by
  have hd := (corrugatedCosMoment_hasDerivAt ε 0 k).add
    ((corrugatedCosMoment_hasDerivAt ε 1 k).const_mul 2)
  have hfun : corrugatedRootIntegral ε =
      (fun t => corrugatedCosMoment ε 0 t + 2 * corrugatedCosMoment ε 1 t) :=
    funext (corrugatedRootIntegral_eq ε)
  have hd' := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrFun hfun t))
  have he : -corrugatedCosMoment ε (0 + 1) k + 2 * -corrugatedCosMoment ε (1 + 1) k =
      -corrugatedCosMoment ε 1 k - 2 * corrugatedCosMoment ε 2 k := by ring
  exact he ▸ hd'

theorem corrugatedRootIntegral_derivative_neg_at_root {ε k : ℝ} (hε : |ε| < 1)
    (hk : corrugatedRootIntegral ε k = 0) :
    -corrugatedCosMoment ε 1 k - 2 * corrugatedCosMoment ε 2 k < 0 := by
  have hz := corrugatedCosMoment_zero_pos hε k
  have hE := (corrugatedRootIntegral_zero_iff hε k).mp hk
  have hv := corrugated_variance_pos hε k
  rw [hE] at hv
  have hq : (1 / 4 : ℝ) < corrugatedCosMoment ε 2 k / corrugatedCosMoment ε 0 k := by
    norm_num at hv
    linarith
  have hq' := (lt_div_iff₀ hz).mp hq
  rw [corrugatedRootIntegral_eq] at hk
  linarith

def corrugatedRootValue (ε : ℝ) : ℝ :=
  if hε : |ε| < 1 then corrugatedRoot ε hε else 0

theorem corrugatedRootValue_spec {ε : ℝ} (hε : |ε| < 1) :
    corrugatedRootIntegral ε (corrugatedRootValue ε) = 0 := by
  simpa only [corrugatedRootValue, dif_pos hε] using corrugatedRoot_spec ε hε

theorem corrugatedRootValue_contDiffAt {ε : ℝ} (hε : |ε| < 1) :
    ContDiffAt ℝ ∞ corrugatedRootValue ε := by
  let F : ℝ × ℝ → ℝ := fun p => corrugatedRootIntegral p.1 p.2
  let k := corrugatedRoot ε hε
  have hk : corrugatedRootIntegral ε k = 0 := corrugatedRoot_spec ε hε
  have hc : ContDiffAt ℝ ∞ F (ε, k) := corrugatedRootIntegral_joint_contDiff.contDiffAt
  let D := fderiv ℝ F (ε, k) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hd : HasFDerivAt (fun t => F (ε, t)) D k :=
    (hc.differentiableAt (by simp)).hasFDerivAt.comp k (hasFDerivAt_prodMk_right ε k)
  have hd' := (corrugatedRootIntegral_hasDerivAt ε k).hasFDerivAt
  have heD : D = ContinuousLinearMap.toSpanSingleton ℝ
      (-corrugatedCosMoment ε 1 k - 2 * corrugatedCosMoment ε 2 k) := hd.unique hd'
  have hn := (corrugatedRootIntegral_derivative_neg_at_root hε hk).ne
  have hi : D.IsInvertible := by
    rw [heD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hn), ?_⟩
    ext x
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul]
  let ψ := hc.implicitFunction (by simp) hi
  have hs : ContDiffAt ℝ ∞ ψ ε := hc.contDiffAt_implicitFunction (by simp) hi
  have he : ∀ᶠ t in 𝓝 ε, F (t, ψ t) = F (ε, k) :=
    hc.eventually_apply_implicitFunction (by simp) hi
  have hv : ∀ᶠ t in 𝓝 ε, |t| < 1 :=
    (continuous_abs.tendsto ε).eventually (gt_mem_nhds hε)
  have heq : corrugatedRootValue =ᶠ[𝓝 ε] ψ := by
    filter_upwards [hv, he] with t ht hroot
    have hrt : corrugatedRootIntegral t (ψ t) = 0 := hroot.trans hk
    simp only [corrugatedRootValue, dif_pos ht]
    exact ((corrugatedRoot_eq_iff t ht (ψ t)).mp hrt).symm
  exact hs.congr_of_eventuallyEq heq

theorem corrugatedRootValue_contDiffOn :
    ContDiffOn ℝ ∞ corrugatedRootValue {ε : ℝ | |ε| < 1} :=
  fun _ hε => (corrugatedRootValue_contDiffAt hε).contDiffWithinAt

end
end TightVer401
