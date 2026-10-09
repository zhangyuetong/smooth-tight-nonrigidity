import TightVer401.PositiveExitConstructionFirstIntegral
import TightVer401.FermiSupportFlowExistence
import TightVer401.SeamCompactCollar
import TightVer401.ThinBandLocalCalculus
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! A conserved actual smooth first integral proves full return identity,
not merely multiplier one. The scalar family is the retained constructed
ODE family; transverse local injection is derived from its actual label
derivative. The final Fermi adapter still requires proving the actual
pullback label's differential annihilation for the selected Fermi root. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Conservation on every sufficiently near trajectory of an actual smooth
full-period scalar family, derived by differentiation on the whole interval. -/
theorem positiveExit_actual_flow_label_conserved {C f u : Coord → ℝ}
    {W V : Set Coord} {P : ℝ} (hP : 0 < P)
    (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W)
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    (hvs : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V)
    (hconserve : ∀ p ∈ W, fderiv ℝ C p (![1, f p] : Coord) = 0) :
    ∃ ε > 0, ∀ x : ℝ, |x| ≤ ε →
      C (![P, u ![P, x]] : Coord) = C (![0, u ![0, x]] : Coord) := by
  obtain ⟨ε, hε, hstrip⟩ := seam_compact_axis_open_collar isCompact_Icc hV hvs
  refine ⟨ε, hε, fun x hx => ?_⟩
  let g : ℝ → ℝ := fun r => C ![r, u ![r, x]]
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) : HasDerivAt g 0 r := by
    have hp := hstrip r hr x hx
    have hsu := scalarFlowPeriod_slice0_hasDerivAt hV hu hp
    have hgraph := ruled_graph_hasDerivAt hsu
    have hcp := himage (![r, x] : Coord) hp
    simp only [Matrix.cons_val_zero] at hcp
    have hdc := (((hC _ hcp).contDiffAt (hW.mem_nhds hcp)).differentiableAt (by simp)).hasFDerivAt
    have hh := hdc.comp_hasDerivAt r hgraph
    change HasDerivAt g
      (fderiv ℝ C (![r, u ![r, x]] : Coord) (![1, coordPartial 0 u ![r, x]] : Coord)) r at hh
    rw [hode _ hp] at hh
    simp only [Matrix.cons_val_zero] at hh
    rw [hconserve _ hcp] at hh
    exact hh
  have hdiff : DifferentiableOn ℝ g (Icc (0 : ℝ) P) :=
    fun r hr => (hd r hr).differentiableAt.differentiableWithinAt
  have hzero : ∀ r ∈ Icc (0 : ℝ) P,
      fderivWithin ℝ g (Icc (0 : ℝ) P) r = 0 := by
    intro r hr
    have hh : HasFDerivWithinAt g (0 : ℝ →L[ℝ] ℝ) (Icc (0 : ℝ) P) r := by
      convert! (hd r hr).hasFDerivAt.hasFDerivWithinAt using 1
      ext a
      simp
    exact hh.fderivWithin (uniqueDiffOn_Icc hP r hr)
  exact (convex_Icc (0 : ℝ) P).is_const_of_fderivWithin_eq_zero hdiff hzero
    ⟨hP.le, le_rfl⟩ ⟨le_rfl, hP.le⟩

/-- Actual conservation and an actual nonzero transverse label derivative
force identity of the entire nearby return map. No identity-return premise
or locally-injective-label witness is supplied. -/
theorem positiveExit_actual_flow_return_identity {C f u : Coord → ℝ}
    {W V : Set Coord} {P : ℝ} (hP : 0 < P)
    (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W)
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    (hvs : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0)
    (hinitial : (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hperiod : (fun x : ℝ => C (![P, x] : Coord)) =ᶠ[𝓝 (0 : ℝ)]
      (fun x : ℝ => C (![0, x] : Coord)))
    (hconserve : ∀ p ∈ W, fderiv ℝ C p (![1, f p] : Coord) = 0)
    (htransverse : coordPartial 1 C (![0, 0] : Coord) ≠ 0) :
    (fun x : ℝ => u ![P, x]) =ᶠ[𝓝 (0 : ℝ)] id := by
  have h0 : (![0, 0] : Coord) ∈ V := hvs 0 ⟨le_rfl, hP.le⟩
  have hP0 : (![P, 0] : Coord) ∈ V := hvs P ⟨hP.le, le_rfl⟩
  have hC0 : (![0, 0] : Coord) ∈ W := by
    have hh := himage (![0, 0] : Coord) h0
    simpa only [Matrix.cons_val_zero, hzero 0 ⟨le_rfl, hP.le⟩] using hh
  let c : ℝ → ℝ := fun x => C ![0, x]
  have hι : ContDiff ℝ ∞ (fun x : ℝ => (![0, x] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))
      exact contDiff_const
    · change ContDiff ℝ ∞ (id : ℝ → ℝ)
      exact contDiff_id
  have hc : ContDiffAt ℝ ∞ c 0 :=
    ((hC _ hC0).contDiffAt (hW.mem_nhds hC0)).comp 0 hι.contDiffAt
  have hcd : HasDerivAt c (coordPartial 1 C (![0, 0] : Coord)) 0 :=
    exitGraph_slice_hasDerivAt hW hC hC0
  have hci : Function.Injective (fderiv ℝ c 0) := by
    intro a b hab
    rw [hcd.hasFDerivAt.fderiv] at hab
    change a * coordPartial 1 C (![0, 0] : Coord) =
      b * coordPartial 1 C (![0, 0] : Coord) at hab
    have hz : (a - b) * coordPartial 1 C (![0, 0] : Coord) = 0 := by nlinarith [hab]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right htransverse)
  obtain ⟨J, hJ, hinj⟩ := exists_local_injOn_of_injective_strictFDeriv
    (hc.hasStrictFDerivAt (by simp)) hci
  obtain ⟨ε, hε, hlabels⟩ := positiveExit_actual_flow_label_conserved hP hW hC
    hV hu himage hode hvs hconserve
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0, |x| ≤ ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
    exact (by simpa only [mem_ball, Real.dist_eq, sub_zero] using hx : |x| < ε).le
  have hρ : ContDiff ℝ ∞ (fun x : ℝ => (![P, x] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun _ : ℝ => P)
      exact contDiff_const
    · change ContDiff ℝ ∞ (id : ℝ → ℝ)
      exact contDiff_id
  have hRc : ContinuousAt (fun x : ℝ => u ![P, x]) 0 :=
    (((hu _ hP0).contDiffAt (hV.mem_nhds hP0)).comp 0 hρ.contDiffAt).continuousAt
  have hRt : Tendsto (fun x : ℝ => u ![P, x]) (𝓝 0) (𝓝 0) := by
    change Tendsto (fun x : ℝ => u ![P, x]) (𝓝 0) (𝓝 (u ![P, 0])) at hRc
    simpa only [hzero P ⟨hP.le, le_rfl⟩] using hRc
  have hRJ : ∀ᶠ x : ℝ in 𝓝 0, u ![P, x] ∈ J := hRt.eventually hJ
  have hperReturn := hRt.eventually hperiod
  filter_upwards [hsmall, hJ, hRJ, hinitial, hperReturn] with x hx hxJ hRxJ hix hper
  have he := hlabels x hx
  rw [hper, hix] at he
  exact hinj hRxJ hxJ he

/-- The retained actual Fermi flow construction plus a proved smooth regular
periodic conserved label constructs exactly the baseline identity return
family used by `exists_fermiExit_smooth_perturbation`. -/
theorem positiveExit_exists_fermi_identity_return {κ : ℝ → ℝ} {H C : Coord → ℝ}
    {U : Set Coord} {P : ℝ}
    (hP : 0 < P) (hκ : ContDiff ℝ ∞ κ)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (hC : ContDiffOn ℝ ∞ C U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r, 0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hperiod : (fun x : ℝ => C (![P, x] : Coord)) =ᶠ[𝓝 (0 : ℝ)]
      (fun x : ℝ => C (![0, x] : Coord)))
    (hconserve : ∀ p ∈ U,
      fderiv ℝ C p (![1, fermiSupportAsymptoticSlope κ H p] : Coord) = 0)
    (htransverse : coordPartial 1 C (![0, 0] : Coord) ≠ 0) :
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0, u q] : Coord) ∈ U) ∧
      (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ H ![q 0, u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V) ∧
      (∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0) ∧
      ((fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      ((fun x : ℝ => u ![P, x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      (∀ q ∈ V, (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H ![q 0, u q]).det < 0) := by
  obtain ⟨V, u, hV, hu, himage, hode, hvs, huzero, hi, _, hdet⟩ :=
    exists_fermiSupport_full_period_flow hP hκ hU hH hscale hseam hzero hpos
  exact ⟨V, u, hV, hu, himage, hode, hvs, huzero, hi,
    positiveExit_actual_flow_return_identity hP hU hC hV hu himage hode hvs huzero hi
      hperiod hconserve htransverse, hdet⟩

end
end TightVer401
