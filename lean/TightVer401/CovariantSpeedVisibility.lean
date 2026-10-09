import TightVer401.CovariantSpeedEmbedding
import TightVer401.VisibilitySpeedStability

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem exists_covariantSpeedCurve_L1_visibility_threshold
    (L : ℝ) [Fact (0 < L)] {T R : ℝ} {ξ : ℂ} (N : ℕ)
    (hNT : (N : ℝ) * T = L) (hT : T ∈ Icc 0 L)
    (hξ : ξ ≠ 1) (hN : ξ ^ N = 1) (hR : 0 ≤ R)
    (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hPcell : ∀ t, P (t + T) = ξ * P t)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hbT : Function.Periodic b T)
    (U V : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hUL : Function.Periodic U L) (hVL : Function.Periodic V L)
    (hvisible : ∀ t, R < ‖covariantSpeedCurve T ξ b P t‖ ∧
      0 < inner ℝ (U t) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ b P t)) ∧
      0 < inner ℝ (V t) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ b P t))) :
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a T →
      (∫ t in 0..L, |a t - b t|) < η →
      ∀ t, R < ‖covariantSpeedCurve T ξ a P t‖ ∧
        0 < inner ℝ (U t) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ a P t)) ∧
        0 < inner ℝ (V t) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ a P t)) := by
  have hbcov : Function.Periodic (covariantSpeedCurve T ξ b P) L := by
    rw [← hNT]
    exact covariantSpeedCurve_periodic hb.continuous hP.continuous hbT hPcell hξ N hN
  have hbcurve := covariantSpeedCurve_contDiff T ξ hb hP
  have hδ := (periodicLift_contMDiff hbcurve hbcov).continuous
  have hUc := (periodicLift_contMDiff hU hUL).continuous
  have hVc := (periodicLift_contMDiff hV hVL).continuous
  have hvis : ∀ q ∈ (univ : Set (AddCircle L)), R < ‖hbcov.lift q‖ ∧
      0 < inner ℝ (hUL.lift q) (corrugatedVisibilityDirection R (hbcov.lift q)) ∧
      0 < inner ℝ (hVL.lift q) (corrugatedVisibilityDirection R (hbcov.lift q)) := by
    intro q _
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa only [Function.Periodic.lift_coe] using hvisible t
  obtain ⟨ε, hε, hmargin⟩ := exists_visibility_fixedDirection_threshold
    isCompact_univ hR hδ hUc hVc hvis
  obtain ⟨η, hη, hclose⟩ := exists_covariantSpeedCurve_L1_uniform_threshold hb.continuous hP.continuous hT hε
  refine ⟨η, hη, fun a ha haT hsmall t => ?_⟩
  have hacov : Function.Periodic (covariantSpeedCurve T ξ a P) L := by
    rw [← hNT]
    exact covariantSpeedCurve_periodic ha.continuous hP.continuous haT hPcell hξ N hN
  let q := periodProjection L t
  let x := AddCircle.equivIco L 0 q
  have hx : (x : ℝ) ∈ Icc 0 L := by
    have hm := x.property
    exact ⟨hm.1, by simpa only [zero_add] using hm.2.le⟩
  have hxq : periodProjection L (x : ℝ) = q := AddCircle.coe_equivIco
  have haeq : hacov.lift q = covariantSpeedCurve T ξ a P (x : ℝ) := by
    rw [← hxq]
    exact hacov.lift_coe _
  have hbeq : hbcov.lift q = covariantSpeedCurve T ξ b P (x : ℝ) := by
    rw [← hxq]
    exact hbcov.lift_coe _
  have hnear : ‖hacov.lift q - hbcov.lift q‖ < ε := by
    rw [haeq, hbeq]
    exact hclose a ha.continuous hsmall (x : ℝ) hx
  have hv := hmargin q (mem_univ q) (hacov.lift q) hnear
  simpa only [q, periodicLift_coe] using hv

end
end TightVer401
