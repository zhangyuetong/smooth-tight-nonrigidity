import TightVer401.ConcaveJetJoinAcceleration
import TightVer401.ConcaveJetJoinMomentVector
import TightVer401.ConcaveJetJoinPiecewiseMoments
import TightVer401.ConcaveJetJoinGerms

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem exists_jetAcceleration_positive_floor {L : ℝ} (hL : 0 ≤ L)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hapos : ∀ x ∈ Icc 0 L, 0 < a x) (hbpos : ∀ x ∈ Icc 0 L, 0 < b x) :
    ∃ μ > 0, (∀ x ∈ Icc 0 L, μ ≤ a x) ∧ (∀ x ∈ Icc 0 L, μ ≤ b x) := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hL⟩⟩ ha.continuousOn
  obtain ⟨y, hy, hmin'⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hL⟩⟩ hb.continuousOn
  exact ⟨min (a x) (b y), lt_min (hapos x hx) (hbpos y hy),
    fun z hz => (min_le_left _ _).trans (hmin hz),
    fun z hz => (min_le_right _ _).trans (hmin' hz)⟩

/-- The actual vector moment equality gives both scalar endpoint constraints. -/
theorem concaveJetJoin_endpoint_of_affine_moment {L c : ℝ} (hc : c ∈ Ioo 0 L)
    {qL qR a : ℝ → ℝ} (hqL : ContDiff ℝ ∞ qL) (hqR : ContDiff ℝ ∞ qR)
    (ha : ContDiff ℝ ∞ a) (hv : qL c = qR c) (hd : deriv qL c = deriv qR c)
    (hm : jetAccelerationMoment 0 L jetAffineMomentVector a =
      jetAccelerationMoment 0 L jetAffineMomentVector
        (concaveJetJoinBlendPiecewise c (fun x => -deriv (deriv qL) x)
          (fun x => -deriv (deriv qR) x))) :
    concaveJetReconstruction 0 (qL 0) (deriv qL 0) a L = qR L ∧
      deriv (concaveJetReconstruction 0 (qL 0) (deriv qL 0) a) L = deriv qR L := by
  have hqL₂ := (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hqL).2)).2
  have hqR₂ := (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hqR).2)).2
  have hia := (ha.continuous.smul jetAffineMomentVector_contDiff.continuous).intervalIntegrable (μ := volume) 0 L
  have hip := concaveJetJoinBlendPiecewise_intervalIntegrable (c := c) (A := 0) (B := L)
    hqL₂.neg.continuous hqR₂.neg.continuous jetAffineMomentVector_contDiff.continuous
  obtain ⟨hM, hF⟩ := (jetAffineMoment_eq_iff 0 L hia hip).mp hm
  have hsM := concaveJetJoinBlendPiecewise_interval_split (E := ℝ)
    (f := fun _ => (1 : ℝ)) hc.1.le hc.2.le hqL₂.neg.continuous hqR₂.neg.continuous continuous_const
  have hsF := concaveJetJoinBlendPiecewise_interval_split (E := ℝ)
    (f := fun x : ℝ => x) hc.1.le hc.2.le hqL₂.neg.continuous hqR₂.neg.continuous continuous_id
  simp only [smul_eq_mul, mul_one] at hsM
  simp only [smul_eq_mul] at hsF
  simp_rw [mul_comm] at hsF
  exact concaveJetReconstruction_piecewise_endpoint hqL hqR ha 0 c L hv hd
    (hM.trans hsM) (hF.trans hsF)

end
end TightVer401
