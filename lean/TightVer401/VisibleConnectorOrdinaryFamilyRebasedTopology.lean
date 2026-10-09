import TightVer401.VisibleConnectorTerminalPositiveTrace
import TightVer401.VisibleConnectorOrdinaryFamilySourceEnclosure
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual topology of the SAME terminal after the increasing displaced phase.
No inverse or new filling is chosen; its full range and old filling survive. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A continuous actual phase with one physical-period drift covers ℝ. -/
theorem visibleConnectorOrdinaryFamily_rebased_phase_surjective
    {a : ℝ → ℝ} {L : ℝ} (ha : Continuous a) (hL : 0 < L)
    (hshift : ∀ s, a (s + L) = a s + L) : Surjective a := by
  have hnat : ∀ n : ℕ, ∀ s, a (s + (n : ℝ) * L) = a s + (n : ℝ) * L := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hshift, ih]
      ring
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y - a 0| / L)
  have habs : |y - a 0| < (n : ℝ) * L := (div_lt_iff₀ hL).mp hn
  have hupper : a ((n : ℝ) * L) = a 0 + (n : ℝ) * L := by
    simpa only [zero_add] using hnat n 0
  have hnegative := hnat n (-((n : ℝ) * L))
  rw [neg_add_cancel] at hnegative
  have hlower : a (-((n : ℝ) * L)) = a 0 - (n : ℝ) * L := by linarith
  apply intermediate_value_univ (-((n : ℝ) * L)) ((n : ℝ) * L) ha
  rw [hlower, hupper]
  exact ⟨by linarith [neg_abs_le (y - a 0)], by linarith [le_abs_self (y - a 0)]⟩

/-- Rebased source range is literally the original terminal range. -/
theorem visibleConnectorOrdinaryFamily_rebased_range
    {V : Type*} {T : ℝ → V} {a : ℝ → ℝ} {L : ℝ}
    (ha : Continuous a) (hL : 0 < L) (hshift : ∀ s, a (s + L) = a s + L) :
    range (fun s => T (a s)) = range T := by
  apply Subset.antisymm
  · rintro z ⟨s, rfl⟩
    exact ⟨a s, rfl⟩
  · rintro z ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := visibleConnectorOrdinaryFamily_rebased_phase_surjective ha hL hshift s
    exact ⟨t, by change T (a t) = T s; rw [ht]⟩

/-- Positive phase speed and its SAME shift preserve injectivity modulo L. -/
theorem visibleConnectorOrdinaryFamily_rebased_injOn
    {V : Type*} {T : ℝ → V} {a : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : Periodic T L) (hi : InjOn T (Ico 0 L))
    (hapos : ∀ s, 0 < deriv a s) (hshift : ∀ s, a (s + L) = a s + L) :
    InjOn (fun s => T (a s)) (Ico 0 L) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hm : StrictMono a := strictMono_of_deriv_pos hapos
  have hLift := periodicComplexCurve_lift_injective hp hi
  intro s hs t ht he
  have hquot : (a s : AddCircle L) = (a t : AddCircle L) := by
    apply hLift
    simpa only [hp.lift_coe] using he
  obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int L (a s) (a t)).mp hquot
  have hst : s < t + L := by linarith [hs.2, ht.1]
  have hts : t < s + L := by linarith [ht.2, hs.1]
  have habove := hm hts
  have hbelow := hm hst
  rw [hshift] at habove hbelow
  have hkhi : (k : ℝ) < 1 := by nlinarith [hk]
  have hklo : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk]
  have hkhi' : k < 1 := by exact_mod_cast hkhi
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkzero : k = 0 := by omega
  rw [hkzero] at hk
  simp only [Int.cast_zero, zero_mul, add_zero] at hk
  exact hm.injective hk

/-- All genuine terminal geometry survives the SAME increasing phase,
including actual derivative determinant and positive origin argument turn. -/
theorem visibleConnectorOrdinaryFamily_rebased_terminal_fields
    {L : ℝ} (hL : 0 < L) {T : ℝ → Coord} {a : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (ha : ContDiff ℝ ∞ a)
    (hp : Periodic T L) (hi : InjOn T (Ico 0 L))
    (hne : ∀ s, positiveExitComplexTrace T s ≠ 0)
    (hdet : ∀ s, 0 < visibleConnectorDet (T s) (deriv T s))
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L)
    (hapos : ∀ s, 0 < deriv a s) (hshift : ∀ s, a (s + L) = a s + L) :
    let Ta := fun s => T (a s)
    ContDiff ℝ ∞ Ta ∧ Periodic Ta L ∧ InjOn Ta (Ico 0 L) ∧
      (∀ s, positiveExitComplexTrace Ta s ≠ 0) ∧
      (∀ s, 0 < visibleConnectorDet (Ta s) (deriv Ta s)) ∧
      HasPositiveArgumentTurn (positiveExitComplexTrace Ta) L ∧ range Ta = range T := by
  let Ta := fun s => T (a s)
  have hs : ContDiff ℝ ∞ Ta := hT.comp ha
  have hpa : Periodic Ta L := by intro s; dsimp [Ta]; rw [hshift s, hp (a s)]
  have hia := visibleConnectorOrdinaryFamily_rebased_injOn hL hp hi hapos hshift
  have hnea : ∀ s, positiveExitComplexTrace Ta s ≠ 0 := fun s => hne (a s)
  have hda (s : ℝ) : deriv Ta s = deriv a s • deriv T (a s) := by
    exact (((hT.differentiable (by simp) (a s)).hasDerivAt).scomp s
      ((ha.differentiable (by simp) s).hasDerivAt)).deriv
  have hdeta : ∀ s, 0 < visibleConnectorDet (Ta s) (deriv Ta s) := by
    intro s
    rw [hda s]
    have he : visibleConnectorDet (Ta s) (deriv a s • deriv T (a s)) =
        deriv a s * visibleConnectorDet (T (a s)) (deriv T (a s)) := by
      simp only [Ta, visibleConnectorDet, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    exact mul_pos (hapos s) (hdet (a s))
  obtain ⟨hcn, hpn, hin, hregn, hnen, htn, hrn⟩ :=
    visibleConnectorTerminalNormalizedTrace_fields hL hT hp hne hdet hturn hi
  obtain ⟨phi, hphi, hproj, hphiShift⟩ :=
    positiveExit_actual_positive_argument_lift hcn hpn hnen htn
  have hta : HasPositiveArgumentTurn (positiveExitComplexTrace Ta) L := by
    refine ⟨fun s => phi (a s / L), hphi.continuous.comp (ha.continuous.div_const L), ?_, ?_⟩
    · intro s
      have he : L * (a s / L) = a s := by field_simp [hL.ne']
      simpa only [visibleConnectorTerminalNormalizedTrace, he, positiveExitComplexTrace,
        Function.comp_apply, Ta] using hproj (a s / L)
    · have hendpoint : a L / L = a 0 / L + 1 := by
        have h := hshift 0
        simp only [zero_add] at h
        rw [h]
        field_simp [hL.ne']
      change phi (a L / L) - phi (a 0 / L) = 2 * Real.pi
      rw [hendpoint, hphiShift]
      ring
  exact ⟨hs, hpa, hia, hnea, hdeta, hta,
    visibleConnectorOrdinaryFamily_rebased_range ha.continuous hL hshift⟩

/-- The SAME original H is a positive Jordan filling of the normalized
rebased terminal. Its boundary, positivity and full range are constructed. -/
theorem visibleConnectorOrdinaryFamily_rebased_same_positive_jordan
    {L : ℝ} (hL : 0 < L) {T : ℝ → Coord} {a : ℝ → ℝ} (H : ℂ ≃ₜ ℂ)
    (hT : ContDiff ℝ ∞ T) (ha : ContDiff ℝ ∞ a)
    (hp : Periodic T L) (hi : InjOn T (Ico 0 L))
    (hne : ∀ s, positiveExitComplexTrace T s ≠ 0)
    (hdet : ∀ s, 0 < visibleConnectorDet (T s) (deriv T s))
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L)
    (hapos : ∀ s, 0 < deriv a s) (hshift : ∀ s, a (s + L) = a s + L)
    (hfront : range (positiveExitComplexTrace T) = frontier (jordanInterior H))
    (h0 : (0 : ℂ) ∈ jordanInterior H) :
    PositiveJordanParametrization H
      (visibleConnectorTerminalNormalizedTrace L (fun s => T (a s))) ∧
      range (fun s => T (a s)) = range T ∧
      range (visibleConnectorTerminalNormalizedTrace L (fun s => T (a s))) =
        frontier (jordanInterior H) := by
  obtain ⟨hs, hpa, hia, hnea, hdeta, hta, hra⟩ :=
    visibleConnectorOrdinaryFamily_rebased_terminal_fields hL hT ha hp hi hne hdet hturn hapos hshift
  obtain ⟨hcn, hpn, hin, hregn, hnen, htn, hrn⟩ :=
    visibleConnectorTerminalNormalizedTrace_fields hL hs hpa hnea hdeta hta hia
  have hcrange : range (positiveExitComplexTrace (fun s => T (a s))) =
      range (positiveExitComplexTrace T) := by
    change range (fun s => positiveExitComplexTrace T (a s)) = range (positiveExitComplexTrace T)
    exact visibleConnectorOrdinaryFamily_rebased_range ha.continuous hL hshift
  have hboundary : range (visibleConnectorTerminalNormalizedTrace L (fun s => T (a s))) =
      frontier (jordanInterior H) := hrn.trans (hcrange.trans hfront)
  have himage : visibleConnectorTerminalNormalizedTrace L (fun s => T (a s)) '' Icc 0 1 =
      range (visibleConnectorTerminalNormalizedTrace L (fun s => T (a s))) := by
    apply Subset.antisymm (image_subset_range _ _)
    rintro z ⟨t, rfl⟩
    let h1 : 0 < (1 : ℝ) := by norm_num
    refine ⟨toIcoMod h1 0 t, Ico_subset_Icc_self (toIcoMod_mem_Ico' h1 t), ?_⟩
    symm
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul h1 0 t]
    exact hpn.zsmul (toIcoDiv h1 0 t) _
  have hclosed : visibleConnectorTerminalNormalizedTrace L (fun s => T (a s)) 1 =
      visibleConnectorTerminalNormalizedTrace L (fun s => T (a s)) 0 := by
    simpa only [zero_add] using hpn 0
  refine ⟨⟨hcn, hpn, hin, hregn, himage.trans hboundary, ?_⟩, hra, hboundary⟩
  exact positiveExit_positive_turn_all_interior_lifts hcn.continuous hclosed htn H hboundary.subset h0

end
end TightVer401


