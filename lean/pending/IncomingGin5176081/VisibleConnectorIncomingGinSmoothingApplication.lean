import TightVer401.VisibleConnectorIncomingGinCarrier
import TightVer401.VisibleConnectorIncomingGinGerm
import TightVer401.RelativeSaddleSmoothing

/-! Invoke the published on-sides construction ONCE on the full fixed carrier.
The normal-side classifier and modification neighborhood are derived from the
actual height.  The resulting full open Gin and raw terminal equality
neighborhoods are constructed, rather than assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem visibleConnectorIncomingGinGerm_seam_range {L : ℝ} {gamma : ℝ → ℂ}
    (hperiod : Periodic gamma L) :
    seamNormalSeam gamma hperiod = range (fun s => seamComplexCoord (gamma s)) := by
  apply Subset.antisymm
  · rintro x ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨s, ?_⟩
    simpa only [seamNormalCoordinates_central] using (seamNormalNative_coe hperiod s 0).symm
  · rintro x ⟨s, rfl⟩
    refine ⟨periodProjection L s, ?_⟩
    simpa only [seamNormalCoordinates_central] using seamNormalNative_coe hperiod s 0

/-- Ordinary analytic seam data produce a final scalar on the SAME full V.
Gin is smooth only on GinU; raw is smooth only on Vraw.  The negative-height
carrier restriction is literal and supplies the required branch containment. -/
theorem visibleConnectorIncomingGin_exists_smoothed_full_carrier
    {L : ℝ} [hL : Fact (0 < L)] {gamma : ℝ → ℂ}
    (hgamma : ContDiff ℝ ∞ gamma) (hperiod : Periodic gamma L)
    (hregular : ∀ s, deriv gamma s ≠ 0) (hEmbed : Injective hperiod.lift)
    {B Gin raw : Coord → ℝ} {Vraw GinU : Set Coord}
    {pOriginal Tterminal : ℝ → Coord}
    (hVraw : IsOpen Vraw) (hGinU : IsOpen GinU) (hB : ContDiffOn ℝ ∞ B Vraw)
    (hGin : ContDiffOn ℝ ∞ Gin GinU) (hraw : ContDiffOn ℝ ∞ raw Vraw)
    (hGinNeg : ∀ x ∈ GinU, (planarHessian Gin x).det < 0)
    (hrawNeg : ∀ x ∈ Vraw, (planarHessian raw x).det < 0)
    (hSeamV : ∀ s, seamComplexCoord (gamma s) ∈ visibleConnectorIncomingGinCarrier Vraw GinU B)
    (hzero : ∀ s, B (seamComplexCoord (gamma s)) = 0)
    (honlyzero : ∀ x ∈ visibleConnectorIncomingGinCarrier Vraw GinU B,
      B x = 0 → x ∈ range (fun s => seamComplexCoord (gamma s)))
    (hnormal : ∀ s, fderiv ℝ B (seamComplexCoord (gamma s))
      (seamComplexCoord (Complex.I * deriv gamma s)) < 0)
    (hValue : ∀ s, Gin (seamComplexCoord (gamma s)) = raw (seamComplexCoord (gamma s)))
    (hGradient : ∀ s, planarGradient Gin (seamComplexCoord (gamma s)) =
      planarGradient raw (seamComplexCoord (gamma s)))
    (hOriginalCompact : IsCompact (range pOriginal)) (hTerminalCompact : IsCompact (range Tterminal))
    (hOriginalV : ∀ s, pOriginal s ∈ visibleConnectorIncomingGinCarrier Vraw GinU B)
    (hTerminalV : ∀ s, Tterminal s ∈ visibleConnectorIncomingGinCarrier Vraw GinU B)
    (hOriginalNegative : ∀ s, B (pOriginal s) < 0)
    (hTerminalPositive : ∀ s, 0 < B (Tterminal s))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let V := visibleConnectorIncomingGinCarrier Vraw GinU B
    let P : Set Coord := {y | B y < 0}
    ∃ N : Set Coord, ∃ H : Coord → ℝ, ∃ Oin Oterminal : Set Coord,
      IsOpen N ∧ seamNormalSeam gamma hperiod ⊆ N ∧
      closure N ⊆ V \ (range pOriginal ∪ range Tterminal) ∧
      ContDiffOn ℝ ∞ H V ∧ (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      IsOpen Oin ∧ range pOriginal ⊆ Oin ∧ Oin ⊆ V ∩ GinU ∧ EqOn H Gin Oin ∧
      IsOpen Oterminal ∧ range Tterminal ⊆ Oterminal ∧ Oterminal ⊆ V ∩ Vraw ∧ EqOn H raw Oterminal ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] relativeSaddlePiecewise P Gin raw) ∧
      (∀ x ∈ V, |H x - relativeSaddlePiecewise P Gin raw x| < epsilon ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise P Gin raw) x‖ < epsilon) := by
  let V := visibleConnectorIncomingGinCarrier Vraw GinU B
  let P : Set Coord := {y | B y < 0}
  have hV : IsOpen V := visibleConnectorIncomingGinCarrier_isOpen hVraw hGinU hB.continuousOn
  have hBV : ContDiffOn ℝ ∞ B V := visibleConnectorIncomingGinCarrier_contDiffOn hB
  have hSeam : seamNormalSeam gamma hperiod ⊆ V := by
    rw [visibleConnectorIncomingGinGerm_seam_range hperiod]
    rintro x ⟨s, rfl⟩
    exact hSeamV s
  have hSeamZero : ∀ x ∈ seamNormalSeam gamma hperiod, B x = 0 := by
    rw [visibleConnectorIncomingGinGerm_seam_range hperiod]
    rintro x ⟨s, rfl⟩
    exact hzero s
  have hSeamGin : seamNormalSeam gamma hperiod ⊆ GinU := by
    intro x hx
    rcases (hSeam hx).2 with hGin | hpos
    · exact hGin
    · have hp : 0 < B x := hpos
      rw [hSeamZero x hx] at hp
      exact False.elim (lt_irrefl (0 : ℝ) hp)
  have hSeamRaw : seamNormalSeam gamma hperiod ⊆ Vraw := fun x hx => (hSeam hx).1
  have hC : IsCompact (seamNormalSeam gamma hperiod) :=
    isCompact_range ((seamNormalNative_continuous hgamma hperiod).comp
      (continuous_id.prodMk continuous_const))
  obtain ⟨N, hN, hSeamN, hclosureN⟩ := visibleConnectorIncomingGinGerm_exists_modification_avoiding_both
    hV hC hOriginalCompact hTerminalCompact hSeam hSeamZero
    (by rintro x ⟨s, rfl⟩; exact hOriginalNegative s)
    (by rintro x ⟨s, rfl⟩; exact hTerminalPositive s)
  obtain ⟨r, hr, hclassify⟩ := visibleConnectorIncomingGin_exists_canonical_side_threshold
    hL.out hgamma hperiod hV hBV hSeamV hzero hnormal
  have hBoundary : V ∩ frontier P ⊆ seamNormalSeam gamma hperiod := by
    intro x hx
    rw [visibleConnectorIncomingGinGerm_seam_range hperiod]
    exact honlyzero x hx.1
      (visibleConnectorIncomingGin_sublevel_frontier_zero hV hBV.continuousOn x hx)
  have hPositiveDomain : V ∩ interior P ⊆ GinU := by
    intro x hx
    exact visibleConnectorIncomingGinCarrier_negative_subset Vraw GinU B
      ⟨hx.1, interior_subset hx.2⟩
  have hNegativeDomain : V ∩ interior Pᶜ ⊆ Vraw := fun x hx => hx.1.1
  have hSide (s t : ℝ) (ht : |t| < r) (_hne : t ≠ 0)
      (_hx : seamNormalCoordinates gamma (![s, t] : Coord) ∈ V) :
      seamNormalCoordinates gamma (![s, t] : Coord) ∈ P ↔ 0 < t :=
    (hclassify s t ht.le).2
  obtain ⟨H, hH, hHneg, hOld, _, _, hClose⟩ := exists_relative_saddle_smoothing_on_sides
    hgamma hperiod hregular hEmbed hV hN hGinU hVraw hSeam hSeamN hSeamGin hSeamRaw
    hBoundary hPositiveDomain hNegativeDomain hr hSide hGin hraw hValue hGradient
    hGinNeg hrawNeg hepsilon
  have hpN (s : ℝ) : pOriginal s ∉ N := by
    intro hn
    exact (hclosureN (subset_closure hn)).2 (Or.inl (mem_range_self s))
  have htN (s : ℝ) : Tterminal s ∉ N := by
    intro hn
    exact (hclosureN (subset_closure hn)).2 (Or.inr (mem_range_self s))
  have hOldIf : ∀ x ∈ V \ N,
      H =ᶠ[𝓝 x] (fun y => if B y < 0 then Gin y else raw y) := by
    intro x hx
    simpa only [relativeSaddlePiecewise, P, mem_setOf_eq] using hOld x hx
  have hOriginalGerm := visibleConnectorIncomingGin_retain_original_scalar_germ hV
    hBV.continuousOn hOriginalV hpN hOriginalNegative hOldIf
  have hTerminalGerm := visibleConnectorIncomingGinGerm_retain_terminal_scalar hV
    hBV.continuousOn hTerminalV htN hTerminalPositive hOldIf
  have hpGin (s : ℝ) : pOriginal s ∈ GinU :=
    visibleConnectorIncomingGinCarrier_negative_subset Vraw GinU B
      ⟨hOriginalV s, hOriginalNegative s⟩
  have htRaw (s : ℝ) : Tterminal s ∈ Vraw := (hTerminalV s).1
  obtain ⟨Oin, hOin, hpOin, hOinDomain, hEqGin⟩ :=
    visibleConnectorIncomingGinGerm_exists_open_branch_equality hV hGinU hOriginalV hpGin hOriginalGerm
  obtain ⟨Oterminal, hOterminal, htOterminal, hOTerminalDomain, hEqRaw⟩ :=
    visibleConnectorIncomingGinGerm_exists_open_branch_equality hV hVraw hTerminalV htRaw hTerminalGerm
  exact ⟨N, H, Oin, Oterminal, hN, hSeamN, hclosureN, hH, hHneg,
    hOin, hpOin, hOinDomain, hEqGin, hOterminal, htOterminal, hOTerminalDomain, hEqRaw, hOld, hClose⟩

end
end TightVer401
