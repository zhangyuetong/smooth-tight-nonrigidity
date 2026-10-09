import TightVer401.VisibleConnectorFinalSmoothingBoundary
import TightVer401.VisibleConnectorFinalSmoothingCarrier
import TightVer401.VisibleConnectorFinalSmoothingSide

/-! One relative smoothing on the full constructed carrier. All domain, side,
modification and open boundary equality producers are proved in owned leaves.
Inputs below are actual scalar/height/curve facts, not a granted smoothing
package. The same raw domain remains in the same Cartesian target. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

 theorem visibleConnectorFinalSmoothing_seam_range {L : ℝ} {gamma : ℝ → ℂ}
    (hp : Periodic gamma L) :
    seamNormalSeam gamma hp = range (fun s => seamComplexCoord (gamma s)) := by
  apply Subset.antisymm
  · rintro x ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨s, ?_⟩
    simpa only [seamNormalCoordinates_central, periodProjection, QuotientAddGroup.mk'_apply] using (seamNormalNative_coe hp s 0).symm
  · rintro x ⟨s, rfl⟩
    refine ⟨periodProjection L s, ?_⟩
    simpa only [seamNormalCoordinates_central] using seamNormalNative_coe hp s 0

/-- Construct ONE final H and two explicit open boundary equality domains on
full fixed V, retaining the raw target and closed band. H's gradient inverse
is a separate subsequent construction. -/
theorem visibleConnectorFinalSmoothing_exists_full_scalar
    {L : ℝ} [hL : Fact (0 < L)] {gamma : ℝ → ℂ}
    (hgamma : ContDiff ℝ ∞ gamma) (hp : Periodic gamma L)
    (hreg : ∀ s, deriv gamma s ≠ 0) (hEmbed : Injective hp.lift)
    {B Gin raw : Coord → ℝ} {Vraw GinU K T C : Set Coord}
    (E : OpenPartialHomeomorph Coord Coord) (hRawTarget : Vraw ⊆ E.target)
    (hRawOpen : IsOpen Vraw) (hGinOpen : IsOpen GinU)
    (hB : ContDiffOn ℝ ∞ B Vraw)
    (hGin : ContDiffOn ℝ ∞ Gin GinU) (hraw : ContDiffOn ℝ ∞ raw Vraw)
    (hGinNeg : ∀ x ∈ GinU, (planarHessian Gin x).det < 0)
    (hrawNeg : ∀ x ∈ Vraw, (planarHessian raw x).det < 0)
    (hSeamRaw : ∀ s, seamComplexCoord (gamma s) ∈ Vraw)
    (hSeamGin : ∀ s, seamComplexCoord (gamma s) ∈ GinU)
    (hzero : ∀ s, B (seamComplexCoord (gamma s)) = 0)
    (honlyzero : ∀ x ∈ visibleConnectorFinalSmoothingCarrier Vraw GinU B,
      B x = 0 → x ∈ range (fun s => seamComplexCoord (gamma s)))
    (hnormal : ∀ s, fderiv ℝ B (seamComplexCoord (gamma s))
      (seamComplexCoord (Complex.I * deriv gamma s)) < 0)
    (hValue : ∀ s, Gin (seamComplexCoord (gamma s)) = raw (seamComplexCoord (gamma s)))
    (hGradient : ∀ s, planarGradient Gin (seamComplexCoord (gamma s)) =
      planarGradient raw (seamComplexCoord (gamma s)))
    (hK : IsCompact K) (hT : IsCompact T)
    (hKV : K ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B)
    (hTV : T ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B)
    (hnegative : ∀ x ∈ K, B x < 0) (hpositive : ∀ x ∈ T, 0 < B x)
    (hBand : C ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let V := visibleConnectorFinalSmoothingCarrier Vraw GinU B
    ∃ N : Set Coord, ∃ H : Coord → ℝ,
      IsOpen V ∧ V ⊆ E.target ∧ IsOpen N ∧ seamNormalSeam gamma hp ⊆ N ∧
      closure N ⊆ V \ (K ∪ T) ∧
      ContDiffOn ℝ ∞ H V ∧ (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ C, (planarHessian H x).det < 0) ∧
      (let Oin := visibleConnectorFinalSmoothingIncomingOpen V GinU N B
       IsOpen Oin ∧ K ⊆ Oin ∧ Oin ⊆ V ∩ GinU ∧ EqOn H Gin Oin) ∧
      (let Ot := visibleConnectorFinalSmoothingTerminalOpen V Vraw N B
       IsOpen Ot ∧ T ⊆ Ot ∧ Ot ⊆ V ∩ Vraw ∧ EqOn H raw Ot) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] relativeSaddlePiecewise {y | B y < 0} Gin raw) ∧
      ∀ x ∈ V, |H x - relativeSaddlePiecewise {y | B y < 0} Gin raw x| < epsilon ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise {y | B y < 0} Gin raw) x‖ < epsilon := by
  let V := visibleConnectorFinalSmoothingCarrier Vraw GinU B
  let P : Set Coord := {y | B y < 0}
  have hV : IsOpen V := visibleConnectorFinalSmoothingCarrier_open hRawOpen hGinOpen hB.continuousOn
  have hBV : ContDiffOn ℝ ∞ B V := hB.mono (fun _ hx => hx.1)
  have hSeamV : seamNormalSeam gamma hp ⊆ V := by
    rw [visibleConnectorFinalSmoothing_seam_range hp]
    rintro x ⟨s, rfl⟩
    exact ⟨hSeamRaw s, Or.inl (hSeamGin s)⟩
  have hSR : seamNormalSeam gamma hp ⊆ Vraw := fun _ hx => (hSeamV hx).1
  have hSG : seamNormalSeam gamma hp ⊆ GinU := by
    rw [visibleConnectorFinalSmoothing_seam_range hp]
    rintro x ⟨s, rfl⟩
    exact hSeamGin s
  have hSZ : ∀ x ∈ seamNormalSeam gamma hp, B x = 0 := by
    rw [visibleConnectorFinalSmoothing_seam_range hp]
    rintro x ⟨s, rfl⟩
    exact hzero s
  have hCompact : IsCompact (seamNormalSeam gamma hp) :=
    isCompact_range ((seamNormalNative_continuous hgamma hp).comp
      (continuous_id.prodMk continuous_const))
  obtain ⟨N, hN, hSN, hClosure⟩ := visibleConnectorFinalSmoothing_exists_modification
    hV hCompact hK hT hSeamV hSZ hnegative hpositive
  obtain ⟨r, hr, hclassify⟩ := visibleConnectorFinalSmoothing_exists_canonical_side_threshold
    hL.out hgamma hp hV hBV (fun s => ⟨hSeamRaw s, Or.inl (hSeamGin s)⟩) hzero hnormal
  have hBoundary : V ∩ frontier P ⊆ seamNormalSeam gamma hp := by
    intro x hx
    rw [visibleConnectorFinalSmoothing_seam_range hp]
    exact honlyzero x hx.1 (visibleConnectorFinalSmoothing_sublevel_frontier_zero hV hBV.continuousOn x hx)
  have hGinSide : V ∩ interior P ⊆ GinU := by
    intro x hx
    have hn : x ∈ P := interior_subset hx.2
    have hn : B x < 0 := hn
    exact visibleConnectorFinalSmoothingCarrier_nonpositive_domain hx.1 hn.le
  obtain ⟨H, hH, hNeg, hOld, _, _, hClose⟩ := exists_relative_saddle_smoothing_on_sides
    hgamma hp hreg hEmbed hV hN hGinOpen hRawOpen hSeamV hSN hSG hSR
    hBoundary hGinSide (fun _ hx => hx.1.1) hr
    (fun s t ht _ _ => (hclassify s t ht.le).2)
    hGin hraw hValue hGradient hGinNeg hrawNeg hepsilon
  have hKN : Disjoint K (closure N) := Set.disjoint_left.mpr (by
    intro x hk hn
    exact (hClosure hn).2 (Or.inl hk))
  have hTN : Disjoint T (closure N) := Set.disjoint_left.mpr (by
    intro x ht hn
    exact (hClosure hn).2 (Or.inr ht))
  have hKG : K ⊆ GinU := fun x hx =>
    visibleConnectorFinalSmoothingCarrier_nonpositive_domain (hKV hx) (hnegative x hx).le
  exact ⟨N, H, hV, visibleConnectorFinalSmoothingCarrier_subset_target hRawTarget,
    hN, hSN, hClosure, hH, hNeg, (fun x hx => hNeg x (hBand hx)),
    visibleConnectorFinalSmoothing_incoming_open hV hGinOpen hBV.continuousOn hKV hKG hKN hnegative hOld,
    visibleConnectorFinalSmoothing_terminal_open hV hRawOpen hBV.continuousOn hTV
      (fun _ hx => (hTV hx).1) hTN hpositive hOld, hOld, hClose⟩

end
end TightVer401



