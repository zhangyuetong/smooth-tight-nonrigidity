import TightVer401.VisibleConnectorFinalSmoothingConstruction
import TightVer401.VisibleConnectorFinalSmoothingSeamEmbedding
import TightVer401.VisibleConnectorFinalSmoothingHeightCarrier
import TightVer401.VisibleConnectorFinalSmoothingSeamDelta

/-! Actual old-height application on the SAME Cartesian source inverse. The
height, its only-zero seam, normal sign, regular embedded seam, full carrier
coverage and protected boundary sets are constructed from ordinary ruling
facts. The raw support potential is a separate scalar throughout. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem finalSmoothingActual_complex_normal (z : ℂ) :
    seamComplexCoord (Complex.I * z) = visibleConnectorJ (seamComplexCoord z) := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, visibleConnectorJ, Complex.mul_re, Complex.mul_im]

/-- Produce the final scalar from the actual SAME raw source inverse and old
ruling height. No height, only-zero condition, normal derivative, seam
embedding, carrier coverage or compact boundary conclusion is supplied. -/
theorem visibleConnectorFinalSmoothing_exists_scalar_from_cartesian
    {L : ℝ} [hL : Fact (0 < L)] {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hcL : Periodic (pc ∘ a) L)
    (hbneg : ∀ s, b s < 0) (hdpos : ∀ s, 0 < d s) (htpos : ∀ s, 0 < b s + d s)
    (hphase : ∀ s, 0 < deriv a s) (rawGamma : ℝ → Coord)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ 1 →
      0 < visibleConnectorDelta (visibleConnectorRebasedSource pc wc a b)
        rawGamma (visibleConnectorRebasedRuling wc a d) q)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hsource : E.source ⊆ {z | 0 < planarRadius z})
    (hi : ContDiffOn ℝ ∞ E.symm E.target)
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    {Gin raw : Coord → ℝ} {GinU Vraw : Set Coord}
    (hGinU : IsOpen GinU) (hVraw : IsOpen Vraw) (hVrawE : Vraw ⊆ E.target)
    (hGin : ContDiffOn ℝ ∞ Gin GinU) (hraw : ContDiffOn ℝ ∞ raw Vraw)
    (hGinNeg : ∀ x ∈ GinU, (planarHessian Gin x).det < 0)
    (hrawNeg : ∀ x ∈ Vraw, (planarHessian raw x).det < 0)
    (hValue : ∀ s, Gin (pc (a s)) = raw (pc (a s)))
    (hGradient : ∀ s, planarGradient Gin (pc (a s)) = planarGradient raw (pc (a s)))
    (hRawBand : ∀ s u, u ∈ Icc (0 : ℝ) 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ Vraw)
    (hGinStrip : ∀ s t, b s ≤ t → t ≤ 0 →
      visibleConnectorSource pc wc ![a s, t] ∈ GinU)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let B := visibleConnectorFinalSmoothingHeight L b d E
    let V := visibleConnectorFinalSmoothingCarrier Vraw GinU B
    let lower := visibleConnectorRebasedSource pc wc a b
    let terminal := fun s => lower s + visibleConnectorRebasedRuling wc a d s
    ∃ H : Coord → ℝ, ∃ Oin Ot : Set Coord,
      IsOpen V ∧ V ⊆ E.target ∧ ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d,
        (planarHessian H x).det < 0) ∧
      (IsOpen Oin ∧ range lower ⊆ Oin ∧ Oin ⊆ V ∩ GinU ∧ EqOn H Gin Oin) ∧
      (IsOpen Ot ∧ range terminal ⊆ Ot ∧ Ot ⊆ V ∩ Vraw ∧ EqOn H raw Ot) ∧
      ∀ x ∈ V, |H x - relativeSaddlePiecewise {y | B y < 0} Gin raw x| < epsilon ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise {y | B y < 0} Gin raw) x‖ < epsilon := by
  have hA := visibleConnectorFinalSmoothing_old_coefficient_of_rebased_Delta
    hp hw ha hb hd hphase hdpos hbneg htpos hDelta
  let B := visibleConnectorFinalSmoothingHeight L b d E
  let V := visibleConnectorFinalSmoothingCarrier Vraw GinU B
  let lower := visibleConnectorRebasedSource pc wc a b
  let terminal := fun s => lower s + visibleConnectorRebasedRuling wc a d s
  let gamma := fun s => seamComplexCoord.symm ((pc ∘ a) s)
  have hB : ContDiffOn ℝ ∞ B E.target :=
    visibleConnectorFinalSmoothingHeight_contDiffOn hb hd hbL hdL E hsource hi
  have hBand := visibleConnectorFinalSmoothingHeightCarrier_closed_band hL.out
    hpL hwL hbL hdL hdpos E hE hclosed hRawBand hGinStrip
  have hSeam (s : ℝ) : pc (a s) ∈ V :=
    visibleConnectorFinalSmoothingHeightCarrier_seam hL.out
      hpL hwL hbL hdL hdpos E hE hclosed hRawBand hGinStrip hbneg htpos s
  have hFacts (s : ℝ) := visibleConnectorFinalSmoothingHeight_rebased_band hL.out
    hpL hwL hbL hdL hbneg hdpos htpos E hE hclosed s
  obtain ⟨hgamma, hreg, hperiod, hEmbed⟩ := visibleConnectorFinalSmoothing_seam_geometry
    hp hw ha hpL hwL hcL hbneg hdpos htpos hphase hA E hE hclosed
  have hSeamRaw (s : ℝ) : seamComplexCoord (gamma s) ∈ Vraw := by
    simpa only [gamma, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using (hSeam s).1
  have hSeamGin (s : ℝ) : seamComplexCoord (gamma s) ∈ GinU := by
    have hg := hGinStrip s 0 (hbneg s).le le_rfl
    simpa [gamma, visibleConnectorSource] using hg
  have hzero (s : ℝ) : B (seamComplexCoord (gamma s)) = 0 := by
    simpa only [B, gamma, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      using (hFacts s).2.2.2.2.2.1
  have hOnlyZero (x : Coord) (hx : x ∈ V) (hz : B x = 0) :
      x ∈ range (fun s => seamComplexCoord (gamma s)) := by
    have hzRange := visibleConnectorFinalSmoothingHeight_zero_range E hE (hVrawE hx.1) hz
    simpa only [gamma, ContinuousLinearEquiv.apply_symm_apply] using hzRange
  have hnormal (s : ℝ) : fderiv ℝ B (seamComplexCoord (gamma s))
      (seamComplexCoord (Complex.I * deriv gamma s)) < 0 := by
    have hDerivative : deriv gamma s = seamComplexCoord.symm (deriv (pc ∘ a) s) :=
      (seamComplexCoord.symm.hasFDerivAt.comp_hasDerivAt s
        ((hp.comp ha).differentiable (by simp) s).hasDerivAt).deriv
    rw [finalSmoothingActual_complex_normal, hDerivative]
    simp only [gamma, ContinuousLinearEquiv.apply_symm_apply]
    exact visibleConnectorFinalSmoothingHeight_normal_neg hL.out hp hw ha
      hpL hwL hbL hdL hbneg hdpos htpos hphase hA E hE hclosed hB s
  obtain ⟨hLowerCompact, hTerminalCompact⟩ :=
    visibleConnectorFinalSmoothingHeightCarrier_boundary_compact hL.out hp hw ha hb hd hpL hwL
  have hLowerV : range lower ⊆ V := by
    rintro x ⟨s, rfl⟩
    apply hBand
    refine ⟨s, 0, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [lower, visibleConnectorSource]
  have hTerminalV : range terminal ⊆ V := by
    rintro x ⟨s, rfl⟩
    apply hBand
    refine ⟨s, 1, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [terminal, lower, visibleConnectorSource]
  have hNegative : ∀ x ∈ range lower, B x < 0 := by
    rintro x ⟨s, rfl⟩
    change visibleConnectorFinalSmoothingHeight L b d E (visibleConnectorRebasedSource pc wc a b s) < 0
    rw [(hFacts s).2.1]
    exact hbneg s
  have hPositive : ∀ x ∈ range terminal, 0 < B x := by
    rintro x ⟨s, rfl⟩
    have hf := (visibleConnectorFinalSmoothingHeight_closed_band hL.out hpL hwL hbL hdL
      E hE hclosed s 1 (by norm_num) (by norm_num)).2
    simp only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, one_mul] at hf
    change 0 < visibleConnectorFinalSmoothingHeight L b d E _
    rw [hf]
    exact htpos s
  have hv (s : ℝ) : Gin (seamComplexCoord (gamma s)) = raw (seamComplexCoord (gamma s)) := by
    simpa only [gamma, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hValue s
  have hg (s : ℝ) : planarGradient Gin (seamComplexCoord (gamma s)) =
      planarGradient raw (seamComplexCoord (gamma s)) := by
    simpa only [gamma, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hGradient s
  obtain ⟨N, H, hV, hVT, _, _, _, hH, hNeg, hClosedNeg, hIn, hOut, _, hClose⟩ :=
    visibleConnectorFinalSmoothing_exists_full_scalar hgamma hperiod hreg hEmbed E hVrawE
      hVraw hGinU (hB.mono hVrawE) hGin hraw hGinNeg hrawNeg
      hSeamRaw hSeamGin hzero hOnlyZero hnormal hv hg hLowerCompact hTerminalCompact
      hLowerV hTerminalV hNegative hPositive hBand hepsilon
  exact ⟨H, visibleConnectorFinalSmoothingIncomingOpen V GinU N B,
    visibleConnectorFinalSmoothingTerminalOpen V Vraw N B,
    hV, hVT, hH, hNeg, hClosedNeg, hIn, hOut, hClose⟩

end
end TightVer401
