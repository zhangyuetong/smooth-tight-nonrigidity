import TightVer401.VisibleConnectorIncomingGinSmoothingApplication
import TightVer401.VisibleConnectorIncomingGinGlobalSideDerivatives

/-! Literal GlobalHeight application.  E is the SAME Cartesian source inverse;
the phase and height belong to the SAME displaced native inverse retained by
the caller.  This leaf constructs neither inverse.  It produces the final
scalar and full open equality neighborhoods.  Its gradient inverse must later
be constructed for this final scalar by the supplied-potential degree adapter. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingApplication_periodic_range_compact {L : ℝ} (hL : 0 < L)
    {f : ℝ → Coord} (hf : Continuous f) (hp : Periodic f L) : IsCompact (range f) := by
  have heq : f '' Icc (0 : ℝ) L = range f := by
    apply Subset.antisymm (image_subset_range _ _)
    rintro x ⟨s, rfl⟩
    refine ⟨toIcoMod hL 0 s, Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s), ?_⟩
    exact (seam_periodic_eq_representative hL hp s).symm
  rw [← heq]
  exact isCompact_Icc.image hf

private theorem incomingApplication_complex_normal (z : ℂ) :
    seamComplexCoord (Complex.I * z) = visibleConnectorJ (seamComplexCoord z) := by
  ext i
  fin_cases i <;>
    simp [seamComplexCoord_apply, visibleConnectorJ, Complex.mul_re, Complex.mul_im]

/-- Actual scalar smoothing on the full fixed carrier.  The ordinary band
coverage is supplied by the preceding actual Carrier application.  All height
signs, zero-seam boundary and canonical normal side are proved here from the
literal SAME source inverse and rebased ruling.  No exterior germ is an input. -/
theorem visibleConnectorIncomingGin_actual_global_height_smoothing
    {L : ℝ} [hL : Fact (0 < L)] {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hcL : Periodic (pc ∘ a) L)
    (hEmbed : Injective hcL.lift)
    (hbneg : ∀ s, b s < 0) (hdpos : ∀ s, 0 < d s) (htpos : ∀ s, 0 < b s + d s)
    (hphase : ∀ s, 0 < deriv a s) (hA : ∀ s, 0 < visibleConnectorA pc wc (a s))
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
    (hBandV : ∀ s u, 0 ≤ u → u ≤ 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) ![s, u] ∈
          visibleConnectorIncomingGinCarrier Vraw GinU (visibleConnectorIncomingGinGlobalHeight L b d E))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let pOriginal := visibleConnectorRebasedSource pc wc a b
    let Tterminal := fun s => pOriginal s + visibleConnectorRebasedRuling wc a d s
    let B := visibleConnectorIncomingGinGlobalHeight L b d E
    let V := visibleConnectorIncomingGinCarrier Vraw GinU B
    ∃ H : Coord → ℝ, ∃ Oin Oterminal : Set Coord,
      IsOpen V ∧ ContDiffOn ℝ ∞ H V ∧ (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      IsOpen Oin ∧ range pOriginal ⊆ Oin ∧ Oin ⊆ V ∩ GinU ∧ EqOn H Gin Oin ∧
      IsOpen Oterminal ∧ range Tterminal ⊆ Oterminal ∧ Oterminal ⊆ V ∩ Vraw ∧ EqOn H raw Oterminal ∧
      (∀ x ∈ V, |H x - relativeSaddlePiecewise {y | B y < 0} Gin raw x| < epsilon ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise {y | B y < 0} Gin raw) x‖ < epsilon) := by
  let c := pc ∘ a
  let gamma := fun s => seamComplexCoord.symm (c s)
  let pOriginal := visibleConnectorRebasedSource pc wc a b
  let wNew := visibleConnectorRebasedRuling wc a d
  let Tterminal := fun s => pOriginal s + wNew s
  let B := visibleConnectorIncomingGinGlobalHeight L b d E
  let V := visibleConnectorIncomingGinCarrier Vraw GinU B
  have hc : ContDiff ℝ ∞ c := hp.comp ha
  have hgamma : ContDiff ℝ ∞ gamma := seamComplexCoord.symm.contDiff.comp hc
  have hgammaL : Periodic gamma L := by
    intro s
    change seamComplexCoord.symm (c (s + L)) = seamComplexCoord.symm (c s)
    rw [hcL s]
  have hLift (q : AddCircle L) : hgammaL.lift q = seamComplexCoord.symm (hcL.lift q) := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [Function.Periodic.lift_coe]
    rfl
  have hEmbedGamma : Injective hgammaL.lift := by
    intro q r he
    apply hEmbed
    apply seamComplexCoord.symm.injective
    rw [← hLift q, ← hLift r]
    exact he
  have hderivGamma (s : ℝ) : deriv gamma s = seamComplexCoord.symm (deriv c s) :=
    (seamComplexCoord.symm.hasFDerivAt.comp_hasDerivAt s
      (hc.differentiable (by simp) s).hasDerivAt).deriv
  have hregular (s : ℝ) : deriv gamma s ≠ 0 := by
    intro hz
    have hEq : seamComplexCoord.symm (deriv c s) = seamComplexCoord.symm (0 : Coord) := by
      rw [← hderivGamma s, hz]
      simp
    have hc0 : deriv c s = 0 := seamComplexCoord.symm.injective hEq
    have hdet := visibleConnectorIncomingGinGlobalHeight_seam_determinant hp hw ha hphase hA s
    change visibleConnectorDet (deriv c s) (wc (a s)) < 0 at hdet
    rw [hc0] at hdet
    have hbad : (0 : ℝ) < 0 := by
      simpa only [visibleConnectorDet, Pi.zero_apply, zero_mul, sub_self] using hdet
    exact lt_irrefl (0 : ℝ) hbad
  have hBE : ContDiffOn ℝ ∞ B E.target :=
    visibleConnectorIncomingGinGlobalHeight_contDiffOn hb hd hbL hdL E hsource hi
  have hBraw : ContDiffOn ℝ ∞ B Vraw := hBE.mono hVrawE
  have hSeamFacts (s : ℝ) := visibleConnectorIncomingGinGlobalHeight_rebased_band hL.out
    hpL hwL hbL hdL hbneg hdpos htpos E hE hclosed s
  have hSeamV (s : ℝ) : seamComplexCoord (gamma s) ∈ V := by
    have hu0 : 0 < -b s / d s := div_pos (neg_pos.mpr (hbneg s)) (hdpos s)
    have hu1 : -b s / d s < 1 := (div_lt_one (hdpos s)).mpr (by linarith [htpos s])
    have hz : b s + (-b s / d s) * d s = 0 := by field_simp [(hdpos s).ne'] <;> ring
    have hm := hBandV s (-b s / d s) hu0.le hu1.le
    rw [visibleConnector_rebase_source, hz] at hm
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero] using hm
  have hzero (s : ℝ) : B (seamComplexCoord (gamma s)) = 0 := by
    simpa only [B, gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      using (hSeamFacts s).2.2.2.2.2.1
  have honlyzero (x : Coord) (hx : x ∈ V) (hz : B x = 0) :
      x ∈ range (fun s => seamComplexCoord (gamma s)) := by
    obtain ⟨s, hs⟩ := visibleConnectorIncomingGinGlobalHeight_zero_range hdpos E hE (hVrawE hx.1) hz
    refine ⟨s, ?_⟩
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hs
  have hnormal (s : ℝ) : fderiv ℝ B (seamComplexCoord (gamma s))
      (seamComplexCoord (Complex.I * deriv gamma s)) < 0 := by
    rw [incomingApplication_complex_normal, hderivGamma]
    simp only [gamma, ContinuousLinearEquiv.apply_symm_apply]
    exact visibleConnectorIncomingGinGlobalHeight_normal_neg hL.out hp hw ha
      hpL hwL hbL hdL hbneg hdpos htpos hphase hA E hE hclosed hBE s
  have hpSmooth : ContDiff ℝ ∞ pOriginal := (hp.comp ha).add (hb.smul (hw.comp ha))
  have hwSmooth : ContDiff ℝ ∞ wNew := hd.smul (hw.comp ha)
  have htSmooth : ContDiff ℝ ∞ Tterminal := hpSmooth.add hwSmooth
  have htPeriod : Periodic Tterminal L := by
    intro s
    change pOriginal (s + L) + wNew (s + L) = pOriginal s + wNew s
    rw [hpL s, hwL s]
  have hpCompact := incomingApplication_periodic_range_compact hL.out hpSmooth.continuous hpL
  have htCompact := incomingApplication_periodic_range_compact hL.out htSmooth.continuous htPeriod
  have hpV (s : ℝ) : pOriginal s ∈ V := by
    simpa only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_smul, add_zero] using hBandV s 0 (by norm_num) (by norm_num)
  have htV (s : ℝ) : Tterminal s ∈ V := by
    simpa only [Tterminal, pOriginal, wNew, visibleConnectorSource,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] using hBandV s 1 (by norm_num) (by norm_num)
  have hpNegative (s : ℝ) : B (pOriginal s) < 0 := by
    rw [(hSeamFacts s).2.1]
    exact hbneg s
  have htPositive (s : ℝ) : 0 < B (Tterminal s) := by
    have hval := (visibleConnectorIncomingGinGlobalHeight_closed_band hL.out hpL hwL hbL hdL
      E hE hclosed s 1 (by norm_num) (by norm_num)).2
    simp only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_smul, one_mul] at hval
    rw [hval]
    exact htpos s
  have hValueGamma (s : ℝ) : Gin (seamComplexCoord (gamma s)) = raw (seamComplexCoord (gamma s)) := by
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hValue s
  have hGradientGamma (s : ℝ) : planarGradient Gin (seamComplexCoord (gamma s)) =
      planarGradient raw (seamComplexCoord (gamma s)) := by
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hGradient s
  obtain ⟨N, H, Oin, Oterminal, _, _, _, hH, hHneg,
    hOin, hpOin, hOinDomain, hEqGin, hOterminal, htOterminal, hOterminalDomain, hEqRaw, _, hClose⟩ :=
    visibleConnectorIncomingGin_exists_smoothed_full_carrier hgamma hgammaL hregular hEmbedGamma
      hVraw hGinU hBraw hGin hraw hGinNeg hrawNeg hSeamV hzero honlyzero hnormal
      hValueGamma hGradientGamma hpCompact htCompact hpV htV hpNegative htPositive hepsilon
  exact ⟨H, Oin, Oterminal,
    visibleConnectorIncomingGinCarrier_isOpen hVraw hGinU hBraw.continuousOn,
    hH, hHneg, hOin, hpOin, hOinDomain, hEqGin, hOterminal, htOterminal, hOterminalDomain, hEqRaw, hClose⟩

end
end TightVer401
