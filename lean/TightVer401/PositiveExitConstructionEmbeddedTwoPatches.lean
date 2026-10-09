import TightVer401.PositiveExitConstructionTwoPatches
import TightVer401.PositiveExitConstructionEmbeddingPatch

/-! Two exits of the SAME original potential, with sequential amplitude selection.
The first uses G as its actual gradient baseline; the second uses G plus the
first change. Compact disjoint strips preserve both original Fermi constructions.
The actual combined gradient is embedded and has its actual smooth inverse on
its entire image. No exit, inverse, or perturbed embedding package is an input. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Select both complete leaves from one protected core, choose each exit below
the embedding threshold of its actual current baseline, and construct the
inverse of the SAME final gradient. Original Fermi tensors and returns are
preserved by the derived disjointness of the two compact change strips. -/
theorem positiveExit_exists_two_actual_embedded_cartesian_patches {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hδ : 0 < δ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hNi : Function.Injective (d.bandGaussMap (b := w)))
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ t, ambientCross (d.T t) (d.E t) = d.n t)
    (hτ : ∀ t, d.τ t < 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (G : Coord → ℝ) (hG : ContDiffOn ℝ ∞ G e.target)
    (hrec : ∀ p, planarSupportMap G (e p) = d.bandMap p)
    (hdet : ∀ y ∈ e.target, (planarHessian G y).det < 0)
    (hemb : Topology.IsEmbedding (fun y : e.target => planarGradient G y.val))
    (C : Set Coord) (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    {η ξ σin σout : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (hσin : σin ≠ 0) (hσout : σout ≠ 0) :
    ∃ vin vout : Ioo (0 : ℝ) δ, (vin : ℝ) < (vout : ℝ) ∧
    ∃ S1 : ℝ ≃ₜ ℝ, ∃ P1 : ℝ, ∃ hP1 : 0 < P1, ∃ ρMax1 : ℝ,
    ∃ hp1 : Function.Periodic (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) P1,
      letI : Fact (0 < P1) := ⟨hP1⟩
      ∃ D1 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (η/2) ξ σin ρMax1,
      ∃ B1 : PositiveExitActualCartesianPatch G e.target
        (C ∪ range (e ∘ positiveExitLeaf d hb hinside vout))
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (η/2) ξ σin ρMax1 D1,
      let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
      ∃ S2 : ℝ ≃ₜ ℝ, ∃ P2 : ℝ, ∃ hP2 : 0 < P2, ∃ ρMax2 : ℝ,
      ∃ hp2 : Function.Periodic (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) P2,
      letI : Fact (0 < P2) := ⟨hP2⟩
      ∃ D2 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (η/2) ξ σout ρMax2,
      ∃ B2 : PositiveExitActualCartesianPatch G e.target (C ∪ A1)
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (η/2) ξ σout ρMax2 D2,
      let A2 := positiveExitFermiPatchStrip D2.fermi_chart D2.rho_lt_tube
      let Ge := fun z => G z + B1.change z + B2.change z
      Disjoint A1 A2 ∧
      ContDiffOn ℝ ∞ Ge e.target ∧
      ContDiff ℝ ∞ (fun z => B1.change z + B2.change z) ∧
      HasCompactSupport (fun z => B1.change z + B2.change z) ∧
      (∀ z, fermiCoordinateC2Size (fun q => B1.change q + B2.change q) z < η) ∧
      IsOpen (A1 ∪ A2)ᶜ ∧ C ⊆ (A1 ∪ A2)ᶜ ∧ EqOn Ge G (A1 ∪ A2)ᶜ ∧
      (∀ z ∈ C, Ge =ᶠ[𝓝 z] G) ∧
      IsInfinitesimalBendingOn (planarSupportMap Ge) (Y ∘ e.symm) e.target ∧
      (∀ y ∈ e.target, (planarHessian Ge y).det < 0) ∧
      Nonempty (PositiveExitPairedFermiPreserved D1 B1 Ge) ∧
      Nonempty (PositiveExitPairedFermiPreserved D2 B2 Ge) ∧
      Topology.IsEmbedding (fun y : e.target => planarGradient Ge y.val) ∧
      ∃ h : OpenPartialHomeomorph e.target Coord,
        h.source = univ ∧
        h.target = range (fun y : e.target => planarGradient Ge y.val) ∧
        (h : e.target → Coord) = (fun y : e.target => planarGradient Ge y.val) ∧
        ContDiffOn ℝ ∞ (fun q => (h.symm q).val) h.target := by
  obtain ⟨vin,vout,horder,_hlabels,hin,hout,hboth,_hsin,_hsout,_hsboth⟩ :=
    positiveExit_exists_two_protected_complete_leaves d hb e hinside heS heF heI hδ hC hne hprotect
  let Lout : Set Coord := range (e ∘ positiveExitLeaf d hb hinside vout)
  have hLout : IsCompact Lout := isCompact_range (heD.continuous.comp
    (positiveExitLeaf_contMDiff d hb hinside vout).continuous)
  have hraw (v : Ioo (0 : ℝ) δ) (t : ℝ) :
      gnomonicInverse (positiveExitRawLeaf d hb hinside v t) =
        e (positiveExitLeaf d hb hinside v (periodProjection T t)) :=
    positiveExitGaussLeaf_cartesian_source d hb e hinside heF v (periodProjection T t)
  have havoid1 (t : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside vin t) ∉ C ∪ Lout := by
    rw [hraw]
    intro hmem
    rcases hmem with hc | hl
    · exact disjoint_left.mp hin (mem_range_self (periodProjection T t)) hc
    · exact disjoint_left.mp hboth (mem_range_self (periodProjection T t)) hl
  have hsupport1 : e '' tsupport Y ⊆ C ∪ Lout := fun _ hz => Or.inl (hsupport hz)
  obtain ⟨S1,P1,hP1,ρMax1,_hρ1,hp1,D1,B1,_hsmall1,hEmbedding1,_hcutoff1,_hbend1,_hS1,_hLength1⟩ :=
    positiveExit_selected_leaf_actual_embedded_cartesian_patch d hb hinside vin hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ Lout) (hC.union hLout) havoid1
      Y hbend hsupport1 G hG hemb (fun y hy => (hdet y hy).ne)
      (half_pos hη) hξ hσin hξ
  letI : Fact (0 < P1) := ⟨hP1⟩
  let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
  have hA1 : IsCompact A1 := positiveExitFermiPatchStrip_compact D1.fermi_chart
    D1.rho_lt_tube D1.fermi_chart_smooth
  have havoid2 (t : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside vout t) ∉ C ∪ A1 := by
    rw [hraw]
    intro hmem
    rcases hmem with hc | ha
    · exact disjoint_left.mp hout (mem_range_self (periodProjection T t)) hc
    · exact disjoint_left.mp B1.strip_disjoint ha
        (Or.inr (mem_range_self (periodProjection T t)))
  have hsupport2 : e '' tsupport Y ⊆ C ∪ A1 := fun _ hz => Or.inl (hsupport hz)
  let H1 : Coord → ℝ := fun z => G z + B1.change z
  have hH1 : ContDiffOn ℝ ∞ H1 e.target := hG.add B1.change_smooth.contDiffOn
  have hdetH1 : ∀ y ∈ e.target, (planarHessian H1 y).det ≠ 0 :=
    fun y hy => (B1.whole_saddle y hy).ne
  obtain ⟨S2,P2,hP2,ρMax2,_hρ2,hp2,D2,B2,_hsmall2,hEmbedding2,_hcutoff2,_hbend2,_hS2,_hLength2⟩ :=
    positiveExit_selected_leaf_actual_embedded_cartesian_patch d hb hinside vout hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ A1) (hC.union hA1) havoid2
      Y hbend hsupport2 H1 hH1 hEmbedding1 hdetH1 (half_pos hη) hξ hσout hξ
  letI : Fact (0 < P2) := ⟨hP2⟩
  let A2 := positiveExitFermiPatchStrip D2.fermi_chart D2.rho_lt_tube
  let Ge := fun z => G z + B1.change z + B2.change z
  have hA2 : IsCompact A2 := positiveExitFermiPatchStrip_compact D2.fermi_chart
    D2.rho_lt_tube D2.fermi_chart_smooth
  have hdis : Disjoint A1 A2 := by
    apply disjoint_left.mpr
    intro z hz1 hz2
    exact disjoint_left.mp B2.strip_disjoint hz2 (Or.inr hz1)
  have hGe : ContDiffOn ℝ ∞ Ge e.target :=
    (hG.add B1.change_smooth.contDiffOn).add B2.change_smooth.contDiffOn
  have hprotected : C ⊆ (A1 ∪ A2)ᶜ := by
    intro z hz hmem
    rcases hmem with hz1 | hz2
    · exact disjoint_left.mp B1.strip_disjoint hz1 (Or.inl hz)
    · exact disjoint_left.mp B2.strip_disjoint hz2 (Or.inl hz)
  have hprotectedOpen : IsOpen (A1 ∪ A2)ᶜ := (hA1.union hA2).isClosed.isOpen_compl
  have hprotectedEq : EqOn Ge G (A1 ∪ A2)ᶜ := by
    intro z hz
    have hz1 : z ∉ A1 := fun h => hz (Or.inl h)
    have hz2 : z ∉ A2 := fun h => hz (Or.inr h)
    have h1 := (positiveExit_pair_change_zero B1 hz1).eq_of_nhds
    have h2 := (positiveExit_pair_change_zero B2 hz2).eq_of_nhds
    change G z + B1.change z + B2.change z = G z
    rw [h1,h2,add_zero,add_zero]
  have hprotectedGerm (z : Coord) (hz : z ∈ C) : Ge =ᶠ[𝓝 z] G :=
    hprotectedEq.eventuallyEq_of_mem (hprotectedOpen.mem_nhds (hprotected hz))
  have hgerm1 (z : Coord) (hz : z ∈ A1) : Ge =ᶠ[𝓝 z] (fun q => G q + B1.change q) := by
    have hz2 : z ∉ A2 := fun h => disjoint_left.mp hdis hz h
    filter_upwards [positiveExit_pair_change_zero B2 hz2] with q hq
    change G q + B1.change q + B2.change q = G q + B1.change q
    rw [hq,add_zero]
  have hgerm2 (z : Coord) (hz : z ∉ A1) : Ge =ᶠ[𝓝 z] (fun q => G q + B2.change q) := by
    filter_upwards [positiveExit_pair_change_zero B1 hz] with q hq
    change G q + B1.change q + B2.change q = G q + B2.change q
    rw [hq,add_zero]
  have hwhole (z : Coord) (hz : z ∈ e.target) : (planarHessian Ge z).det < 0 := by
    by_cases hz1 : z ∈ A1
    · have he := hgerm1 z hz1
      have hess : planarHessian Ge z = planarHessian (fun q => G q + B1.change q) z := by
        ext i j
        exact (fermiCoordinatePartial_eventuallyEq (fermiCoordinatePartial_eventuallyEq he j) i).eq_of_nhds
      rw [hess]
      exact B1.whole_saddle z hz
    · have he := hgerm2 z hz1
      have hess : planarHessian Ge z = planarHessian (fun q => G q + B2.change q) z := by
        ext i j
        exact (fermiCoordinatePartial_eventuallyEq (fermiCoordinatePartial_eventuallyEq he j) i).eq_of_nhds
      rw [hess]
      exact B2.whole_saddle z hz
  have hBending : IsInfinitesimalBendingOn (planarSupportMap Ge) (Y ∘ e.symm) e.target := by
    refine ⟨hbend.1, ?_⟩
    intro z hz i j
    by_cases hs : e.symm z ∈ tsupport Y
    · have hzc : z ∈ C := hsupport ⟨e.symm z,hs,e.right_inv hz⟩
      have he := hprotectedGerm z hzc
      have hm : planarSupportMap Ge =ᶠ[𝓝 z] planarSupportMap G := by
        filter_upwards [he,he.eventuallyEq_nhds] with q hq hg
        unfold planarSupportMap
        simp only [coordPartial,hg.fderiv_eq (𝕜 := ℝ),hq]
      have hd := hm.fderiv_eq (𝕜 := ℝ)
      simpa only [strain,coordPartial,hd] using hbend.2 z hz i j
    · have hi : ContinuousAt e.symm z :=
        (heI.continuousOn z hz).continuousAt (e.open_target.mem_nhds hz)
      have he : (Y ∘ e.symm) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hi.preimage_mem_nhds ((isClosed_tsupport Y).isOpen_compl.mem_nhds hs)] with q hq
        change Y (e.symm q) = 0
        by_contra hn
        exact hq (subset_tsupport Y hn)
      have hd : fderiv ℝ (Y ∘ e.symm) z = 0 :=
        (he.fderiv_eq (𝕜 := ℝ)).trans (hasFDerivAt_const (c := (0 : Ambient)) z).fderiv
      simp only [strain,coordPartial,hd,ContinuousLinearMap.zero_apply,
        inner_zero_left,inner_zero_right,add_zero]
  have hC2 (z : Coord) : fermiCoordinateC2Size (fun q => B1.change q + B2.change q) z < η :=
    (positiveExit_pair_C2_triangle B1.change_smooth B2.change_smooth z).trans_lt
      (by linarith [B1.change_C2 z,B2.change_C2 z])
  have hpres1 := positiveExit_pair_preserves_actual_fermi D1 B1 hGe hgerm1
  have hpres2 := positiveExit_pair_preserves_actual_fermi D2 B2 hGe
    (fun z hz => hgerm2 z (fun hz1 => disjoint_left.mp hdis hz1 hz))
  have hEmbedded : Topology.IsEmbedding (fun y : e.target => planarGradient Ge y.val) :=
    hEmbedding2
  have hneU : e.target.Nonempty := by
    refine ⟨e (positiveExitLeaf d hb hinside vin (periodProjection T 0)), ?_⟩
    apply e.mapsTo
    rw [heS]
    exact mem_univ _
  have hactual : (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) = Ge := by
    funext z
    change G z + (1 : ℝ) * (B1.change z + B2.change z) =
      G z + B1.change z + B2.change z
    ring
  have hdetActual : ∀ y ∈ e.target,
      (planarHessian (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) y).det ≠ 0 := by
    rw [hactual]
    exact fun y hy => (hwhole y hy).ne
  have hEmbeddedActual : Topology.IsEmbedding (fun y : e.target =>
      planarGradient (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) y.val) := by
    rw [hactual]
    exact hEmbedded
  obtain ⟨h,hhS,hhT,hhF,hhI⟩ := positiveExit_actual_gradient_global_inverse
    e.open_target hneU hG (B1.change_smooth.add B2.change_smooth) 1 hdetActual hEmbeddedActual
  rw [hactual] at hhT hhF
  exact ⟨vin,vout,horder,S1,P1,hP1,ρMax1,hp1,D1,B1,
    S2,P2,hP2,ρMax2,hp2,D2,B2,hdis,hGe,B1.change_smooth.add B2.change_smooth,
    B1.change_compact.add B2.change_compact,hC2,
    hprotectedOpen,hprotected,hprotectedEq,hprotectedGerm,hBending,hwhole,hpres1,hpres2,hEmbedded,h,hhS,hhT,hhF,hhI⟩


end
end TightVer401

