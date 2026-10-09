import TightVer401.VisibleConnectorDisplacedSeamOpenImage

/-! Patch the ACTUAL native original-point inverse to a real close phase.
The fixed period chart is applied to the phase DIFFERENCE from the original
parameter. This retains the original p and never extends w beyond Omega. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def visibleConnectorDisplacedPhaseDifference {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) (z : ℝ × ℝ) : AddCircle L :=
  (visibleConnectorDisplacedNativeSolution e p z).1 - periodProjection L z.2

def visibleConnectorDisplacedRealPhase {L : ℝ} [Fact (0 < L)]
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  z.2 + (periodChart L).symm (visibleConnectorDisplacedPhaseDifference e p z)

def visibleConnectorDisplacedRealPhaseDomain {L : ℝ} [Fact (0 < L)]
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) : Set (ℝ × ℝ) :=
  visibleConnectorDisplacedNativeSolutionDomain e p ∩
    visibleConnectorDisplacedPhaseDifference e p ⁻¹' (periodChart L).target

private theorem displaced_periodChart_zero (L : ℝ) [Fact (0 < L)] :
    (periodChart L).symm 0 = 0 := by
  have h := (periodChart L).left_inv (periodChart_zero_source L)
  change (periodChart L).symm (periodProjection L 0) = 0 at h
  simpa only [map_zero] using h

/-- The close phase represents the SAME actual native inverse, throughout its
actual phase domain. -/
theorem visibleConnectorDisplacedRealPhase_projection {L : ℝ} [Fact (0 < L)]
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) {z : ℝ × ℝ}
    (hz : z ∈ visibleConnectorDisplacedRealPhaseDomain e p) :
    periodProjection L (visibleConnectorDisplacedRealPhase e p z) =
      (visibleConnectorDisplacedNativeSolution e p z).1 := by
  have h := (periodChart L).right_inv hz.2
  change periodProjection L ((periodChart L).symm
    (visibleConnectorDisplacedPhaseDifference e p z)) =
      visibleConnectorDisplacedPhaseDifference e p z at h
  change periodProjection L (z.2 + (periodChart L).symm
    (visibleConnectorDisplacedPhaseDifference e p z)) = _
  rw [map_add, h]
  simp only [visibleConnectorDisplacedPhaseDifference]
  abel

set_option backward.isDefEq.respectTransparency true in
/-- Construct a real phase on ONE uniform rho strip, with actual full-period
shift, smooth real height and the literal original-point ruling equation.
The central displacement derivatives are proved from the constructed inverse;
no sign or real phase package is supplied as input. -/
theorem visibleConnectorDisplaced_exists_smooth_real_phase {L : ℝ} [Fact (0 < L)]
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hip : Injective hpL.lift) (hOmega : IsOpen Omega) (hw : ContDiffOn ℝ ∞ w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega) (hwzero : ∀ s, w (0, s) = w0 s)
    (hdet : ∀ s, visibleConnectorDet (deriv p s) (w0 s) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord),
      (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
        visibleConnectorDisplacedNativePsi hpL hw0L hwL ∧
      (∀ y ∈ e.target, ∃ s : ℝ,
        ∃ a : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
        ContDiffOn ℝ ∞ a.symm a.target ∧
        ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧
          B ⊆ e.target ∧ B ⊆ a.target ∧
          (∀ v ∈ B, e.symm v = visibleConnectorDisplacedNativeChart L s (a.symm v))) ∧
      IsOpen (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e p)
        (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      ContDiffOn ℝ ∞ (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
        (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      (∀ z ∈ visibleConnectorDisplacedRealPhaseDomain e p,
        visibleConnectorDisplacedPhi p w0 w z.1
          (![visibleConnectorDisplacedRealPhase e p z,
            (visibleConnectorDisplacedNativeSolution e p z).2] : Coord) = p z.2) ∧
      (∀ rho s, visibleConnectorDisplacedRealPhase e p (rho, s + L) =
        visibleConnectorDisplacedRealPhase e p (rho, s) + L) ∧
      (∀ rho, Periodic (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L) ∧
      (∀ s, visibleConnectorDisplacedRealPhase e p (0, s) = s) ∧
      (∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0) ∧
      (∀ s, HasDerivAt (fun rho => visibleConnectorDisplacedRealPhase e p (rho, s)) 0 0) ∧
      (∀ s, HasDerivAt (fun t => visibleConnectorDisplacedRealPhase e p (0, t)) 1 s) ∧
      (∀ s, HasDerivAt
        (fun rho => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) (-1) 0) ∧
      ∃ eta > 0, Icc (-eta) eta ×ˢ (univ : Set ℝ) ⊆
        visibleConnectorDisplacedRealPhaseDomain e p := by
  obtain ⟨e, hef, haxisE, hregular, hLocal, hDopen, hQc, hBs, hSolve, hPeriod,
    hBase, hCentral, hBr, _, _, _⟩ :=
    visibleConnectorDisplaced_exists_native_open_image hp hw0 hpL hw0L hwL
      hip hOmega hw haxis hwzero hdet
  let D := visibleConnectorDisplacedRealPhaseDomain e p
  let a := visibleConnectorDisplacedRealPhase e p
  let b := fun z : ℝ × ℝ => (visibleConnectorDisplacedNativeSolution e p z).2
  have hProj : Continuous (periodProjection L) := AddCircle.continuous_mk' L
  have hDiff : ContinuousOn (visibleConnectorDisplacedPhaseDifference e p)
      (visibleConnectorDisplacedNativeSolutionDomain e p) :=
    hQc.fst.sub (hProj.comp continuous_snd).continuousOn
  have hD : IsOpen D := hDiff.isOpen_inter_preimage hDopen (periodChart L).open_target
  have hBaseDiff (s : ℝ) : visibleConnectorDisplacedPhaseDifference e p (0, s) = 0 := by
    simp only [visibleConnectorDisplacedPhaseDifference, hBase s, sub_self]
  have hDaxis (s : ℝ) : (0, s) ∈ D := by
    refine ⟨?_, ?_⟩
    · have hf0 : visibleConnectorDisplacedNativePsi hpL hw0L hwL
          (0, (periodProjection L s, 0)) = (0, p s) := by
        simp only [visibleConnectorDisplacedNativePsi, periodicLift_coe, zero_smul, add_zero]
      have ht := e.map_source (haxisE (periodProjection L s))
      rw [hef, hf0] at ht
      exact ht
    · change visibleConnectorDisplacedPhaseDifference e p (0, s) ∈ (periodChart L).target
      rw [hBaseDiff]
      exact periodChart_zero_target L
  have hA0 (s : ℝ) : a (0, s) = s := by
    simp only [a, visibleConnectorDisplacedRealPhase, hBaseDiff, displaced_periodChart_zero, add_zero]
  have hB0 (s : ℝ) : b (0, s) = 0 := congrArg Prod.snd (hBase s)
  have hA : ContDiffOn ℝ ∞ a D := by
    intro z hz
    let j : ℝ × ℝ → ℝ × Coord := fun x => (x.1, p x.2)
    have hj : ContDiff ℝ ∞ j := contDiff_fst.prodMk (hp.comp contDiff_snd)
    obtain ⟨r, a0, ha0, B, hB, hzB, _, hBa, heq⟩ := hLocal (j z) hz.1
    let Q : ℝ × ℝ → Coord := fun x => (a0.symm (j x)).2
    have hAi : ContDiffAt ℝ ∞ a0.symm (j z) :=
      (ha0 _ (hBa hzB)).contDiffAt (a0.open_target.mem_nhds (hBa hzB))
    have hQ : ContDiffAt ℝ ∞ Q z := (hAi.comp z hj.contDiffAt).snd
    let d : ℝ × ℝ → ℝ := fun x => Q x 0 - x.2
    have hd : ContDiffAt ℝ ∞ d z :=
      ((contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffAt.comp z hQ).sub contDiffAt_snd
    have hNative (x : ℝ × ℝ) (hx : j x ∈ B) :
        (visibleConnectorDisplacedNativeSolution e p x).1 = periodProjection L (Q x 0) := by
      change (e.symm (j x)).2.1 = _
      rw [heq _ hx, visibleConnectorDisplacedNativeChart_apply]
    have hdz : periodProjection L (d z) ∈ (periodChart L).target := by
      have he : visibleConnectorDisplacedPhaseDifference e p z = periodProjection L (d z) := by
        change (visibleConnectorDisplacedNativeSolution e p z).1 - periodProjection L z.2 = _
        rw [hNative z hzB, map_sub]
      rw [← he]
      exact hz.2
    have hCoords : ContDiffAt ℝ ∞ ((periodChart L).symm ∘ periodProjection L) (d z) :=
      ((periodChart_coords_contDiff L) _ hdz).contDiffAt
        (((periodChart L).open_target.preimage hProj).mem_nhds hdz)
    have hlocal : ContDiffAt ℝ ∞
        (fun x => x.2 + (periodChart L).symm (periodProjection L (d x))) z :=
      contDiffAt_snd.add (hCoords.comp z hd)
    have hEq : a =ᶠ[𝓝 z]
        (fun x => x.2 + (periodChart L).symm (periodProjection L (d x))) := by
      filter_upwards [(hB.preimage hj.continuous).mem_nhds hzB] with x hx
      change x.2 + (periodChart L).symm
        ((visibleConnectorDisplacedNativeSolution e p x).1 - periodProjection L x.2) = _
      rw [hNative x hx, map_sub]
    exact (hlocal.congr_of_eventuallyEq hEq).contDiffWithinAt
  have hPhasePeriod (rho s : ℝ) : a (rho, s + L) = a (rho, s) + L := by
    have hProjPeriod : periodProjection L (s + L) = periodProjection L s := by
      change ((s + L : ℝ) : AddCircle L) = (s : AddCircle L)
      exact AddCircle.coe_add_period L s
    change s + L + (periodChart L).symm
      ((visibleConnectorDisplacedNativeSolution e p (rho, s + L)).1 - periodProjection L (s + L)) = _
    have hper : visibleConnectorDisplacedNativeSolution e p (rho, s + L) =
        visibleConnectorDisplacedNativeSolution e p (rho, s) := hPeriod rho s
    rw [hper, hProjPeriod]
    change s + L + (periodChart L).symm
      (visibleConnectorDisplacedPhaseDifference e p (rho, s)) =
        s + (periodChart L).symm (visibleConnectorDisplacedPhaseDifference e p (rho, s)) + L
    ring
  have hHeightPeriod (rho : ℝ) : Periodic (fun s => b (rho, s)) L :=
    fun s => congrArg Prod.snd (hPeriod rho s)
  have hEquation (z : ℝ × ℝ) (hz : z ∈ D) :
      visibleConnectorDisplacedPhi p w0 w z.1 (![a z, b z] : Coord) = p z.2 := by
    have hq := visibleConnectorDisplacedRealPhase_projection e p hz
    have hactual := congrArg Prod.snd (hSolve z hz.1)
    change hpL.lift (visibleConnectorDisplacedNativeSolution e p z).1 +
      z.1 • hw0L.lift (visibleConnectorDisplacedNativeSolution e p z).1 +
      b z • (hwL z.1).lift (visibleConnectorDisplacedNativeSolution e p z).1 = p z.2 at hactual
    rw [← hq, periodicLift_coe, periodicLift_coe, periodicLift_coe] at hactual
    simpa only [visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one] using hactual
  have hAr (s : ℝ) : HasDerivAt (fun rho => a (rho, s)) 0 0 := by
    obtain ⟨B, Q, hB, hsB, _, hQ, hNative, _, hQ0, hQr, _⟩ := hCentral s
    let d : ℝ × ℝ → ℝ := fun z => Q z 0 - z.2
    have hd0 : d (0, s) = 0 := by simp only [d, hQ0, Matrix.cons_val_zero, sub_self]
    have hQAt : ContDiffAt ℝ ∞ Q (0, s) :=
      (hQ _ hsB).contDiffAt (hB.mem_nhds hsB)
    have hdcont : ContinuousAt d (0, s) := by
      have hc : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Q z 0) (0, s) :=
        (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffAt.comp (0, s) hQAt
      exact (hc.sub contDiffAt_snd).continuousAt
    have hdSource : d (0, s) ∈ (periodChart L).source := by
      rw [hd0]
      exact periodChart_zero_source L
    have hsmall : ∀ᶠ z in 𝓝 (0, s), d z ∈ (periodChart L).source :=
      hdcont.eventually ((periodChart L).open_source.mem_nhds hdSource)
    have hEq : a =ᶠ[𝓝 (0, s)] (fun z => Q z 0) := by
      filter_upwards [hB.mem_nhds hsB, hsmall] with z hz hs
      change z.2 + (periodChart L).symm
        ((visibleConnectorDisplacedNativeSolution e p z).1 - periodProjection L z.2) = _
      rw [hNative z hz]
      change z.2 + (periodChart L).symm
        (periodProjection L (Q z 0) - periodProjection L z.2) = _
      rw [← map_sub]
      have he := (periodChart L).left_inv hs
      change (periodChart L).symm (periodProjection L (d z)) = d z at he
      rw [he]
      dsimp only [d]
      ring
    have hpath : ContinuousAt (fun rho : ℝ => (rho, s)) 0 :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact hQr.congr_of_eventuallyEq (hEq.comp_tendsto hpath)
  have hAs (s : ℝ) : HasDerivAt (fun t => a (0, t)) 1 s := by
    have he : (fun t => a (0, t)) = (id : ℝ → ℝ) := funext hA0
    rw [he]
    exact hasDerivAt_id s
  letI := periodCircleChartedSpace L
  have hpl : Continuous hpL.lift := (periodicLift_contMDiff hp hpL).continuous
  let jn : ℝ × AddCircle L → ℝ × Coord := fun z => (z.1, hpL.lift z.2)
  have hjn : Continuous jn := continuous_fst.prodMk (hpl.comp continuous_snd)
  let Dn := jn ⁻¹' e.target
  have hDn : IsOpen Dn := e.open_target.preimage hjn
  let dn : ℝ × AddCircle L → AddCircle L := fun z => (e.symm (jn z)).2.1 - z.2
  have hdn : ContinuousOn dn Dn :=
    ((e.continuousOn_symm.comp hjn.continuousOn (fun _ hz => hz)).snd.fst).sub
      continuous_snd.continuousOn
  let W := Dn ∩ dn ⁻¹' (periodChart L).target
  have hW : IsOpen W := hdn.isOpen_inter_preimage hDn (periodChart L).open_target
  have hWaxis (q : AddCircle L) : (0, q) ∈ W := by
    have hF0 : visibleConnectorDisplacedNativePsi hpL hw0L hwL (0, (q, 0)) =
        (0, hpL.lift q) := by
      simp only [visibleConnectorDisplacedNativePsi, zero_smul, add_zero]
    have ht := e.map_source (haxisE q)
    rw [hef, hF0] at ht
    have hi := e.left_inv (haxisE q)
    rw [hef, hF0] at hi
    refine ⟨ht, ?_⟩
    change (e.symm (0, hpL.lift q)).2.1 - q ∈ (periodChart L).target
    rw [hi, sub_self]
    exact periodChart_zero_target L
  let K : Set (ℝ × AddCircle L) := (fun q : AddCircle L => ((0 : ℝ), q)) '' univ
  have hK : IsCompact K := isCompact_univ.image (continuous_const.prodMk continuous_id)
  have hKW : K ⊆ W := by rintro _ ⟨q, _, rfl⟩; exact hWaxis q
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  refine ⟨e, hef, hLocal, hD, hA, hBs.mono inter_subset_left, hEquation, hPhasePeriod,
    hHeightPeriod, hA0, hB0, hAr, hAs, hBr, r / 2, half_pos hr, ?_⟩
  intro z hz
  have hn : (z.1, periodProjection L z.2) ∈ W := by
    apply hrW
    apply Metric.thickening_subset_cthickening r K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, periodProjection L z.2), ⟨periodProjection L z.2, mem_univ _, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt ((abs_le.mpr hz.1).trans_lt (half_lt_self hr)) hr
  change (z.1, p z.2) ∈ e.target ∧
    (e.symm (z.1, p z.2)).2.1 - periodProjection L z.2 ∈ (periodChart L).target
  change (z.1, hpL.lift (periodProjection L z.2)) ∈ e.target ∧
    (e.symm (z.1, hpL.lift (periodProjection L z.2))).2.1 - periodProjection L z.2 ∈
      (periodChart L).target at hn
  simpa only [periodicLift_coe] using hn

end
end TightVer401