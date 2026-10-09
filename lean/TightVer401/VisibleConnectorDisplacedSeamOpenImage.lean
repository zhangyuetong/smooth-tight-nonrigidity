import TightVer401.VisibleConnectorDisplacedSeamCompact

/-! The actual compact displaced ruling has an OPEN Cartesian image and an
actual native inverse there. Every original p(s) is covered for one rho interval.
Local real chart solutions retain their literal displacement derivatives. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The native inverse solution to the original, undisplaced incoming curve. -/
def visibleConnectorDisplacedNativeSolution {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) (z : ℝ × ℝ) : AddCircle L × ℝ :=
  (e.symm (z.1, p z.2)).2

/-- Its actual open target preimage; no global ruling extension is used. -/
def visibleConnectorDisplacedNativeSolutionDomain {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (p : ℝ → Coord) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => (z.1, p z.2)) ⁻¹' e.target

private theorem displaced_inverse_fderiv_injective
    {f : (ℝ × Coord) → ℝ × Coord}
    (e : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord))
    (hef : (e : (ℝ × Coord) → ℝ × Coord) = f)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {x : ℝ × Coord} (hx : x ∈ e.source) (hf : ContDiffAt ℝ ∞ f x) :
    Injective (fderiv ℝ f x) := by
  have hy : f x ∈ e.target := by rw [← hef]; exact e.map_source hx
  have hi : ContDiffAt ℝ ∞ e.symm (f x) :=
    (hei _ hy).contDiffAt (e.open_target.mem_nhds hy)
  let D := fderiv ℝ f x
  let B := fderiv ℝ e.symm (f x)
  have hc : HasFDerivAt (e.symm ∘ f) (B.comp D) x :=
    (hi.differentiableAt (by simp)).hasFDerivAt.comp x
      (hf.differentiableAt (by simp)).hasFDerivAt
  have heq : (e.symm ∘ f) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    change e.symm (f y) = y
    rw [← hef]
    exact e.left_inv hy
  have hid : HasFDerivAt (id : (ℝ × Coord) → ℝ × Coord) (B.comp D) x :=
    hc.congr_of_eventuallyEq heq.symm
  have hBD : B.comp D = ContinuousLinearMap.id ℝ (ℝ × Coord) :=
    hid.unique (hasFDerivAt_id x)
  have hleft : LeftInverse B D := by
    intro v
    have hv := congrArg (fun A : (ℝ × Coord) →L[ℝ] ℝ × Coord => A v) hBD
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hv
  exact hleft.injective

/-- ONE actual native inverse covers every original point for a uniform small
rho interval. Each source point has an actual Omega chart with injective joint
Jacobian; each central target has a smooth real chart solution of the original
ruling equation. In those charts a_rho=0 and b_rho=-1, with the SAME global
native inverse. A patched global real phase and uniform negative b are later
obligations. -/
theorem visibleConnectorDisplaced_exists_native_open_image {L : ℝ} [Fact (0 < L)]
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
      (∀ q : AddCircle L, (0, (q, 0)) ∈ e.source) ∧
      (∀ z ∈ e.source, ∃ s : ℝ,
        z ∈ (visibleConnectorDisplacedNativeChart L s).target ∧
        (((visibleConnectorDisplacedNativeChart L s).symm z).1,
          ((visibleConnectorDisplacedNativeChart L s).symm z).2 0) ∈ Omega ∧
        Injective (fderiv ℝ (visibleConnectorDisplacedPsi p w0 w)
          ((visibleConnectorDisplacedNativeChart L s).symm z))) ∧
      (∀ y ∈ e.target, ∃ s : ℝ,
        ∃ a : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
        ContDiffOn ℝ ∞ a.symm a.target ∧
        ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧
          B ⊆ e.target ∧ B ⊆ a.target ∧
          (∀ v ∈ B, e.symm v = visibleConnectorDisplacedNativeChart L s (a.symm v))) ∧
      IsOpen (visibleConnectorDisplacedNativeSolutionDomain e p) ∧
      ContinuousOn (visibleConnectorDisplacedNativeSolution e p)
        (visibleConnectorDisplacedNativeSolutionDomain e p) ∧
      ContDiffOn ℝ ∞ (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
        (visibleConnectorDisplacedNativeSolutionDomain e p) ∧
      (∀ z ∈ visibleConnectorDisplacedNativeSolutionDomain e p,
        visibleConnectorDisplacedNativePsi hpL hw0L hwL
          (z.1, visibleConnectorDisplacedNativeSolution e p z) = (z.1, p z.2)) ∧
      (∀ rho, Periodic (fun s => visibleConnectorDisplacedNativeSolution e p (rho, s)) L) ∧
      (∀ s, visibleConnectorDisplacedNativeSolution e p (0, s) =
        (periodProjection L s, 0)) ∧
      (∀ s, ∃ D : Set (ℝ × ℝ), ∃ Q : (ℝ × ℝ) → Coord,
        IsOpen D ∧ (0, s) ∈ D ∧
        D ⊆ visibleConnectorDisplacedNativeSolutionDomain e p ∧
        ContDiffOn ℝ ∞ Q D ∧
        (∀ z ∈ D, visibleConnectorDisplacedNativeSolution e p z =
          (periodProjection L (Q z 0), Q z 1)) ∧
        (∀ z ∈ D, visibleConnectorDisplacedPhi p w0 w z.1 (Q z) = p z.2) ∧
        Q (0, s) = (![s, 0] : Coord) ∧
        HasDerivAt (fun rho => Q (rho, s) 0) 0 0 ∧
        HasDerivAt (fun rho => Q (rho, s) 1) (-1) 0) ∧
      (∀ s, HasDerivAt
        (fun rho => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) (-1) 0) ∧
      ∃ delta > 0, ∀ rho s, |rho| ≤ delta → (rho, p s) ∈ e.target := by
  let F := visibleConnectorDisplacedNativePsi hpL hw0L hwL
  let f := visibleConnectorDisplacedPsi p w0 w
  obtain ⟨V0, hV0, haxisV0, hcV0, hiV0, _⟩ :=
    visibleConnectorDisplaced_exists_compact_native_collar hp hw0 hpL hw0L hwL
      hip hOmega hw haxis hwzero hdet
  choose a ha haf haOmega hai haD haDm haQ haSolve haQ0 haQr haa hab using
    fun s => visibleConnectorDisplaced_exists_local_inverse hp hw0 hOmega hw hwzero
      s (haxis s) (hdet s)
  let c (s : ℝ) := visibleConnectorDisplacedNativeChart L s
  let ell (s : ℝ) := (c s).symm.trans (a s)
  have hellSource (s : ℝ) : (ell s).source =
      (c s).target ∩ (c s).symm ⁻¹' (a s).source := rfl
  have hmatch (s : ℝ) : EqOn F (ell s) (ell s).source := by
    intro z hz
    rw [hellSource] at hz
    have h := visibleConnectorDisplacedNativePsi_chart hpL hw0L hwL s ((c s).symm z)
    change F (c s ((c s).symm z)) = f ((c s).symm z) at h
    rw [(c s).right_inv hz.1] at h
    change F z = a s ((c s).symm z)
    rw [haf s]
    exact h
  have hcenter (s : ℝ) : (0, (periodProjection L s, 0)) ∈ (ell s).source := by
    let x : ℝ × Coord := (0, ![s, 0])
    have hx : x ∈ (c s).source := ⟨mem_univ _, ruledCircleChart_center_source L s⟩
    have h : c s x ∈ (ell s).source := by
      rw [hellSource]
      refine ⟨(c s).map_source hx, ?_⟩
      change (c s).symm (c s x) ∈ (a s).source
      rw [(c s).left_inv hx]
      exact ha s
    simpa only [c, x, visibleConnectorDisplacedNativeChart_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using h
  let O := ⋃ s : ℝ, (ell s).source
  let V := V0 ∩ O
  have hV : IsOpen V := hV0.inter (isOpen_iUnion fun s => (ell s).open_source)
  have haxisV (q : AddCircle L) : (0, (q, 0)) ∈ V := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨haxisV0 _, mem_iUnion.mpr ⟨s, hcenter s⟩⟩
  have hiV : InjOn F V := hiV0.mono inter_subset_left
  have hcV : ContinuousOn F V := hcV0.mono inter_subset_left
  have hopen (S : Set (ℝ × (AddCircle L × ℝ))) (hS : IsOpen S) (hSV : S ⊆ V) :
      IsOpen (F '' S) := by
    have hEq : F '' S = ⋃ s : ℝ, ell s '' (S ∩ (ell s).source) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨s, hs⟩ := mem_iUnion.mp (hSV hz).2
        exact mem_iUnion.mpr ⟨s, z, ⟨hz, hs⟩, (hmatch s hs).symm⟩
      · intro hy
        obtain ⟨s, z, hz, heq⟩ := mem_iUnion.mp hy
        exact ⟨z, hz.1, (hmatch s hz.2).trans heq⟩
    rw [hEq]
    exact isOpen_iUnion fun s => (ell s).isOpen_image_of_subset_source
      (hS.inter (ell s).open_source) inter_subset_right
  let pe := hiV.toPartialEquiv F V
  have hOpenRestriction : IsOpenMap (fun z : V => F z) := by
    intro S hS
    have hSambient : IsOpen (Subtype.val '' S) := hV.isOpenMap_subtype_val S hS
    have hSV : Subtype.val '' S ⊆ V := by rintro z ⟨x, _, rfl⟩; exact x.property
    have h := hopen (Subtype.val '' S) hSambient hSV
    simpa only [image_image, Function.comp_def] using h
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hcV hOpenRestriction hV
  have hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) = F := rfl
  have heSource : e.source = V := rfl
  have hsource : ∀ q : AddCircle L, (0, (q, 0)) ∈ e.source := haxisV
  have hregular : ∀ z ∈ e.source, ∃ s : ℝ,
      z ∈ (c s).target ∧
      (((c s).symm z).1, ((c s).symm z).2 0) ∈ Omega ∧
      Injective (fderiv ℝ f ((c s).symm z)) := by
    intro z hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp hz.2
    rw [hellSource] at hs
    have harg := haOmega s hs.2
    have hZ : IsOpen ((fun x : ℝ × Coord => (x.1, x.2 0)) ⁻¹' Omega) :=
      hOmega.preimage (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    have hf : ContDiffAt ℝ ∞ f ((c s).symm z) :=
      ((visibleConnectorDisplacedPsi_contDiffOn hp hw0 hw) _ harg).contDiffAt
        (hZ.mem_nhds harg)
    exact ⟨s, hs.1, harg, displaced_inverse_fderiv_injective (a s) (haf s) (hai s) hs.2 hf⟩
  have hlocalInverse (y : ℝ × Coord) (hy : y ∈ e.target) : ∃ s : ℝ,
      ∃ a : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
      ContDiffOn ℝ ∞ a.symm a.target ∧
      ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧
        B ⊆ e.target ∧ B ⊆ a.target ∧
        (∀ v ∈ B, e.symm v = c s (a.symm v)) := by
    have hx := e.map_target hy
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx.2
    have hellTarget : y ∈ (ell s).target := by
      have himage := (ell s).map_source hs
      rw [← hmatch s hs, ← hef, e.right_inv hy] at himage
      exact himage
    let B := ((ell s).target ∩ (ell s).symm ⁻¹' e.source) ∩ e.target
    have hB : IsOpen B := ((ell s).isOpen_inter_preimage_symm e.open_source).inter e.open_target
    have heq (v : ℝ × Coord) (hv : v ∈ B) : e.symm v = (ell s).symm v := by
      apply e.injOn (e.map_target hv.2) hv.1.2
      rw [e.right_inv hv.2, hef, hmatch s ((ell s).map_target hv.1.1),
        (ell s).right_inv hv.1.1]
    have heqy : e.symm y = (ell s).symm y := by
      apply (ell s).injOn hs ((ell s).map_target hellTarget)
      rw [← hmatch s hs, ← hef, e.right_inv hy, (ell s).right_inv hellTarget]
    have hyB : y ∈ B := by
      refine ⟨⟨hellTarget, ?_⟩, hy⟩
      change (ell s).symm y ∈ e.source
      rw [← heqy]
      exact hx
    exact ⟨s, a s, hai s, B, hB, hyB, inter_subset_right,
      fun _ hv => hv.1.1.1, fun v hv => heq v hv⟩
  let j : ℝ × ℝ → ℝ × Coord := fun z => (z.1, p z.2)
  have hj : Continuous j := continuous_fst.prodMk (hp.continuous.comp continuous_snd)
  have hDomain : IsOpen (visibleConnectorDisplacedNativeSolutionDomain e p) :=
    e.open_target.preimage hj
  have hSolution : ContinuousOn (visibleConnectorDisplacedNativeSolution e p)
      (visibleConnectorDisplacedNativeSolutionDomain e p) :=
    (e.continuousOn_symm.comp hj.continuousOn (fun _ hz => hz)).snd
  have hHeight : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedNativeSolutionDomain e p) := by
    intro z hz
    obtain ⟨s, a0, ha0, B, hB, hzB, _, hBa, heq⟩ := hlocalInverse (j z) hz
    have hAi : ContDiffAt ℝ ∞ a0.symm (j z) :=
      (ha0 _ (hBa hzB)).contDiffAt (a0.open_target.mem_nhds (hBa hzB))
    have hjAt : ContDiffAt ℝ ∞ j z :=
      (contDiff_fst.prodMk (hp.comp contDiff_snd)).contDiffAt
    have hc : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => (a0.symm (j x)).2 1) z :=
      (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt.comp z ((hAi.comp z hjAt).snd)
    have hEq : (fun x => (visibleConnectorDisplacedNativeSolution e p x).2) =ᶠ[𝓝 z]
        (fun x => (a0.symm (j x)).2 1) := by
      filter_upwards [(hB.preimage hj).mem_nhds hzB] with x hx
      change (e.symm (j x)).2.2 = _
      rw [heq _ hx, visibleConnectorDisplacedNativeChart_apply]
    exact (hc.congr_of_eventuallyEq hEq).contDiffWithinAt
  have hsolve (z : ℝ × ℝ) (hz : z ∈ visibleConnectorDisplacedNativeSolutionDomain e p) :
      F (z.1, visibleConnectorDisplacedNativeSolution e p z) = (z.1, p z.2) := by
    have heq := e.right_inv hz
    rw [hef] at heq
    have hrho := congrArg (fun t : ℝ × Coord => t.1) heq
    change (e.symm (z.1, p z.2)).1 = z.1 at hrho
    change F ((e.symm (z.1, p z.2)).1, (e.symm (z.1, p z.2)).2) = (z.1, p z.2) at heq
    rw [hrho] at heq
    exact heq
  have hperiod (rho : ℝ) : Periodic
      (fun s => visibleConnectorDisplacedNativeSolution e p (rho, s)) L := by
    intro s
    change (e.symm (rho, p (s + L))).2 = (e.symm (rho, p s)).2
    rw [hpL s]
  have hbase (s : ℝ) : visibleConnectorDisplacedNativeSolution e p (0, s) =
      (periodProjection L s, 0) := by
    have hF : F (0, (periodProjection L s, 0)) = (0, p s) := by
      simp only [F, visibleConnectorDisplacedNativePsi, periodicLift_coe, zero_smul, add_zero]
    have h := e.left_inv (hsource (periodProjection L s))
    rw [hef, hF] at h
    exact congrArg Prod.snd h
  have hcharts (s : ℝ) : ∃ D : Set (ℝ × ℝ), ∃ Q : (ℝ × ℝ) → Coord,
      IsOpen D ∧ (0, s) ∈ D ∧ D ⊆ visibleConnectorDisplacedNativeSolutionDomain e p ∧
      ContDiffOn ℝ ∞ Q D ∧
      (∀ z ∈ D, visibleConnectorDisplacedNativeSolution e p z =
        (periodProjection L (Q z 0), Q z 1)) ∧
      (∀ z ∈ D, visibleConnectorDisplacedPhi p w0 w z.1 (Q z) = p z.2) ∧
      Q (0, s) = (![s, 0] : Coord) ∧
      HasDerivAt (fun rho => Q (rho, s) 0) 0 0 ∧
      HasDerivAt (fun rho => Q (rho, s) 1) (-1) 0 := by
    let B := ((ell s).target ∩ (ell s).symm ⁻¹' e.source) ∩ e.target
    have hB : IsOpen B := ((ell s).isOpen_inter_preimage_symm e.open_source).inter e.open_target
    let z0 : ℝ × (AddCircle L × ℝ) := (0, (periodProjection L s, 0))
    have hF0 : F z0 = (0, p s) := by
      simp only [F, z0, visibleConnectorDisplacedNativePsi, periodicLift_coe, zero_smul, add_zero]
    have hell0 : ell s z0 = (0, p s) := (hmatch s (hcenter s)).symm.trans hF0
    have ht0 : (0, p s) ∈ (ell s).target := hell0 ▸ (ell s).map_source (hcenter s)
    have hB0 : (0, p s) ∈ B := by
      refine ⟨⟨ht0, ?_⟩, ?_⟩
      · change (ell s).symm (0, p s) ∈ e.source
        rw [← hell0]
        have hz0 : z0 ∈ (ell s).source := hcenter s
        rw [(ell s).left_inv hz0]
        exact hsource _
      · rw [← hF0, ← hef]
        exact e.map_source (hsource _)
    let D := j ⁻¹' B
    have hD : IsOpen D := hB.preimage hj
    have hD0 : (0, s) ∈ D := hB0
    have hDa : D ⊆ visibleConnectorDisplacedSolutionDomain (a s) p := by
      intro z hz
      exact hz.1.1.1
    have hDe : D ⊆ visibleConnectorDisplacedNativeSolutionDomain e p := fun _ hz => hz.2
    have heq (z : ℝ × ℝ) (hz : z ∈ D) : e.symm (j z) = (ell s).symm (j z) := by
      apply e.injOn (e.map_target hz.2) hz.1.2
      rw [e.right_inv hz.2, hef, hmatch s ((ell s).map_target hz.1.1),
        (ell s).right_inv hz.1.1]
    have hQeq (z : ℝ × ℝ) (hz : z ∈ D) :
        visibleConnectorDisplacedNativeSolution e p z =
          (periodProjection L (visibleConnectorDisplacedSolution (a s) p z 0),
            visibleConnectorDisplacedSolution (a s) p z 1) := by
      change (e.symm (j z)).2 = _
      rw [heq z hz]
      change (c s ((a s).symm (j z))).2 = _
      rw [visibleConnectorDisplacedNativeChart_apply]
      rfl
    exact ⟨D, visibleConnectorDisplacedSolution (a s) p, hD, hD0, hDe,
      (haQ s).mono hDa, hQeq, fun z hz => haSolve s z (hDa hz), haQ0 s, haa s, hab s⟩
  have hb (s : ℝ) : HasDerivAt
      (fun rho => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) (-1) 0 := by
    obtain ⟨D, Q, hD, hD0, _, _, hQ, _, _, _, hQr⟩ := hcharts s
    have hpath : Continuous (fun rho : ℝ => (rho, s)) := continuous_id.prodMk continuous_const
    have heq : (fun rho => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) =ᶠ[𝓝 0]
        (fun rho => Q (rho, s) 1) := by
      filter_upwards [(hD.preimage hpath).mem_nhds hD0] with rho hrho
      exact congrArg Prod.snd (hQ (rho, s) hrho)
    exact hQr.congr_of_eventuallyEq heq
  let K : Set (ℝ × (AddCircle L × ℝ)) :=
    (fun q : AddCircle L => (0, (q, (0 : ℝ)))) '' univ
  have hK : IsCompact K := isCompact_univ.image
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hKV : K ⊆ V := by rintro _ ⟨q, _, rfl⟩; exact haxisV q
  have hKt : IsCompact (F '' K) := hK.image_of_continuousOn (hcV.mono hKV)
  have hKtE : F '' K ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    rw [← hef]
    exact e.map_source (hKV hz)
  obtain ⟨r, hr, hrT⟩ := hKt.exists_cthickening_subset_open e.open_target hKtE
  refine ⟨e, hef, hsource, hregular, hlocalInverse, hDomain, hSolution, hHeight, hsolve, hperiod, hbase, hcharts, hb, r / 2, half_pos hr, ?_⟩
  intro rho s hrho
  apply hrT
  apply Metric.thickening_subset_cthickening r (F '' K)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(0, p s), ?_, ?_⟩
  · refine ⟨(0, (periodProjection L s, 0)), ⟨periodProjection L s, mem_univ _, rfl⟩, ?_⟩
    simp only [F, visibleConnectorDisplacedNativePsi, periodicLift_coe, zero_smul, add_zero]
  · rw [Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (hrho.trans_lt (half_lt_self hr)) hr

end
end TightVer401