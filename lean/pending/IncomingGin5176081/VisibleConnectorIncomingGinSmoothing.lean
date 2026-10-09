import TightVer401.VisibleConnectorDisplacedSeamOpenImage
import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.SeamNormalRegularTube

/-! Actual inverse-height calculus for the displaced incoming Gin seam.
The inverse is the constructed displaced ruling inverse. No side classifier,
global extension of Gin, or exterior smoothing package is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def visibleConnectorIncomingGinHeight {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (rho : ℝ) (y : Coord) : ℝ := (e.symm (rho, y)).2.2

def visibleConnectorIncomingGinDomain {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (rho : ℝ) : Set Coord := (fun y => (rho, y)) ⁻¹' e.target

def visibleConnectorIncomingGinSide {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (rho : ℝ) : Set Coord := {y | visibleConnectorIncomingGinHeight e rho y < 0}

theorem visibleConnectorIncomingGinDomain_isOpen {L : ℝ}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord)) (rho : ℝ) :
    IsOpen (visibleConnectorIncomingGinDomain e rho) :=
  e.open_target.preimage (continuous_const.prodMk continuous_id)

/-- The scalar height is smooth on the ACTUAL slice of the constructed image.
The local-chart premise is literally retained by the native inverse producer. -/
theorem visibleConnectorIncomingGinHeight_contDiffOn {L : ℝ} [Fact (0 < L)]
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hlocal : ∀ y ∈ e.target, ∃ s : ℝ,
      ∃ a : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
      ContDiffOn ℝ ∞ a.symm a.target ∧
      ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧
        B ⊆ e.target ∧ B ⊆ a.target ∧
        (∀ v ∈ B, e.symm v = visibleConnectorDisplacedNativeChart L s (a.symm v)))
    (rho : ℝ) :
    ContDiffOn ℝ ∞ (visibleConnectorIncomingGinHeight e rho)
      (visibleConnectorIncomingGinDomain e rho) := by
  intro y hy
  obtain ⟨s, a, ha, B, hB, hyB, _, hBa, heq⟩ := hlocal (rho, y) hy
  have hpath : ContDiff ℝ ∞ (fun z : Coord => (rho, z)) :=
    contDiff_const.prodMk contDiff_id
  have hi : ContDiffAt ℝ ∞ a.symm (rho, y) :=
    (ha _ (hBa hyB)).contDiffAt (a.open_target.mem_nhds (hBa hyB))
  have hs : ContDiffAt ℝ ∞ (fun z : Coord => (a.symm (rho, z)).2 1) y :=
    (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt.comp y ((hi.comp y hpath.contDiffAt).snd)
  have hgerm : (fun z => (a.symm (rho, z)).2 1) =ᶠ[𝓝 y]
      visibleConnectorIncomingGinHeight e rho := by
    filter_upwards [(hB.preimage hpath.continuous).mem_nhds hyB] with z hz
    simp only [visibleConnectorIncomingGinHeight, heq _ hz,
      visibleConnectorDisplacedNativeChart_apply]
  exact (hs.congr_of_eventuallyEq hgerm.symm).contDiffWithinAt

/-- The actual native inverse producer, with its scalar smoothness retained
on every target slice. This constructs an inverse rather than assuming one. -/
theorem visibleConnectorIncomingGin_exists_inverse_height {L : ℝ} [Fact (0 < L)]
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
      (∀ rho, ContDiffOn ℝ ∞ (visibleConnectorIncomingGinHeight e rho)
        (visibleConnectorIncomingGinDomain e rho)) ∧
      (∀ s, HasDerivAt
        (fun rho => visibleConnectorIncomingGinHeight e rho (p s)) (-1) 0) ∧
      ∃ delta > 0, ∀ rho s, |rho| ≤ delta →
        p s ∈ visibleConnectorIncomingGinDomain e rho := by
  obtain ⟨e, hef, hsource, _, hlocal, _, _, _, _, _, _, _, hBr,
    delta, hdelta, hcover⟩ := visibleConnectorDisplaced_exists_native_open_image
      hp hw0 hpL hw0L hwL hip hOmega hw haxis hwzero hdet
  refine ⟨e, hef, hsource, fun rho => visibleConnectorIncomingGinHeight_contDiffOn e hlocal rho,
    ?_, delta, hdelta, hcover⟩
  intro s
  exact hBr s

/-- Compactness selects a single displacement interval for the WHOLE new
seam in the source of that SAME actual inverse. -/
theorem visibleConnectorIncomingGin_exists_source_displacement_bound {L : ℝ} [Fact (0 < L)]
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (haxis : ∀ q : AddCircle L, (0, (q, 0)) ∈ e.source) :
    ∃ delta > 0, ∀ rho q, |rho| ≤ delta → (rho, (q, 0)) ∈ e.source := by
  let K : Set (ℝ × (AddCircle L × ℝ)) :=
    (fun q : AddCircle L => ((0 : ℝ), (q, (0 : ℝ)))) '' univ
  have hK : IsCompact K := isCompact_univ.image
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hKS : K ⊆ e.source := by rintro _ ⟨q, _, rfl⟩; exact haxis q
  obtain ⟨r, hr, hthick⟩ := hK.exists_cthickening_subset_open e.open_source hKS
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro rho q hrho
  apply hthick
  apply Metric.thickening_subset_cthickening r K
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(0, (q, 0)), ⟨q, mem_univ _, rfl⟩, ?_⟩
  rw [Prod.dist_eq, dist_self]
  simp only [Real.dist_eq, sub_zero]
  exact max_lt (hrho.trans_lt (half_lt_self hr)) hr

/-- Actual forward/inverse equality at every height for which the constructed
native ruling is defined. -/
theorem visibleConnectorIncomingGinHeight_forward {L : ℝ}
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
      visibleConnectorDisplacedNativePsi hpL hw0L hwL)
    (rho s u : ℝ) (hx : (rho, (periodProjection L s, u)) ∈ e.source) :
    visibleConnectorDisplacedPhi p w0 w rho (![s, u] : Coord) ∈
        visibleConnectorIncomingGinDomain e rho ∧
      visibleConnectorIncomingGinHeight e rho
        (visibleConnectorDisplacedPhi p w0 w rho (![s, u] : Coord)) = u := by
  have hactual : e (rho, (periodProjection L s, u)) =
      (rho, visibleConnectorDisplacedPhi p w0 w rho (![s, u] : Coord)) := by
    rw [hef]
    simp only [visibleConnectorDisplacedNativePsi, periodicLift_coe,
      visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hm := e.map_source hx
  have hi := e.left_inv hx
  rw [hactual] at hm hi
  exact ⟨hm, congrArg (fun z : ℝ × (AddCircle L × ℝ) => z.2.2) hi⟩

/-- The two actual inverse-height derivative identities use left-inverse
germs; no transported differential is granted. -/
theorem visibleConnectorIncomingGinHeight_derivatives {L : ℝ}
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
      visibleConnectorDisplacedNativePsi hpL hw0L hwL)
    (rho : ℝ)
    (hsource : ∀ s, (rho, (periodProjection L s, 0)) ∈ e.source)
    (hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingGinHeight e rho)
      (visibleConnectorIncomingGinDomain e rho)) (s : ℝ) :
    let pc := fun r => p r + rho • w0 r
    visibleConnectorIncomingGinHeight e rho (pc s) = 0 ∧
      fderiv ℝ (visibleConnectorIncomingGinHeight e rho) (pc s) (deriv pc s) = 0 ∧
      fderiv ℝ (visibleConnectorIncomingGinHeight e rho) (pc s) (w (rho, s)) = 1 := by
  let pc := fun r => p r + rho • w0 r
  have hpc : ContDiff ℝ ∞ pc := hp.add (contDiff_const.smul hw0)
  have hzero (r : ℝ) : visibleConnectorIncomingGinHeight e rho (pc r) = 0 := by
    simpa only [visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_smul, add_zero, pc] using
      (visibleConnectorIncomingGinHeight_forward hpL hw0L hwL e hef rho r 0 (hsource r)).2
  have hmem : pc s ∈ visibleConnectorIncomingGinDomain e rho := by
    simpa only [visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_smul, add_zero, pc] using
      (visibleConnectorIncomingGinHeight_forward hpL hw0L hwL e hef rho s 0 (hsource s)).1
  have hBd := ((hB _ hmem).contDiffAt
    ((visibleConnectorIncomingGinDomain_isOpen e rho).mem_nhds hmem)).differentiableAt (by simp)
  have ht := hBd.hasFDerivAt.comp_hasDerivAt s (hpc.differentiable (by simp) s).hasDerivAt
  have htz : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (fderiv ℝ (visibleConnectorIncomingGinHeight e rho) (pc s) (deriv pc s)) s := by
    simpa only [Function.comp_def, hzero] using ht
  have hline : HasDerivAt (fun u : ℝ => pc s + u • w (rho, s)) (w (rho, s)) 0 := by
    simpa using
      (hasDerivAt_const 0 (pc s)).add ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (w (rho, s))))
  have hBdLine : DifferentiableAt ℝ (visibleConnectorIncomingGinHeight e rho)
      (pc s + (0 : ℝ) • w (rho, s)) := by
    simpa only [zero_smul, add_zero] using hBd
  have hu := hBdLine.hasFDerivAt.comp_hasDerivAt 0 hline
  simp only [zero_smul, add_zero] at hu
  have hpath : Continuous (fun u : ℝ => (rho, (periodProjection L s, u))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hlineEq : (fun u => visibleConnectorIncomingGinHeight e rho (pc s + u • w (rho, s)))
      =ᶠ[𝓝 0] id := by
    filter_upwards [(e.open_source.preimage hpath).mem_nhds (hsource s)] with u hx
    simpa only [pc, visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one]
      using (visibleConnectorIncomingGinHeight_forward hpL hw0L hwL e hef rho s u hx).2
  have hui : HasDerivAt (id : ℝ → ℝ)
      (fderiv ℝ (visibleConnectorIncomingGinHeight e rho) (pc s) (w (rho, s))) 0 := by
    exact hu.congr_of_eventuallyEq hlineEq.symm
  exact ⟨hzero s, htz.unique (hasDerivAt_const s 0), hui.unique (hasDerivAt_id 0)⟩

private theorem incomingGin_clm_coordinates (A : Coord →L[ℝ] ℝ) (v : Coord) :
    A v = v 0 * A (Pi.single 0 1) + v 1 * A (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The exact normal derivative. The numerator is Euclidean squared length,
not the sup norm squared of `Coord`. -/
theorem visibleConnectorIncomingGin_normal_derivative (A : Coord →L[ℝ] ℝ)
    (v w : Coord) (hv : A v = 0) (hw : A w = 1) :
    visibleConnectorDet v w * A (visibleConnectorJ v) = v 0 ^ 2 + v 1 ^ 2 := by
  have halgebra : visibleConnectorDet v w * A (visibleConnectorJ v) =
      (v 0 ^ 2 + v 1 ^ 2) * A w - (v 0 * w 0 + v 1 * w 1) * A v := by
    simp only [incomingGin_clm_coordinates, visibleConnectorDet, visibleConnectorJ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [halgebra, hv, hw]
  ring

theorem visibleConnectorIncomingGin_normal_derivative_neg (A : Coord →L[ℝ] ℝ)
    (v w : Coord) (hv : A v = 0) (hw : A w = 1)
    (hdet : visibleConnectorDet v w < 0) : A (visibleConnectorJ v) < 0 := by
  have hsq : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        simp [visibleConnectorDet, h0, h1] at hdet
      simpa only [h0, zero_pow (by decide : 2 ≠ 0), zero_add] using sq_pos_of_ne_zero h1
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (sq_nonneg _)
  have hprod := visibleConnectorIncomingGin_normal_derivative A v w hv hw
  nlinarith

/-- At the displaced seam, the actual inverse height decreases on the
canonical positive normal. -/
theorem visibleConnectorIncomingGinHeight_normal_neg {L : ℝ}
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
      visibleConnectorDisplacedNativePsi hpL hw0L hwL)
    (rho : ℝ) (hsource : ∀ s, (rho, (periodProjection L s, 0)) ∈ e.source)
    (hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingGinHeight e rho)
      (visibleConnectorIncomingGinDomain e rho))
    (hdet : ∀ s, visibleConnectorDet (deriv (fun r => p r + rho • w0 r) s) (w (rho, s)) < 0)
    (s : ℝ) :
    fderiv ℝ (visibleConnectorIncomingGinHeight e rho) (p s + rho • w0 s)
      (visibleConnectorJ (deriv (fun r => p r + rho • w0 r) s)) < 0 := by
  obtain ⟨_, hv, hw⟩ := visibleConnectorIncomingGinHeight_derivatives hp hw0 hpL hw0L hwL
    e hef rho hsource hB s
  exact visibleConnectorIncomingGin_normal_derivative_neg _ _ _ hv hw (hdet s)

/-- Compact separation constructs a modification neighborhood whose closure
avoids the ORIGINAL negative graph, without changing the fixed ambient domain. -/
theorem visibleConnectorIncomingGin_exists_modification_neighborhood
    {B : Coord → ℝ} {V C K : Set Coord} (hV : IsOpen V)
    (hC : IsCompact C) (hK : IsCompact K) (hCV : C ⊆ V)
    (hzero : ∀ x ∈ C, B x = 0) (hnegative : ∀ x ∈ K, B x < 0) :
    ∃ N : Set Coord, IsOpen N ∧ C ⊆ N ∧ closure N ⊆ V \ K := by
  have hCK : C ⊆ V \ K := by
    intro x hx
    refine ⟨hCV hx, ?_⟩
    intro hxK
    have hn := hnegative x hxK
    rw [hzero x hx] at hn
    exact lt_irrefl 0 hn
  have hW : IsOpen (V \ K) := hV.diff hK.isClosed
  obtain ⟨r, hr, hthick⟩ := hC.exists_cthickening_subset_open hW hCK
  refine ⟨Metric.thickening r C, Metric.isOpen_thickening, ?_, ?_⟩
  · exact Metric.self_subset_thickening hr C
  · exact (Metric.closure_thickening_subset_cthickening r C).trans hthick

/-- Full scalar germ preservation at the ORIGINAL curve follows from the
relative construction's outside germ and actual negative inverse height.
This is a consumer of that literal outside equality, not a smoothing grant. -/
theorem visibleConnectorIncomingGin_retain_original_scalar_germ
    {B Gin raw H : Coord → ℝ} {V N : Set Coord} {p : ℝ → Coord}
    (hV : IsOpen V) (hB : ContinuousOn B V)
    (hpV : ∀ s, p s ∈ V) (hpN : ∀ s, p s ∉ N) (hb : ∀ s, B (p s) < 0)
    (houtside : ∀ x ∈ V \ N,
      H =ᶠ[𝓝 x] (fun y => if B y < 0 then Gin y else raw y)) :
    ∀ s, H =ᶠ[𝓝 (p s)] Gin := by
  intro s
  have hc : ContinuousAt B (p s) := (hB _ (hpV s)).continuousAt (hV.mem_nhds (hpV s))
  have hbranch : (fun y => if B y < 0 then Gin y else raw y) =ᶠ[𝓝 (p s)] Gin := by
    filter_upwards [hc.eventually (gt_mem_nhds (hb s))] with y hy
    exact if_pos hy
  exact (houtside (p s) ⟨hpV s, hpN s⟩).trans hbranch

end
end TightVer401
