import TightVer401.VisibleConnectorDisplacedSeamLocal
import TightVer401.VisibleConnectorIncomingCollar

/-! Compact native injectivity for the actual joint displaced ruling. The
original-point inverse image and a real periodic phase lift remain separate. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def visibleConnectorDisplacedNativePsi {L : ℝ} {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (z : ℝ × (AddCircle L × ℝ)) : ℝ × Coord :=
  (z.1, hpL.lift z.2.1 + z.1 • hw0L.lift z.2.1 + z.2.2 • (hwL z.1).lift z.2.1)

def visibleConnectorDisplacedNativeChart (L s : ℝ) [Fact (0 < L)] :
    OpenPartialHomeomorph (ℝ × Coord) (ℝ × (AddCircle L × ℝ)) :=
  (Homeomorph.refl ℝ).toOpenPartialHomeomorph.prod (ruledCircleChart L s)

theorem visibleConnectorDisplacedNativeChart_apply (L s : ℝ) [Fact (0 < L)] (z : ℝ × Coord) :
    visibleConnectorDisplacedNativeChart L s z = (z.1, (periodProjection L (z.2 0), z.2 1)) := rfl

theorem visibleConnectorDisplacedNativePsi_chart {L : ℝ} [Fact (0 < L)]
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L) (s : ℝ) (z : ℝ × Coord) :
    visibleConnectorDisplacedNativePsi hpL hw0L hwL (visibleConnectorDisplacedNativeChart L s z) =
      visibleConnectorDisplacedPsi p w0 w z := by
  rw [visibleConnectorDisplacedNativeChart_apply]
  change (z.1, hpL.lift (periodProjection L (z.2 0)) +
    z.1 • hw0L.lift (periodProjection L (z.2 0)) +
    z.2 1 • (hwL z.1).lift (periodProjection L (z.2 0))) = _
  rw [periodicLift_coe, periodicLift_coe, periodicLift_coe]
  rfl

private theorem displacedNative_local_gate {L : ℝ} [Fact (0 < L)]
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hOmega : IsOpen Omega) (hw : ContDiffOn ℝ ∞ w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega) (hwzero : ∀ s, w (0, s) = w0 s)
    (hdet : ∀ s, visibleConnectorDet (deriv p s) (w0 s) ≠ 0) (q : AddCircle L) :
    ∃ T : Set (ℝ × (AddCircle L × ℝ)), IsOpen T ∧ (0, (q, 0)) ∈ T ∧
      ContinuousOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) T ∧
      InjOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) T := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  let c := visibleConnectorDisplacedNativeChart L s
  let z0 : ℝ × Coord := (0, ![s, 0])
  have hzC : z0 ∈ c.source := ⟨mem_univ _, ruledCircleChart_center_source L s⟩
  obtain ⟨e, he, hef, heOmega, _, _, _, _, _, _, _, _, _⟩ :=
    visibleConnectorDisplaced_exists_local_inverse hp hw0 hOmega hw hwzero s (haxis s) (hdet s)
  let T := c.target ∩ c.symm ⁻¹' e.source
  have hT : IsOpen T := c.isOpen_inter_preimage_symm e.open_source
  have hcenter : c z0 ∈ T := by
    refine ⟨c.map_source hzC, ?_⟩
    change c.symm (c z0) ∈ e.source
    rw [c.left_inv hzC]
    exact he
  have hmatch : EqOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL)
      (visibleConnectorDisplacedPsi p w0 w ∘ c.symm) T := by
    intro z hz
    have h := visibleConnectorDisplacedNativePsi_chart hpL hw0L hwL s (c.symm z)
    change visibleConnectorDisplacedNativePsi hpL hw0L hwL (c (c.symm z)) =
      visibleConnectorDisplacedPsi p w0 w (c.symm z) at h
    rw [c.right_inv hz.1] at h
    exact h
  have hcart : ContinuousOn (visibleConnectorDisplacedPsi p w0 w) e.source :=
    (visibleConnectorDisplacedPsi_contDiffOn hp hw0 hw).continuousOn.mono heOmega
  have hcont : ContinuousOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) T :=
    (hcart.comp (c.continuousOn_symm.mono inter_subset_left) (fun _ hz => hz.2)).congr hmatch
  have hi : InjOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) T := by
    intro x hx y hy hxy
    apply c.symm.injOn hx.1 hy.1
    apply e.injOn hx.2 hy.2
    rw [hef]
    exact (hmatch hx).symm.trans (hxy.trans (hmatch hy))
  refine ⟨T, hT, ?_, hcont, hi⟩
  have hc0 : c z0 = (0, ((s : AddCircle L), 0)) := rfl
  rw [hc0] at hcenter
  exact hcenter

/-- The compact original native curve supplies ONE actual joint collar.
The width applies simultaneously to displacement rho and ruling height u.
No inverse-image coverage or real phase patch is assumed or asserted. -/
theorem visibleConnectorDisplaced_exists_compact_native_collar {L : ℝ} [Fact (0 < L)]
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hip : Injective hpL.lift) (hOmega : IsOpen Omega) (hw : ContDiffOn ℝ ∞ w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega) (hwzero : ∀ s, w (0, s) = w0 s)
    (hdet : ∀ s, visibleConnectorDet (deriv p s) (w0 s) ≠ 0) :
    ∃ V : Set (ℝ × (AddCircle L × ℝ)), IsOpen V ∧
      (∀ q : AddCircle L, (0, (q, 0)) ∈ V) ∧
      ContinuousOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) V ∧
      InjOn (visibleConnectorDisplacedNativePsi hpL hw0L hwL) V ∧
      ∃ delta > 0,
        (Icc (-delta) delta ×ˢ ((univ : Set (AddCircle L)) ×ˢ Icc (-delta) delta)) ⊆ V ∧
        Topology.IsEmbedding
          (fun z : ↥(Ioo (-delta) delta ×ˢ ((univ : Set (AddCircle L)) ×ˢ Ioo (-delta) delta)) =>
            visibleConnectorDisplacedNativePsi hpL hw0L hwL z) := by
  let F := visibleConnectorDisplacedNativePsi hpL hw0L hwL
  let K : Set (ℝ × (AddCircle L × ℝ)) := (fun q : AddCircle L => (0, (q, (0 : ℝ)))) '' univ
  have hK : IsCompact K := isCompact_univ.image
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  choose T hTo hTmem hTcont hTinj using
    displacedNative_local_gate hp hw0 hpL hw0L hwL hOmega hw haxis hwzero hdet
  have hiK : InjOn F K := by
    rintro _ ⟨q, _, rfl⟩ _ ⟨r, _, rfl⟩ h
    have hpr : hpL.lift q = hpL.lift r := by
      simpa only [F, visibleConnectorDisplacedNativePsi, zero_smul, add_zero] using
        congrArg (fun z : ℝ × Coord => z.2) h
    exact congrArg (fun z : AddCircle L => (0, (z, (0 : ℝ)))) (hip hpr)
  have hcK : ∀ z ∈ K, ContinuousAt F z := by
    rintro _ ⟨q, _, rfl⟩
    exact (hTcont q _ (hTmem q)).continuousAt ((hTo q).mem_nhds (hTmem q))
  have hlK : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn F U := by
    rintro _ ⟨q, _, rfl⟩
    exact ⟨T q, (hTo q).mem_nhds (hTmem q), hTinj q⟩
  obtain ⟨V0, hV0, hKV0, hiV0⟩ := hiK.exists_isOpen_superset hK hcK hlK
  let O := ⋃ q : AddCircle L, T q
  have hO : IsOpen O := isOpen_iUnion hTo
  have hcO : ContinuousOn F O := by
    intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp hz
    exact ((hTcont q z hq).continuousAt ((hTo q).mem_nhds hq)).continuousWithinAt
  let V := V0 ∩ O
  have hV : IsOpen V := hV0.inter hO
  have hKV : K ⊆ V := by
    rintro _ ⟨q, _, rfl⟩
    exact ⟨hKV0 ⟨q, mem_univ _, rfl⟩, mem_iUnion.mpr ⟨q, hTmem q⟩⟩
  have hiV : InjOn F V := hiV0.mono inter_subset_left
  have hcV : ContinuousOn F V := hcO.mono inter_subset_right
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let delta := r / 2
  have hd : 0 < delta := half_pos hr
  let S : Set (ℝ × (AddCircle L × ℝ)) :=
    Icc (-delta) delta ×ˢ (univ ×ˢ Icc (-delta) delta)
  have hSV : S ⊆ V := by
    intro z hz
    apply hrV
    apply Metric.thickening_subset_cthickening r K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, (z.2.1, 0)), ⟨z.2.1, mem_univ _, rfl⟩, ?_⟩
    rw [Prod.dist_eq, Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt ((abs_le.mpr hz.1).trans_lt (half_lt_self hr))
      (max_lt hr ((abs_le.mpr hz.2.2).trans_lt (half_lt_self hr)))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_univ.prod isCompact_Icc)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcS : Continuous (fun z : S => F z) :=
    continuousOn_iff_continuous_restrict.mp (hcV.mono hSV)
  have hiS : Injective (fun z : S => F z) := fun x y h =>
    Subtype.ext (hiV (hSV x.property) (hSV y.property) h)
  have heS := (hcS.isClosedEmbedding hiS).isEmbedding
  have hopen : (Ioo (-delta) delta ×ˢ (univ ×ˢ Ioo (-delta) delta) :
      Set (ℝ × (AddCircle L × ℝ))) ⊆ S :=
    prod_mono Ioo_subset_Icc_self (prod_mono Subset.rfl Ioo_subset_Icc_self)
  refine ⟨V, hV, fun q => hKV ⟨q, mem_univ _, rfl⟩, hcV, hiV, delta, hd, hSV, ?_⟩
  exact heS.comp (Topology.IsEmbedding.inclusion hopen)

end
end TightVer401