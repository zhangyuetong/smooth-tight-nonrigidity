import TightVer401.VisibleConnectorLocalPotential
import TightVer401.PlanarGradientInverse
import TightVer401.ThinBandTopology
import TightVer401.ThinBandRuledCharts
import TightVer401.PeriodicCircleFunctions

/-! A thin collar for the actual incoming scalar potential. Both source and
actual gradient injectivity are derived from local inverses and the compact
central circle. Exterior-side certification and nesting are separate. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

local instance incomingCollarCircleChart (L : ℝ) [Fact (0 < L)] :
    ChartedSpace ℝ (AddCircle L) := periodCircleChartedSpace L

/-- The actual periodic raw source, retaining the specified incoming curve. -/
def visibleConnectorIncomingNative {L : ℝ} {p w : ℝ → Coord}
    (hpL : Periodic p L) (hwL : Periodic w L) (z : AddCircle L × ℝ) : Coord :=
  hpL.lift z.1 + z.2 • hwL.lift z.1

theorem visibleConnectorIncomingNative_chart {L : ℝ} [Fact (0 < L)]
    {p w : ℝ → Coord} (hpL : Periodic p L) (hwL : Periodic w L)
    (r : ℝ) (z : Coord) :
    visibleConnectorIncomingNative hpL hwL (ruledCircleChart L r z) =
      visibleConnectorSource p w z := by
  simp only [visibleConnectorIncomingNative, ruledCircleChart_apply, periodicLift_coe]
  rfl

theorem visibleConnectorIncomingNative_continuous {L : ℝ} [Fact (0 < L)]
    {p w : ℝ → Coord} (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hpL : Periodic p L) (hwL : Periodic w L) :
    Continuous (visibleConnectorIncomingNative hpL hwL) := by
  exact ((periodicLift_contMDiff hp hpL).continuous.comp continuous_fst).add
    (continuous_snd.smul ((periodicLift_contMDiff hw hwL).continuous.comp continuous_fst))

/-- An actual Cartesian inverse for the raw source near each central point.
Its source maps into the SAME prescribed open scalar-potential domain. -/
theorem visibleConnectorIncoming_exists_source_chart {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    {U : Set Coord} (hU : IsOpen U) (r : ℝ) (hpU : p r ∈ U)
    (hdet : visibleConnectorDet (deriv p r) (w r) < 0) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      (![r, 0] : Coord) ∈ e.source ∧
      e.source ⊆ (visibleConnectorSource p w) ⁻¹' U ∧
      (e : Coord → Coord) = visibleConnectorSource p w ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  have hd : ContDiff ℝ ∞ (visibleConnectorDelta p p w) := by
    unfold visibleConnectorDelta visibleConnectorA visibleConnectorC visibleConnectorB
      visibleConnectorDet dotProduct
    simp only [Fin.sum_univ_two]
    fun_prop
  let V := (visibleConnectorSource p w) ⁻¹' U ∩
    {z | visibleConnectorDelta p p w z ≠ 0}
  have hV : IsOpen V :=
    (hU.preimage (visibleConnectorSource_contDiff hp hw).continuous).inter
      (isOpen_ne_fun hd.continuous continuous_const)
  have hrV : (![r, 0] : Coord) ∈ V := by
    constructor
    · simpa [visibleConnectorSource] using hpU
    · simpa [visibleConnectorDelta, visibleConnectorA] using neg_ne_zero.mpr hdet.ne
  obtain ⟨e, he, heV, hef, hei⟩ := exists_smooth_local_inverse hV
    (visibleConnectorSource_contDiff hp hw).contDiffOn
    (fun z hz => visibleConnectorSource_fderiv_injective hp hw z hz.2) hrV
  exact ⟨e, he, heV.trans inter_subset_left, hef, hei⟩

private theorem incomingNative_local_inj {L : ℝ} [Fact (0 < L)]
    {p w : ℝ → Coord} (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hdet : ∀ r, visibleConnectorDet (deriv p r) (w r) < 0) (q : AddCircle L) :
    ∃ V ∈ 𝓝 (q, (0 : ℝ)), InjOn (visibleConnectorIncomingNative hpL hwL) V := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ V ∈ 𝓝 (periodProjection L r, (0 : ℝ)),
    InjOn (visibleConnectorIncomingNative hpL hwL) V
  obtain ⟨e, he, _, hef, _⟩ := visibleConnectorIncoming_exists_source_chart hp hw
    isOpen_univ r (mem_univ _) (hdet r)
  have hl : ∃ V ∈ 𝓝 (![r, 0] : Coord), InjOn (visibleConnectorSource p w) V := by
    refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
    simpa only [hef] using e.injOn
  have ht := local_injOn_transport_chart (ruledCircleChart_center_source L r)
    (fun z _ => visibleConnectorIncomingNative_chart hpL hwL r z) hl
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using ht

private theorem incomingNative_gradient_local_inj {L : ℝ} [Fact (0 < L)]
    {p w : ℝ → Coord} {Gin : Coord → ℝ} {U : Set Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hpU : ∀ r, p r ∈ U) (hneg : ∀ x ∈ U, (planarHessian Gin x).det < 0)
    (hdet : ∀ r, visibleConnectorDet (deriv p r) (w r) < 0) (q : AddCircle L) :
    ∃ V ∈ 𝓝 (q, (0 : ℝ)),
      InjOn (planarGradient Gin ∘ visibleConnectorIncomingNative hpL hwL) V := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ V ∈ 𝓝 (periodProjection L r, (0 : ℝ)),
    InjOn (planarGradient Gin ∘ visibleConnectorIncomingNative hpL hwL) V
  obtain ⟨e, he, _, hef, _⟩ := visibleConnectorIncoming_exists_source_chart hp hw
    hU r (hpU r) (hdet r)
  obtain ⟨g, hg, _, hgf, _⟩ := planarGradient_exists_smooth_local_inverse hGin hU
    (fun x hx => (hneg x hx).ne) (hpU r)
  have hraw := visibleConnectorSource_contDiff hp hw
  have hpre : (visibleConnectorSource p w) ⁻¹' g.source ∈ 𝓝 (![r, 0] : Coord) := by
    apply hraw.continuous.continuousAt.preimage_mem_nhds
    simpa [visibleConnectorSource] using g.open_source.mem_nhds hg
  have hl : ∃ V ∈ 𝓝 (![r, 0] : Coord), InjOn
      (planarGradient Gin ∘ visibleConnectorSource p w) V := by
    refine ⟨e.source ∩ (visibleConnectorSource p w) ⁻¹' g.source,
      inter_mem (e.open_source.mem_nhds he) hpre, ?_⟩
    intro x hx y hy hxy
    apply e.injOn hx.1 hy.1
    rw [hef]
    apply g.injOn hx.2 hy.2
    simpa only [hgf, Function.comp_apply] using hxy
  have ht := local_injOn_transport_chart (g := planarGradient Gin ∘
    visibleConnectorIncomingNative hpL hwL) (ruledCircleChart_center_source L r)
    (fun z _ => congrArg (planarGradient Gin)
      (visibleConnectorIncomingNative_chart hpL hwL r z)) hl
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using ht

/-- A single actual two-sided collar for the source and the SAME incoming
potential's gradient. No exterior-side or nesting conclusion is asserted. -/
theorem visibleConnectorIncoming_exists_actual_collar {L : ℝ} [Fact (0 < L)]
    {p gamma w : ℝ → Coord} {Gin : Coord → ℝ} {U : Set Coord}
    (hp : ContDiff ℝ ∞ p) (_hgamma : ContDiff ℝ ∞ gamma)
    (hw : ContDiff ℝ ∞ w) (hpL : Periodic p L)
    (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hip : Injective hpL.lift) (higamma : Injective hgammaL.lift)
    (hactual : gamma = planarGradient Gin ∘ p)
    (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U) (hpU : ∀ r, p r ∈ U)
    (hneg : ∀ x ∈ U, (planarHessian Gin x).det < 0)
    (hdet : ∀ r, visibleConnectorDet (deriv p r) (w r) < 0) :
    ∃ delta > 0,
      InjOn (visibleConnectorIncomingNative hpL hwL) (univ ×ˢ Icc (-delta) delta) ∧
      InjOn (planarGradient Gin ∘ visibleConnectorIncomingNative hpL hwL)
        (univ ×ˢ Icc (-delta) delta) ∧
      MapsTo (visibleConnectorIncomingNative hpL hwL) (univ ×ˢ Icc (-delta) delta) U ∧
      Topology.IsEmbedding (fun z : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-delta) delta) =>
        visibleConnectorIncomingNative hpL hwL z) ∧
      Topology.IsEmbedding (fun z : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-delta) delta) =>
        planarGradient Gin (visibleConnectorIncomingNative hpL hwL z)) ∧
      (∀ r, ∃ e : OpenPartialHomeomorph Coord Coord,
        (![r, 0] : Coord) ∈ e.source ∧
        e.source ⊆ (visibleConnectorSource p w) ⁻¹' U ∧
        (e : Coord → Coord) = visibleConnectorSource p w ∧
        ContDiffOn ℝ ∞ e.symm e.target) := by
  let F := visibleConnectorIncomingNative hpL hwL
  let H := planarGradient Gin ∘ F
  have hF : Continuous F := visibleConnectorIncomingNative_continuous hp hw hpL hwL
  have hcenter (q : AddCircle L) : F (q, 0) ∈ U := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa only [F, visibleConnectorIncomingNative, zero_smul, add_zero,
      Periodic.lift_coe] using hpU r
  have hcenterG (q : AddCircle L) : H (q, 0) = hgammaL.lift q := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    change planarGradient Gin (hpL.lift (r : AddCircle L) + (0 : ℝ) •
      hwL.lift (r : AddCircle L)) = hgammaL.lift (r : AddCircle L)
    simp only [zero_smul, add_zero, Periodic.lift_coe]
    exact (congrFun hactual r).symm
  obtain ⟨a, ha, hiF, _⟩ := exists_thinBand_embedding hF
    (by simpa only [F, visibleConnectorIncomingNative, zero_smul, add_zero] using hip)
    (incomingNative_local_inj hp hw hpL hwL hdet)
  let K : Set (AddCircle L × ℝ) := (fun q : AddCircle L => (q, (0 : ℝ))) '' univ
  have hK : IsCompact K := isCompact_univ.image (continuous_id.prodMk continuous_const)
  have hiHK : InjOn H K := by
    rintro _ ⟨q, _, rfl⟩ _ ⟨r, _, rfl⟩ h
    exact congrArg (fun z : AddCircle L => (z, (0 : ℝ)))
      (higamma (by simpa only [hcenterG] using h))
  have hgrad := planarGradient_contDiffOn hGin hU
  have hcHK : ∀ z ∈ K, ContinuousAt H z := by
    rintro _ ⟨q, _, rfl⟩
    exact ((hgrad.continuousOn _ (hcenter q)).continuousAt
      (hU.mem_nhds (hcenter q))).comp hF.continuousAt
  have hlHK : ∀ z ∈ K, ∃ V ∈ 𝓝 z, InjOn H V := by
    rintro _ ⟨q, _, rfl⟩
    exact incomingNative_gradient_local_inj hp hw hpL hwL hU hGin hpU hneg hdet q
  obtain ⟨V, hV, hKV, hiHV⟩ := hiHK.exists_isOpen_superset hK hcHK hlHK
  obtain ⟨b, hb, hbV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hKU : K ⊆ F ⁻¹' U := by
    rintro _ ⟨q, _, rfl⟩
    exact hcenter q
  obtain ⟨c, hc, hcU⟩ := hK.exists_cthickening_subset_open (hU.preimage hF) hKU
  let delta := min a (min (b / 2) (c / 2))
  have hd : 0 < delta := lt_min ha (lt_min (half_pos hb) (half_pos hc))
  have hda : delta ≤ a := min_le_left _ _
  have hdb : delta ≤ b / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdc : delta ≤ c / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let S : Set (AddCircle L × ℝ) := univ ×ˢ Icc (-delta) delta
  have hthick (r : ℝ) (hr : 0 < r) (hdr : delta ≤ r / 2) :
      S ⊆ Metric.cthickening r K := by
    intro z hz
    apply Metric.thickening_subset_cthickening r K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(z.1, 0), ⟨z.1, mem_univ _, rfl⟩, ?_⟩
    rw [dist_prod_same_left, Real.dist_eq, sub_zero]
    exact ((abs_le.mpr hz.2).trans hdr).trans_lt (half_lt_self hr)
  have hSF : S ⊆ univ ×ˢ Icc (-a) a := by
    intro z hz
    exact ⟨hz.1, ⟨(neg_le_neg hda).trans hz.2.1, hz.2.2.trans hda⟩⟩
  have hiFS : InjOn F S := hiF.mono hSF
  have hiHS : InjOn H S := hiHV.mono ((hthick b hb hdb).trans hbV)
  have hSU : MapsTo F S U := (hthick c hc hdc).trans hcU
  have hS : IsCompact S := isCompact_univ.prod isCompact_Icc
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcontH : ContinuousOn H S := hgrad.continuousOn.comp hF.continuousOn hSU
  have hHrestr : Continuous (fun z : S => H z) :=
    continuousOn_iff_continuous_restrict.mp hcontH
  have hiFrestr : Injective (fun z : S => F z) := fun x y h =>
    Subtype.ext (hiFS x.property y.property h)
  have hiHrestr : Injective (fun z : S => H z) := fun x y h =>
    Subtype.ext (hiHS x.property y.property h)
  have heF := ((hF.comp continuous_subtype_val).isClosedEmbedding hiFrestr).isEmbedding
  have heH := (hHrestr.isClosedEmbedding hiHrestr).isEmbedding
  have hopen : (univ ×ˢ Ioo (-delta) delta : Set (AddCircle L × ℝ)) ⊆ S :=
    prod_mono Subset.rfl Ioo_subset_Icc_self
  refine ⟨delta, hd, hiFS, hiHS, hSU, ?_, ?_, ?_⟩
  · exact heF.comp (Topology.IsEmbedding.inclusion hopen)
  · exact heH.comp (Topology.IsEmbedding.inclusion hopen)
  · intro r
    exact visibleConnectorIncoming_exists_source_chart hp hw hU r (hpU r) (hdet r)

end
end TightVer401