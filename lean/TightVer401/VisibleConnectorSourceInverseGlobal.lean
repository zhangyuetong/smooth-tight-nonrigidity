import TightVer401.AnnularDegree
import TightVer401.QuadraticRadialFillingDegreeData

/-! Actual source inverse from ordinary positive boundary loops and the
actual positive Jacobian. Degree supplies closed injectivity and image;
compact local inversion extends the SAME map across the entire closure. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem sourceInverse_round_eq (r : ℝ) (hr : 0 < r) :
    roundDiskChart r hr = quadraticRadialFillingRoundFilling r hr := by
  ext z
  change (r : ℂ) * z = r • z
  rw [Complex.real_smul]

theorem visibleConnectorSourceInverse_round_open {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    annularCoordJordanInterior (roundDiskChart R hR) (roundDiskChart r hr) =
      {p : Coord | r < planarRadius p ∧ planarRadius p < R} := by
  unfold annularCoordJordanInterior annularJordanInterior
  rw [sourceInverse_round_eq R hR, sourceInverse_round_eq r hr]
  exact quadraticRadialFillingRoundAnnulus_open_coord hr hR

theorem visibleConnectorSourceInverse_round_closed {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    annularCoordJordanClosure (roundDiskChart R hR) (roundDiskChart r hr) =
      {p : Coord | r ≤ planarRadius p ∧ planarRadius p ≤ R} := by
  unfold annularCoordJordanClosure annularJordanClosure
  rw [sourceInverse_round_eq R hR, sourceInverse_round_eq r hr]
  change seamComplexCoord '' (closure
    (quadraticRadialFillingRoundFilling R hR '' Metric.ball (0 : ℂ) 1) \
      (quadraticRadialFillingRoundFilling r hr '' Metric.ball (0 : ℂ) 1)) = _
  rw [quadraticRadialFillingRoundFilling_closure_ball]
  exact quadraticRadialFillingRoundAnnulus_closed_coord hr hR

private theorem sourceInverse_round_nested {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    closure (jordanInterior (roundDiskChart r hr)) ⊆
      jordanInterior (roundDiskChart R hR) := by
  rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball _ hr.ne']
  exact closedBall_subset_ball hrR

private theorem sourceInverse_boundary_representative {Hs : ℂ ≃ₜ ℂ}
    {gamma : ℝ → ℂ} (hgamma : RegularJordanParametrization Hs gamma)
    {z : ℂ} (hz : z ∈ frontier (jordanInterior Hs)) :
    ∃ t ∈ Ico (0 : ℝ) 1, gamma t = z := by
  obtain ⟨t, ht, htz⟩ := hgamma.boundary.symm ▸ hz
  by_cases ht1 : t < 1
  · exact ⟨t, ⟨ht.1, ht1⟩, htz⟩
  have htEq : t = 1 := le_antisymm ht.2 (le_of_not_gt ht1)
  refine ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
  have hp : gamma 1 = gamma 0 := by simpa only [zero_add] using hgamma.periodic 0
  exact hp.symm.trans (htEq ▸ htz)

private theorem sourceInverse_boundary_homeomorph {f : ℂ → ℂ}
    {Hs Ht : ℂ ≃ₜ ℂ} {gamma eta : ℝ → ℂ}
    (hgamma : RegularJordanParametrization Hs gamma)
    (heta : RegularJordanParametrization Ht eta)
    (hf : ContinuousOn f (frontier (jordanInterior Hs)))
    (hTrace : ∀ t, f (gamma t) = eta t) :
    ∃ B : frontier (jordanInterior Hs) ≃ₜ frontier (jordanInterior Ht),
      ∀ z, (B z : ℂ) = f z := by
  have hMaps : MapsTo f (frontier (jordanInterior Hs))
      (frontier (jordanInterior Ht)) := by
    intro z hz
    obtain ⟨t, _, htz⟩ := sourceInverse_boundary_representative hgamma hz
    rw [← htz, hTrace]
    exact heta.mem_frontier t
  have hInj : InjOn f (frontier (jordanInterior Hs)) := by
    intro z hz w hw he
    obtain ⟨t, ht, htz⟩ := sourceInverse_boundary_representative hgamma hz
    obtain ⟨s, hs, hsw⟩ := sourceInverse_boundary_representative hgamma hw
    have he' : eta t = eta s := by rw [← hTrace, ← hTrace, htz, hsw]; exact he
    exact htz.symm.trans ((congrArg gamma (heta.injective ht hs he')).trans hsw)
  have hSurj : SurjOn f (frontier (jordanInterior Hs))
      (frontier (jordanInterior Ht)) := by
    intro y hy
    obtain ⟨t, _, hty⟩ := heta.boundary.symm ▸ hy
    exact ⟨gamma t, hgamma.mem_frontier t, (hTrace t).trans hty⟩
  let g : frontier (jordanInterior Hs) → frontier (jordanInterior Ht) :=
    fun z => ⟨f z, hMaps z.property⟩
  have hg : Bijective g := by
    constructor
    · intro z w he
      exact Subtype.ext (hInj z.property w.property (congrArg Subtype.val he))
    · intro y
      obtain ⟨z, hz, hzy⟩ := hSurj y.property
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  let B := Equiv.ofBijective g hg
  have hB : Continuous B := hf.domRestrict.subtype_mk _
  let : CompactSpace (frontier (jordanInterior Hs)) :=
    isCompact_iff_compactSpace.mp (annular_jordan_frontier_isCompact Hs)
  exact ⟨hB.homeoOfEquivCompactToT2, fun _ => rfl⟩

private theorem sourceInverse_winding {f : ℂ → ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    {gamma eta : ℝ → ℂ} (hgamma : ContDiff ℝ ∞ gamma)
    (hgammaO : ∀ t, gamma t ∈ O) {H : ℂ ≃ₜ ℂ}
    (heta : PositiveJordanParametrization H eta) (hTrace : ∀ t, f (gamma t) = eta t) :
    planarFormIntegral (annularAngularFormP f (H 0))
      (annularAngularFormQ f (H 0)) gamma = 1 := by
  have hCenter : H 0 ∈ jordanInterior H := ⟨0, mem_ball_self zero_lt_one, rfl⟩
  have hAvoid : ∀ t, f (gamma t) ≠ H 0 := by
    intro t he
    rw [hTrace] at he
    have ht := heta.toRegular.mem_frontier t
    rw [frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 (he.symm ▸ hCenter)
  obtain ⟨u, hu, hturn⟩ := heta.positive (H 0) hCenter
  rw [annularAngularForm_integral_eq_pathIncrement hO hf hgamma hgammaO (H 0) hAvoid]
  unfold pathArgumentIncrement
  rw [circlePathIncrement_eq_lift _ u (fun t => by
    change (u t : UnitAddCircle) = normalizedArgument (f (gamma t) - H 0)
    rw [hTrace]
    exact hu t), hturn]
  ring

/-- Actual ordinary positive boundary data construct both the exact closed
annulus homeomorphism and an open inverse collar. The collar Jacobian stays
positive on its whole source, rather than merely on the closed annulus. -/
theorem visibleConnectorSourceInverse_global
    {F : Coord → Coord} {O : Set Coord} {Ho Hi : ℂ ≃ₜ ℂ}
    {etaOuter etaInner : ℝ → ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆ O)
    (hJ : ∀ p : Coord, 1 ≤ planarRadius p → planarRadius p ≤ 2 →
      0 < annularJacobian F p)
    (hOuter : PositiveJordanParametrization Ho etaOuter)
    (hInner : PositiveJordanParametrization Hi etaInner)
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hTraceOuter : ∀ t, annularComplexConjugate F (unitCircleParam 0 2 t) = etaOuter t)
    (hTraceInner : ∀ t, annularComplexConjugate F (unitCircleParam 0 1 t) = etaInner t) :
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi),
      e0.source = {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧ (e0 : Coord → Coord) = F ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ p, (H p : Coord) = F p) ∧
      F '' {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} =
        annularCoordJordanClosure Ho Hi ∧
      {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆ E.source ∧
      E.source ⊆ O ∧ ContDiffOn ℝ ∞ F E.source ∧
      (∀ p ∈ E.source, 0 < annularJacobian F p) ∧
      (E : Coord → Coord) = F ∧ ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) := by
  let K : Set Coord := {p | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2}
  let R2 := roundDiskChart 2 (by norm_num)
  let R1 := roundDiskChart 1 zero_lt_one
  have hOpen : annularCoordJordanInterior R2 R1 =
      {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} :=
    visibleConnectorSourceInverse_round_open zero_lt_one (by norm_num)
  have hClosed : annularCoordJordanClosure R2 R1 = K :=
    visibleConnectorSourceInverse_round_closed zero_lt_one (by norm_num)
  have hSourceNested : closure (jordanInterior R1) ⊆ jordanInterior R2 :=
    sourceInverse_round_nested zero_lt_one (by norm_num) (by norm_num)
  have hRoundOuter := quadraticRadialFillingDegree_positive_round 2 (by norm_num)
  have hRoundInner := quadraticRadialFillingDegree_positive_round 1 zero_lt_one
  let Oc : Set ℂ := seamComplexCoord ⁻¹' O
  have hOc : IsOpen Oc := hO.preimage seamComplexCoord.continuous
  have hFc : ContDiffOn ℝ ∞ (annularComplexConjugate F) Oc :=
    seamComplexCoord.symm.contDiff.comp_contDiffOn
      (hF.comp seamComplexCoord.contDiff.contDiffOn (fun _ hz => hz))
  have hBoundaryO : frontier (jordanInterior R2) ∪ frontier (jordanInterior R1) ⊆ Oc := by
    intro z hz
    apply hKO
    change seamComplexCoord z ∈ K
    rw [← hClosed]
    exact mem_image_of_mem seamComplexCoord
      (annular_jordan_boundary_subset_closure hSourceNested hz)
  obtain ⟨Bo, hBo⟩ := sourceInverse_boundary_homeomorph hRoundOuter.toRegular hOuter.toRegular
    (hFc.continuousOn.mono (fun _ hz => hBoundaryO (Or.inl hz))) hTraceOuter
  obtain ⟨Bi, hBi⟩ := sourceInverse_boundary_homeomorph hRoundInner.toRegular hInner.toRegular
    (hFc.continuousOn.mono (fun _ hz => hBoundaryO (Or.inr hz))) hTraceInner
  have hOuterW := sourceInverse_winding hOc hFc hRoundOuter.smooth
    (fun t => hBoundaryO (Or.inl (hRoundOuter.toRegular.mem_frontier t))) hOuter hTraceOuter
  have hInnerW := sourceInverse_winding hOc hFc hRoundInner.smooth
    (fun t => hBoundaryO (Or.inr (hRoundInner.toRegular.mem_frontier t))) hInner hTraceInner
  obtain ⟨e0, he0S, he0T, he0F, he0I, H0, hH0⟩ :=
    annular_degree_global_diffeomorphism R2 R1 Ho Hi (unitCircleParam 0 2)
      (unitCircleParam 0 1) hRoundOuter hRoundInner hSourceNested hNested F O hO hF
      (fun p hp => by
        apply hKO
        change p ∈ K
        rw [← hClosed]
        exact hp) 1 (Or.inl rfl)
      (fun p hp => by
        have hpRound : 1 < planarRadius p ∧ planarRadius p < 2 := by
          rw [hOpen] at hp
          exact hp
        have hpK : p ∈ K := ⟨hpRound.1.le, hpRound.2.le⟩
        simpa only [Int.cast_one, one_mul] using hJ p hpK.1 hpK.2)
      false Bo Bi hBo hBi 1 (by norm_num) hOuterW hInnerW
  let H : K ≃ₜ annularCoordJordanClosure Ho Hi :=
    (Homeomorph.setCongr hClosed.symm).trans H0
  have hH : ∀ p : K, (H p : Coord) = F p := fun p => hH0 _
  have hImage : F '' K = annularCoordJordanClosure Ho Hi := by
    apply Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      rw [← hH ⟨p, hp⟩]
      exact (H ⟨p, hp⟩).property
    · intro y hy
      obtain ⟨p, hp⟩ := H.surjective ⟨y, hy⟩
      exact ⟨p, p.property, (hH p).symm.trans (congrArg Subtype.val hp)⟩
  have hInj : InjOn F K := by
    intro p hp q hq he
    have he' : H ⟨p, hp⟩ = H ⟨q, hq⟩ :=
      Subtype.ext ((hH ⟨p, hp⟩).trans (he.trans (hH ⟨q, hq⟩).symm))
    exact congrArg Subtype.val (H.injective he')
  have hJac : ContinuousOn (annularJacobian F) O := by
    exact ContinuousLinearMap.continuous_det.comp_continuousOn
      (hF.continuousOn_fderiv_of_isOpen hO (by simp))
  let V := O ∩ (annularJacobian F) ⁻¹' Ioi (0 : ℝ)
  have hV : IsOpen V := hJac.isOpen_inter_preimage hO isOpen_Ioi
  have hKV : K ⊆ V := fun p hp => ⟨hKO hp, hJ p hp.1 hp.2⟩
  have hFV := hF.mono (show V ⊆ O from inter_subset_left)
  have hJV : ∀ p ∈ V, annularJacobian F p ≠ 0 := fun _ hp => hp.2.ne'
  have hCont : ∀ p ∈ K, ContinuousAt F p :=
    fun _ hp => hF.continuousOn.continuousAt (hO.mem_nhds (hKO hp))
  have hLocal : ∀ p ∈ K, ∃ W ∈ 𝓝 p, InjOn F W := by
    intro p hp
    obtain ⟨E, hEp, _hEV, hEf, _hEi⟩ := annular_exists_smooth_local_inverse hV hFV hJV (hKV hp)
    refine ⟨E.source, E.open_source.mem_nhds hEp, ?_⟩
    rw [← hEf]
    exact E.injOn
  obtain ⟨W, hW, hKW, hIW⟩ := hInj.exists_isOpen_superset
    (quadraticRadialFilling_closedAnnulus_isCompact 1 2) hCont hLocal
  let Z := W ∩ V
  have hZ : IsOpen Z := hW.inter hV
  have hKZ : K ⊆ Z := fun p hp => ⟨hKW hp, hKV hp⟩
  have hZO : Z ⊆ O := fun _ hp => hp.2.1
  have hFZ := hF.mono hZO
  have hJZ : ∀ p ∈ Z, 0 < annularJacobian F p := fun _ hp => hp.2.2
  have hIZ : InjOn F Z := hIW.mono inter_subset_left
  have hUnique : ∀ y ∈ F '' Z, ∃! p, p ∈ Z ∧ F p = y := by
    rintro y ⟨p, hp, hpy⟩
    refine ⟨p, ⟨hp, hpy⟩, ?_⟩
    intro q hq
    exact hIZ hq.1 hp (hq.2.trans hpy.symm)
  obtain ⟨E, hES, _hET, hEF, hEI⟩ := annular_exists_smooth_image_inverse hZ hFZ
    (fun p hp => (hJZ p hp).ne') hUnique
  have hKE : K ⊆ E.source := by simpa only [hES] using hKZ
  have hOldSource : ∀ y ∈ annularCoordJordanInterior Ho Hi, e0.symm y ∈ K := by
    intro y hy
    have hp := e0.map_target (he0T.symm ▸ hy)
    rw [he0S] at hp
    have hpRound : 1 < planarRadius (e0.symm y) ∧ planarRadius (e0.symm y) < 2 := by
      rw [hOpen] at hp
      exact hp
    exact ⟨hpRound.1.le, hpRound.2.le⟩
  have hForward : ∀ y ∈ annularCoordJordanInterior Ho Hi, E (e0.symm y) = y := by
    intro y hy
    rw [hEF, ← he0F]
    exact e0.right_inv (he0T.symm ▸ hy)
  refine ⟨e0, E, H, he0S.trans hOpen, he0T, he0F, he0I, hH, hImage,
    hKE, ?_, ?_, ?_, hEF, hEI, ?_, ?_⟩
  · simpa only [hES] using hZO
  · simpa only [hES] using hFZ
  · simpa only [hES] using hJZ
  · intro y hy
    obtain ⟨p, hp, hpy⟩ := hImage.symm ▸ hy
    rw [← hpy, ← hEF]
    exact E.map_source (hKE hp)
  · intro y hy
    calc
      E.symm y = E.symm (E (e0.symm y)) := congrArg E.symm (hForward y hy).symm
      _ = e0.symm y := E.left_inv (hKE (hOldSource y hy))

end
end TightVer401
