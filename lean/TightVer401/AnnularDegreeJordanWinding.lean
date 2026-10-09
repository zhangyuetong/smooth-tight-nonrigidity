import TightVer401.AnnularDegreeBoundaryWinding
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Normed.Group.Uniform

/-!
Ordinary one-point winding data for actual image Jordan loops. Image loops
need only be continuous and closed for the topological argument: no image
boundary differential rank or regular parametrization is required.

The exterior lifting proof adapts TightVer401.CircleDiskWinding.
winding_origin_inside to the actual UnitAddCircle cover used by the pinned
OpenAI CircleLifts foundation (adc7f1241b42e322a6451854ab7e4b4c146bf78a).
Interior constancy uses the proved NormalizedArgument continuous moving-point
increment and integer loop increment, not a degree or preimage-count input.
-/
namespace TightVer401
noncomputable section
open Set Function Filter Metric
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff

/-- Restriction of an actual continuous loop to the parameter interval. -/
def annularLoopPath (η : ℝ → ℂ) (hη : Continuous η) : C(unitInterval, ℂ) :=
  ⟨fun t => η t, hη.comp continuous_subtype_val⟩

/-- The actual moving-point argument increment on any avoiding set. -/
def annularLoopIncrementOn (η : ℝ → ℂ) (hη : Continuous η)
    (U : Set ℂ) (hAvoid : ∀ y ∈ U, ∀ t, η t ≠ y) (y : U) : ℝ :=
  pathArgumentIncrement ⟨(annularLoopPath η hη, y), by
    rintro ⟨t, ht⟩
    exact hAvoid y y.property t ht⟩

theorem annularLoopIncrementOn_continuous (η : ℝ → ℂ) (hη : Continuous η)
    (U : Set ℂ) (hAvoid : ∀ y ∈ U, ∀ t, η t ≠ y) :
    Continuous (annularLoopIncrementOn η hη U hAvoid) := by
  apply continuous_pathArgumentIncrement.comp
  exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- A continuous integer-valued argument increment is constant on each
preconnected avoiding set. -/
theorem annularLoopIncrementOn_eq (η : ℝ → ℂ) (hη : Continuous η)
    (hClosed : η 1 = η 0) (U : Set ℂ) (hU : IsPreconnected U)
    (hAvoid : ∀ y ∈ U, ∀ t, η t ≠ y) (y z : U) :
    annularLoopIncrementOn η hη U hAvoid y =
      annularLoopIncrementOn η hη U hAvoid z := by
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hMaps : MapsTo (annularLoopIncrementOn η hη U hAvoid) univ
      (range ((↑) : ℤ → ℝ)) := by
    intro p _
    obtain ⟨n, hn⟩ := pathArgumentIncrement_integer_of_closed
      (⟨(annularLoopPath η hη, p), by
        rintro ⟨t, ht⟩
        exact hAvoid p p.property t ht⟩ : AvoidingPathPoint) hClosed
    exact ⟨n, hn.symm⟩
  exact isPreconnected_univ.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
    (annularLoopIncrementOn_continuous η hη U hAvoid).continuousOn
    hMaps (mem_univ y) (mem_univ z)

/-- Exterior targets admit one continuous real argument branch on a larger
Jordan disk containing the whole loop, so every actual lift has zero turn. -/
theorem annular_jordan_loop_lift_increment_zero
    {H : ℂ ≃ₜ ℂ} {η : ℝ → ℂ} (hη : Continuous η)
    (hboundary : range η ⊆ frontier (jordanInterior H))
    (hClosed : η 1 = η 0) {y : ℂ} (hy : y ∉ closure (jordanInterior H))
    (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = normalizedArgument (η t - y)) :
    v 1 - v 0 = 0 := by
  classical
  have hgt : 1 < ‖H.symm y‖ := by
    by_contra h
    apply hy
    rw [closure_jordanInterior]
    exact ⟨H.symm y, by simpa only [mem_closedBall, dist_zero_right] using le_of_not_gt h,
      H.apply_symm_apply y⟩
  let r := (‖H.symm y‖ + 1) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrn : r < ‖H.symm y‖ := by dsimp [r]; linarith
  let U : Set ℂ := H '' ball (0 : ℂ) r
  have hU : IsOpen U := H.isOpenMap _ isOpen_ball
  have hUy : ∀ z ∈ U, z ≠ y := by
    rintro z ⟨w, hw, rfl⟩ he
    have hew : w = H.symm y := by simpa using congrArg H.symm he
    have hw' : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
    rw [hew] at hw'
    exact (not_lt_of_ge hrn.le) hw'
  have hηU : ∀ t, η t ∈ U := by
    intro t
    have ht := hboundary (mem_range_self t)
    rw [frontier_jordanInterior] at ht
    obtain ⟨z, hz, he⟩ := ht
    refine ⟨z, ?_, he⟩
    simp only [mem_ball, dist_zero_right, mem_sphere] at hz ⊢
    simpa only [hz] using hr
  letI : ContractibleSpace (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (nonempty_ball.mpr (by linarith))
  letI : SimplyConnectedSpace U := H.isSimplyConnected_image.mpr
    (show SimplyConnectedSpace (ball (0 : ℂ) r) from inferInstance)
  letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  have harg : ContinuousOn (fun z => normalizedArgument (z - y)) U := by
    intro z hz
    exact ((continuousAt_normalizedArgument (sub_ne_zero.mpr (hUy z hz))).comp
      (f := fun w : ℂ => w - y)
      (continuous_id.sub continuous_const).continuousAt).continuousWithinAt
  obtain ⟨u, hu, _, huproj⟩ := exists_continuous_circle_lift
    (fun z => normalizedArgument (z - y)) harg (hηU 0) (v 0) (hproj 0)
  let uI : C(unitInterval, ℝ) :=
    ⟨fun t => u (η t), (hu.comp_continuous hη hηU).comp continuous_subtype_val⟩
  let vI : C(unitInterval, ℝ) := ⟨fun t => v t, hv.comp continuous_subtype_val⟩
  have heq := real_lift_path_increment_eq uI vI
    (fun t => (huproj (η t) (hηU t)).trans (hproj t).symm)
  change u (η 1) - u (η 0) = v 1 - v 0 at heq
  rw [hClosed, sub_self] at heq
  exact heq.symm

/-- Actual image-loop continuity, without a boundary derivative condition. -/
theorem annular_image_loop_continuous
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O) :
    Continuous (F ∘ γ) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hF.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp hγ.continuous.continuousAt)

/-- Identification of the actual angular pullback integral with the
continuous moving-point path increment. -/
theorem annularAngularForm_integral_eq_pathIncrement
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (y : ℂ) (hAvoid : ∀ t, F (γ t) ≠ y) :
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ =
      pathArgumentIncrement
        ⟨(annularLoopPath (F ∘ γ) (annular_image_loop_continuous hO hF hγ hγO), y), by
          rintro ⟨t, ht⟩
          exact hAvoid t ht⟩ := by
  let A : Set ℂ := O ∩ {z | F z ≠ y}
  have hA : IsOpen A := hF.continuousOn.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  have hFA : ContDiffOn ℝ ∞ F A := hF.mono inter_subset_left
  have hγA : ∀ t, γ t ∈ A := fun t => ⟨hγO t, hAvoid t⟩
  obtain ⟨v, hv, hproj, hint⟩ := annularAngularForm_exists_smooth_lift
    hA hFA (fun _ hz => hz.2) hγ hγA
  rw [hint]
  symm
  unfold pathArgumentIncrement
  exact circlePathIncrement_eq_lift _
    ⟨fun t => v t, hv.continuous.comp continuous_subtype_val⟩ (fun t => hproj t)

/-- Ordinary winding vanishes at every point exterior to the actual target
disk, including image loops with degenerate derivatives. -/
theorem annularAngularForm_integral_zero_exterior
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (hClosed : γ 1 = γ 0) (H : ℂ ≃ₜ ℂ)
    (hboundary : range (F ∘ γ) ⊆ frontier (jordanInterior H))
    (y : ℂ) (hy : y ∉ closure (jordanInterior H)) :
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ = 0 := by
  have hAvoid : ∀ t, F (γ t) ≠ y := by
    intro t he
    exact hy (he ▸ frontier_subset_closure (hboundary (mem_range_self t)))
  let A : Set ℂ := O ∩ {z | F z ≠ y}
  have hA : IsOpen A := hF.continuousOn.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  obtain ⟨v, hv, hproj, hint⟩ := annularAngularForm_exists_smooth_lift
    hA (hF.mono inter_subset_left) (fun _ hz => hz.2) hγ (fun t => ⟨hγO t, hAvoid t⟩)
  exact hint.trans (annular_jordan_loop_lift_increment_zero
    (annular_image_loop_continuous hO hF hγ hγO) hboundary
    (congrArg F hClosed) hy v hv.continuous hproj)

/-- Ordinary winding at one interior target determines winding throughout
its actual Jordan disk, by continuity and integer-valued loop increments. -/
theorem annularAngularForm_integral_eq_interior
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (hClosed : γ 1 = γ 0) (H : ℂ ≃ₜ ℂ)
    (hboundary : range (F ∘ γ) ⊆ frontier (jordanInterior H))
    (y z : ℂ) (hy : y ∈ jordanInterior H) (hz : z ∈ jordanInterior H) :
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ =
      planarFormIntegral (annularAngularFormP F z) (annularAngularFormQ F z) γ := by
  have hAvoid : ∀ p ∈ jordanInterior H, ∀ t, (F ∘ γ) t ≠ p := by
    intro p hp t he
    have ht := hboundary (mem_range_self t)
    rw [(jordanInterior_isOpen H).frontier_eq] at ht
    exact ht.2 (he.symm ▸ hp)
  rw [annularAngularForm_integral_eq_pathIncrement hO hF hγ hγO y (hAvoid y hy),
    annularAngularForm_integral_eq_pathIncrement hO hF hγ hγO z (hAvoid z hz)]
  exact annularLoopIncrementOn_eq (F ∘ γ) (annular_image_loop_continuous hO hF hγ hγO)
    (congrArg F hClosed) (jordanInterior H) (isConnected_jordanInterior H).isPreconnected
    hAvoid ⟨y, hy⟩ ⟨z, hz⟩

/-- The full ordinary target profile follows from one actual interior
winding value and the actual Jordan image, without a count identity. -/
theorem annularAngularForm_integral_profile
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (hClosed : γ 1 = γ 0) (H : ℂ ≃ₜ ℂ)
    (hboundary : range (F ∘ γ) = frontier (jordanInterior H))
    (z : ℂ) (hz : z ∈ jordanInterior H) (w : ℝ)
    (hw : planarFormIntegral (annularAngularFormP F z) (annularAngularFormQ F z) γ = w) :
    (∀ y ∈ jordanInterior H,
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ = w) ∧
    (∀ y ∉ closure (jordanInterior H),
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ = 0) := by
  constructor
  · intro y hy
    exact (annularAngularForm_integral_eq_interior hO hF hγ hγO hClosed H
      hboundary.subset y z hy hz).trans hw
  · intro y hy
    exact annularAngularForm_integral_zero_exterior hO hF hγ hγO hClosed H hboundary.subset y hy

/-- For target-ordered Jordan image loops, one ordinary winding value per
component gives the induced annular zero/unit profile. The two ordinary disk
windings agree; subtracting the inner contour gives opposite induced signs. -/
theorem annular_boundary_winding_profile_of_one_point
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γouter γinner : ℝ → ℂ}
    (houter : ContDiff ℝ ∞ γouter) (hinner : ContDiff ℝ ∞ γinner)
    (houterO : ∀ t, γouter t ∈ O) (hinnerO : ∀ t, γinner t ∈ O)
    (hClosedOuter : γouter 1 = γouter 0) (hClosedInner : γinner 1 = γinner 0)
    (Houter Hinner : ℂ ≃ₜ ℂ)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter)
    (himageOuter : range (F ∘ γouter) = frontier (jordanInterior Houter))
    (himageInner : range (F ∘ γinner) = frontier (jordanInterior Hinner))
    (w : ℝ) (hwAbs : |w| = 1)
    (hwOuter : planarFormIntegral (annularAngularFormP F (Houter 0))
      (annularAngularFormQ F (Houter 0)) γouter = w)
    (hwInner : planarFormIntegral (annularAngularFormP F (Hinner 0))
      (annularAngularFormQ F (Hinner 0)) γinner = w) :
    (∀ y ∈ annularJordanForbidden Houter Hinner,
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
        planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner = 0) ∧
    (∀ y ∈ annularJordanInterior Houter Hinner,
      |planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
        planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner| = 1) := by
  have hcenterOuter : Houter 0 ∈ jordanInterior Houter :=
    ⟨0, mem_ball_self zero_lt_one, rfl⟩
  have hcenterInner : Hinner 0 ∈ jordanInterior Hinner :=
    ⟨0, mem_ball_self zero_lt_one, rfl⟩
  obtain ⟨hOuterIn, hOuterOut⟩ := annularAngularForm_integral_profile
    hO hF houter houterO hClosedOuter Houter himageOuter (Houter 0) hcenterOuter w hwOuter
  obtain ⟨hInnerIn, hInnerOut⟩ := annularAngularForm_integral_profile
    hO hF hinner hinnerO hClosedInner Hinner himageInner (Hinner 0) hcenterInner w hwInner
  constructor
  · intro y hy
    rcases hy with hy | hy
    · rw [hOuterIn y (hnested (subset_closure hy)), hInnerIn y hy, sub_self]
    · have hyInner : y ∉ closure (jordanInterior Hinner) :=
        fun hi => hy (subset_closure (hnested hi))
      rw [hOuterOut y hy, hInnerOut y hyInner, sub_self]
  · intro y hy
    rw [hOuterIn y hy.1, hInnerOut y hy.2, sub_zero]
    exact hwAbs

end
end TightVer401
