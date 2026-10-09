import TightVer401.SeamNormalCoordinates
import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth
import Mathlib.Topology.Order.Compact

/-! Choose protection and radial cutoffs from the ordinary initial complex
homeomorphic disks and compact protected set. No protected neighborhood,
continued potential, or completed inverse is supplied as a premise. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped Topology

/-- Compactness makes pointwise positive actual radius uniformly positive and
bounded above. Empty protected sets are allowed. -/
theorem dualRadialCompletionProtected_radial_bounds {K : Set Coord}
    (hK : IsCompact K) (hKpositive : K ⊆ {p | 0 < planarRadius p}) :
    ∃ epsilon L : ℝ, 0 < epsilon ∧ epsilon < L ∧
      ∀ p ∈ K, epsilon < planarRadius p ∧ planarRadius p < L := by
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    simp [hEmpty]
  · obtain ⟨pMin, hpMin, hMin⟩ := hK.exists_isMinOn hNonempty
      quadraticFillerCartesianGradient_radius_continuous.continuousOn
    obtain ⟨pMax, hpMax, hMax⟩ := hK.exists_isMaxOn hNonempty
      quadraticFillerCartesianGradient_radius_continuous.continuousOn
    have hMinPositive : 0 < planarRadius pMin := hKpositive hpMin
    have hMinMax : planarRadius pMin ≤ planarRadius pMax :=
      (isMinOn_iff.mp hMin) pMax hpMax
    refine ⟨planarRadius pMin / 2, planarRadius pMax + 1,
      by positivity, by linarith, ?_⟩
    intro p hp
    have hLower := (isMinOn_iff.mp hMin) p hp
    have hUpper := (isMaxOn_iff.mp hMax) p hp
    constructor <;> linarith

/-- The original ordinary open annulus contains a usable open protected
neighborhood, with derived positive inner and finite outer radial cutoffs. -/
theorem exists_dualRadialCompletionProtected
    {HpPlus HpMinus : ℂ ≃ₜ ℂ} {e0 : OpenPartialHomeomorph Coord Coord} {K : Set Coord}
    (h0 : (0 : ℂ) ∈ HpMinus '' ball (0 : ℂ) 1)
    (hBand : seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source)
    (hK : IsCompact K)
    (hInside : K ⊆ seamComplexCoord '' ((HpPlus '' ball (0 : ℂ) 1) \
      closure (HpMinus '' ball (0 : ℂ) 1))) :
    ∃ epsilon L : ℝ, ∃ W : Set Coord,
      0 < epsilon ∧ epsilon < L ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ e0.source ∧
      W ⊆ {p | 0 < planarRadius p} ∧
      W ⊆ seamComplexCoord '' ((HpPlus '' ball (0 : ℂ) 1) \
        closure (HpMinus '' ball (0 : ℂ) 1)) ∧
      ∀ p ∈ W, epsilon < planarRadius p ∧ planarRadius p < L := by
  let U : Set Coord := seamComplexCoord '' ((HpPlus '' ball (0 : ℂ) 1) \
    closure (HpMinus '' ball (0 : ℂ) 1))
  have hPlusOpen : IsOpen (HpPlus '' ball (0 : ℂ) 1) :=
    HpPlus.isOpenMap _ isOpen_ball
  have hComplexBandOpen : IsOpen ((HpPlus '' ball (0 : ℂ) 1) \
      closure (HpMinus '' ball (0 : ℂ) 1)) :=
    hPlusOpen.sdiff isClosed_closure
  have hUopen : IsOpen U := seamComplexCoord.isOpenMap _ hComplexBandOpen
  have hUsource : U ⊆ e0.source := by
    rintro p ⟨z, hz, rfl⟩
    apply hBand
    refine ⟨z, ⟨subset_closure hz.1, ?_⟩, rfl⟩
    intro hzInner
    exact hz.2 (subset_closure hzInner)
  have hUpositive : U ⊆ {p | 0 < planarRadius p} := by
    rintro p ⟨z, hz, rfl⟩
    have hz0 : z ≠ 0 := by
      intro he
      apply hz.2
      rw [he]
      exact subset_closure h0
    have hr : planarRadius (seamComplexCoord z) = ‖z‖ := by
      rw [seamComplexCoord_apply]
      simp only [planarRadius, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.norm_def, Complex.normSq_apply, pow_two]
    change 0 < planarRadius (seamComplexCoord z)
    rw [hr]
    exact norm_pos_iff.mpr hz0
  have hKpositive : K ⊆ {p | 0 < planarRadius p} :=
    fun _ hp => hUpositive (hInside hp)
  obtain ⟨epsilon, L, hepsilon, hepsilonL, hBounds⟩ :=
    dualRadialCompletionProtected_radial_bounds hK hKpositive
  have hRadialOpen : IsOpen {p : Coord | epsilon < planarRadius p ∧ planarRadius p < L} :=
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
      (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)
  refine ⟨epsilon, L, U ∩ {p | epsilon < planarRadius p ∧ planarRadius p < L},
    hepsilon, hepsilonL, hUopen.inter hRadialOpen, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hInside hp, hBounds p hp⟩
  · intro p hp
    exact hUsource hp.1
  · intro p hp
    exact hUpositive hp.1
  · exact inter_subset_left
  · intro p hp
    exact hp.2

end
end TightVer401
