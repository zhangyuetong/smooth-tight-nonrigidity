import TightVer401.PositiveExitConstructionProtectedLeaves
import Mathlib.Topology.Order.Lattice

/-! Uniform protected-core label margins for the SAME selected source geometry.
This constructs a quantitative gap and an actual open agreement neighborhood.
Jordan enclosure and orientation of the selected graphs remain separate work. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Strict labels on a compact core leave one uniform positive margin on both
sides. The actual open label band is contained in the original source target. -/
theorem positiveExit_selectedSourceGeometry_core_uniform_gap
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    {C : Set Coord} (hC : IsCompact C) (hne : C.Nonempty)
    (hCT : C ⊆ e.target) {lo hi : ℝ}
    (hgap : ∀ p ∈ C, lo < positiveExitCartesianLabel d hb e p ∧
      positiveExitCartesianLabel d hb e p < hi) :
    ∃ ε > 0, ∃ W : Set Coord, IsOpen W ∧ C ⊆ W ∧ W ⊆ e.target ∧
      ∀ p ∈ W, lo + ε < positiveExitCartesianLabel d hb e p ∧
        positiveExitCartesianLabel d hb e p < hi - ε := by
  let A := positiveExitCartesianLabel d hb e
  have hA : ContinuousOn A C :=
    (positiveExitCartesianLabel_contDiffOn d hb e heI).continuousOn.mono hCT
  let f := fun p => min (A p - lo) (hi - A p)
  have hf : ContinuousOn f C := (hA.sub continuousOn_const).inf (continuousOn_const.sub hA)
  obtain ⟨p0, hp0, hmin⟩ := hC.exists_isMinOn hne hf
  have hpos : 0 < f p0 := by
    exact lt_min (sub_pos.mpr (hgap p0 hp0).1) (sub_pos.mpr (hgap p0 hp0).2)
  let ε := f p0 / 2
  have hε : 0 < ε := half_pos hpos
  let W := e.target ∩ {p | lo + ε < A p ∧ A p < hi - ε}
  have hW : IsOpen W := by
    have hcont := (positiveExitCartesianLabel_contDiffOn d hb e heI).continuousOn
    have h1 : IsOpen (e.target ∩ {p | lo + ε < A p}) :=
      isOpen_iff_mem_nhds.mpr (fun p hp =>
        inter_mem (e.open_target.mem_nhds hp.1)
          ((hcont.continuousAt (e.open_target.mem_nhds hp.1)).preimage_mem_nhds
            (Ioi_mem_nhds hp.2)))
    have h2 : IsOpen (e.target ∩ {p | A p < hi - ε}) :=
      isOpen_iff_mem_nhds.mpr (fun p hp =>
        inter_mem (e.open_target.mem_nhds hp.1)
          ((hcont.continuousAt (e.open_target.mem_nhds hp.1)).preimage_mem_nhds
            (Iio_mem_nhds hp.2)))
    convert h1.inter h2 using 1 <;> ext p <;> simp [W, and_assoc, and_left_comm]
  refine ⟨ε, hε, W, hW, ?_, inter_subset_left, fun p hp => hp.2⟩
  intro p hp
  have hm : f p0 ≤ f p := hmin hp
  have hl : f p ≤ A p - lo := min_le_left _ _
  have hh : f p ≤ hi - A p := min_le_right _ _
  refine ⟨hCT hp, ?_, ?_⟩ <;> dsimp [ε] <;> linarith

/-- Produce the actual ordered leaves and a uniform open protected band from
ordinary compact containment in the SAME complete identity-flow image. -/
theorem positiveExit_selectedSourceGeometry_exists_uniform_core_band
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hδ : 0 < δ) {C : Set Coord} (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside)) :
    ∃ vin vout : Ioo (0 : ℝ) δ, (vin : ℝ) < (vout : ℝ) ∧
      ∃ ε > 0, ∃ W : Set Coord, IsOpen W ∧ C ⊆ W ∧ W ⊆ e.target ∧
        ∀ p ∈ W,
          1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 + ε <
            positiveExitCartesianLabel d hb e p ∧
          positiveExitCartesianLabel d hb e p <
            1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0 - ε := by
  obtain ⟨vin, vout, horder, hgap, _⟩ :=
    positiveExit_exists_two_protected_complete_leaves d hb e hinside heS heF heI
      hδ hC hne hprotect
  have hCT : C ⊆ e.target := by
    rintro p hp
    obtain ⟨q, _, rfl⟩ := hprotect hp
    exact e.map_source (by rw [heS]; exact mem_univ q)
  obtain ⟨ε, hε, W, hW, hCW, hWT, hbound⟩ :=
    positiveExit_selectedSourceGeometry_core_uniform_gap d hb e heI hC hne hCT hgap
  exact ⟨vin, vout, horder, ε, hε, W, hW, hCW, hWT, hbound⟩
/-- Retain the actual open agreement region of the selected patch constructor
and intersect it with the quantitative label band. No new potential is chosen. -/
theorem positiveExit_selectedSourceGeometry_protected_agreement
    {G Ge : Coord → ℝ} {C W A1 A2 : Set Coord}
    (hW : IsOpen W) (hCW : C ⊆ W)
    (hOpen : IsOpen (A1 ∪ A2)ᶜ) (hProtected : C ⊆ (A1 ∪ A2)ᶜ)
    (hEq : EqOn Ge G (A1 ∪ A2)ᶜ) :
    ∃ O : Set Coord, IsOpen O ∧ C ⊆ O ∧ O ⊆ W ∧ EqOn Ge G O ∧
      ∀ p ∈ C, Ge =ᶠ[𝓝 p] G := by
  let O := W ∩ (A1 ∪ A2)ᶜ
  have hO : IsOpen O := hW.inter hOpen
  have hCO : C ⊆ O := fun p hp => ⟨hCW hp, hProtected hp⟩
  have hEO : EqOn Ge G O := fun p hp => hEq hp.2
  exact ⟨O, hO, hCO, inter_subset_left, hEO,
    fun p hp => hEO.eventuallyEq_of_mem (hO.mem_nhds (hCO hp))⟩

end
end TightVer401





