import TightVer401.PositiveExitConstructionLabel
import Mathlib.Topology.Order.Compact

/-! Fixed-core application: two actual complete leaves of the SAME identity
band surround the labels of a prescribed compact Cartesian core. Their
Cartesian and spherical source disjointness follows from actual label
constancy, rather than being supplied as a collar or leaf package. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
  (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
  (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
  (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
    principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)

/-- The actual Cartesian leaf has precisely its actual initial-value label. -/
theorem positiveExitCartesianLabel_complete_leaf (heS : e.source = univ)
    (v : Ioo (0 : ℝ) δ) (q : AddCircle T) :
    positiveExitCartesianLabel d hb e (e (positiveExitLeaf d hb hinside v q)) =
      1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0 := by
  change positiveExitLevel d hb (e.symm (e (positiveExitLeaf d hb hinside v q))) = _
  rw [e.left_inv (by rw [heS]; exact mem_univ _)]
  exact positiveExitLevel_identityFlowBandInclusion d hb hinside (q, v)

/-- The actual sphere leaf and actual Cartesian source are the same Gauss
source expressed in the retained northern coordinates. -/
theorem positiveExitGaussLeaf_cartesian_source
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (v : Ioo (0 : ℝ) δ) (q : AddCircle T) :
    gnomonicInverse (positiveExitGaussLeaf d hb hinside v q).val =
      e (positiveExitLeaf d hb hinside v q) := (heF _).symm

/-- Consumer of the fixed-core construction. Ordinary compact core input
and actual complete-flow containment construct ordered actual initial values,
strict protected label bounds and actual Cartesian/spherical disjointness.
No selected-leaf or desired-disjointness witness is an input. -/
theorem positiveExit_exists_two_protected_complete_leaves
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hδ : 0 < δ) {C : Set Coord} (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside)) :
    ∃ vin vout : Ioo (0 : ℝ) δ,
      (vin : ℝ) < (vout : ℝ) ∧
      (∀ p ∈ C,
        1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
          positiveExitCartesianLabel d hb e p ∧
        positiveExitCartesianLabel d hb e p <
          1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) ∧
      Disjoint (range (e ∘ positiveExitLeaf d hb hinside vin)) C ∧
      Disjoint (range (e ∘ positiveExitLeaf d hb hinside vout)) C ∧
      Disjoint (range (e ∘ positiveExitLeaf d hb hinside vin))
        (range (e ∘ positiveExitLeaf d hb hinside vout)) ∧
      Disjoint (range (positiveExitGaussLeaf d hb hinside vin)) (gnomonicPoint '' C) ∧
      Disjoint (range (positiveExitGaussLeaf d hb hinside vout)) (gnomonicPoint '' C) ∧
      Disjoint (range (positiveExitGaussLeaf d hb hinside vin))
        (range (positiveExitGaussLeaf d hb hinside vout)) := by
  let A := positiveExitCartesianLabel d hb e
  let cb := positiveExitCompleteLower d δ
  have hCT : C ⊆ e.target := by
    intro p hp
    obtain ⟨z, _, rfl⟩ := hprotect hp
    exact e.map_source (by rw [heS]; exact mem_univ z)
  have hA : ContinuousOn A C :=
    (positiveExitCartesianLabel_contDiffOn d hb e heI).continuousOn.mono hCT
  have hbelow (p : Coord) (hp : p ∈ C) : cb < A p := by
    obtain ⟨z, hz, rfl⟩ := hprotect hp
    change cb < positiveExitLevel d hb (e.symm (e z))
    rw [e.left_inv (by rw [heS]; exact mem_univ z)]
    have hlabel : positiveExitLevel d hb z ∈ positiveExitLevel d hb ''
        range (identityFlowBandInclusion d hb 0 hinside) := ⟨z, hz, rfl⟩
    rw [positiveExitLevel_complete_image d hb hδ hinside] at hlabel
    exact hlabel
  obtain ⟨pmin, hpmin, hmin⟩ := hC.exists_isMinOn hne hA
  obtain ⟨pmax, hpmax, hmax⟩ := hC.exists_isMaxOn hne hA
  let low := cb + (A pmin - cb) / 2
  let high := A pmax + 1
  have hminlow : cb < A pmin := hbelow pmin hpmin
  have hminmax : A pmin ≤ A pmax := hmin hpmax
  have hlow : cb < low := by dsimp [low]; linarith
  have hlowhigh : low < high := by dsimp [low, high]; linarith
  have hhigh : cb < high := hlow.trans hlowhigh
  have hlowRange : low ∈ range (fun v : Ioo (0 : ℝ) δ =>
      1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0) := by
    rw [positiveExit_initialLevel_range d hδ]
    exact hlow
  have hhighRange : high ∈ range (fun v : Ioo (0 : ℝ) δ =>
      1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0) := by
    rw [positiveExit_initialLevel_range d hδ]
    exact hhigh
  obtain ⟨vout, hvout⟩ := hlowRange
  obtain ⟨vin, hvin⟩ := hhighRange
  change 1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 = low at hvout
  change 1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0 = high at hvin
  have horder : (vin : ℝ) < (vout : ℝ) := by
    by_contra hnot
    have hle : (vout : ℝ) ≤ (vin : ℝ) := le_of_not_gt hnot
    have hρ := ruledRho_pos (d.torsion_ne_zero 0)
    have hrecip := one_div_le_one_div_of_le (mul_pos hρ vout.property.1)
      (mul_le_mul_of_nonneg_left hle hρ.le)
    have hlabels := sub_le_sub_right hrecip (ruledOmega d.k d.τ 0)
    rw [hvin, hvout] at hlabels
    exact (not_le_of_gt hlowhigh) hlabels
  have hbounds : ∀ p ∈ C, low < A p ∧ A p < high := by
    intro p hp
    have hmn := hmin hp
    have hmx := hmax hp
    change A pmin ≤ A p at hmn
    change A p ≤ A pmax at hmx
    dsimp [low, high]
    constructor <;> linarith
  have hinLabel (q : AddCircle T) : A (e (positiveExitLeaf d hb hinside vin q)) = high :=
    (positiveExitCartesianLabel_complete_leaf d hb e hinside heS vin q).trans hvin
  have houtLabel (q : AddCircle T) : A (e (positiveExitLeaf d hb hinside vout q)) = low :=
    (positiveExitCartesianLabel_complete_leaf d hb e hinside heS vout q).trans hvout
  have hcartIn : Disjoint (range (e ∘ positiveExitLeaf d hb hinside vin)) C := by
    apply Set.disjoint_left.mpr
    rintro p ⟨q, rfl⟩ hp
    have hh := (hbounds _ hp).2
    change A (e (positiveExitLeaf d hb hinside vin q)) < high at hh
    rw [hinLabel] at hh
    exact lt_irrefl _ hh
  have hcartOut : Disjoint (range (e ∘ positiveExitLeaf d hb hinside vout)) C := by
    apply Set.disjoint_left.mpr
    rintro p ⟨q, rfl⟩ hp
    have hh := (hbounds _ hp).1
    change low < A (e (positiveExitLeaf d hb hinside vout q)) at hh
    rw [houtLabel] at hh
    exact lt_irrefl _ hh
  have hcartBoth : Disjoint (range (e ∘ positiveExitLeaf d hb hinside vin))
      (range (e ∘ positiveExitLeaf d hb hinside vout)) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨q, rfl⟩ ⟨r, hr⟩
    have hh := congrArg A hr
    change A (e (positiveExitLeaf d hb hinside vout r)) =
      A (e (positiveExitLeaf d hb hinside vin q)) at hh
    rw [houtLabel, hinLabel] at hh
    exact hlowhigh.ne hh
  have hsphere (v : Ioo (0 : ℝ) δ)
      (hd : Disjoint (range (e ∘ positiveExitLeaf d hb hinside v)) C) :
      Disjoint (range (positiveExitGaussLeaf d hb hinside v)) (gnomonicPoint '' C) := by
    apply Set.disjoint_left.mpr
    rintro n ⟨q, rfl⟩ ⟨p, hp, heq⟩
    have hh := congrArg (fun n : RoundSphere => gnomonicInverse n.val) heq
    change gnomonicInverse (planarUnitNormal p) =
      gnomonicInverse (positiveExitGaussLeaf d hb hinside v q).val at hh
    rw [gnomonic_left_inverse, positiveExitGaussLeaf_cartesian_source d hb e hinside heF] at hh
    exact (Set.disjoint_left.mp hd) (mem_range_self q) (by
      change e (positiveExitLeaf d hb hinside v q) ∈ C
      rw [← hh]
      exact hp)
  refine ⟨vin, vout, horder, ?_, hcartIn, hcartOut, hcartBoth,
    hsphere vin hcartIn, hsphere vout hcartOut, ?_⟩
  · intro p hp
    rw [hvin, hvout]
    exact hbounds p hp
  · apply Set.disjoint_left.mpr
    rintro n ⟨q, rfl⟩ ⟨r, hr⟩
    have hh := congrArg (fun n : RoundSphere => gnomonicInverse n.val) hr
    rw [positiveExitGaussLeaf_cartesian_source d hb e hinside heF,
      positiveExitGaussLeaf_cartesian_source d hb e hinside heF] at hh
    exact (Set.disjoint_left.mp hcartBoth) (mem_range_self q) ⟨r, hh⟩

end
end TightVer401
