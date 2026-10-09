import TightVer401.AngularDescentCharts
import Mathlib.Topology.Order.Compact

/-! Actual radial source bands for the later quadratic-filling degree argument.
No target image or injectivity assertion is assumed here. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology

def quadraticRadialFillingOpenAnnulus (ε R : ℝ) : Set Coord :=
  {p | ε < planarRadius p ∧ planarRadius p < R}

def quadraticRadialFillingClosedAnnulus (ε R : ℝ) : Set Coord :=
  {p | ε ≤ planarRadius p ∧ planarRadius p ≤ R}

def quadraticRadialFillingRadiusLevel (r : ℝ) : Set Coord :=
  {p | planarRadius p = r}

theorem quadraticRadialFilling_radius_continuous : Continuous planarRadius :=
  Real.continuous_sqrt.comp
    (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))

theorem quadraticRadialFilling_openAnnulus_isOpen (ε R : ℝ) :
    IsOpen (quadraticRadialFillingOpenAnnulus ε R) :=
  (isOpen_lt continuous_const quadraticRadialFilling_radius_continuous).inter
    (isOpen_lt quadraticRadialFilling_radius_continuous continuous_const)

theorem quadraticRadialFilling_closedAnnulus_isClosed (ε R : ℝ) :
    IsClosed (quadraticRadialFillingClosedAnnulus ε R) :=
  (isClosed_le continuous_const quadraticRadialFilling_radius_continuous).inter
    (isClosed_le quadraticRadialFilling_radius_continuous continuous_const)

theorem quadraticRadialFilling_radiusLevel_isClosed (r : ℝ) :
    IsClosed (quadraticRadialFillingRadiusLevel r) :=
  isClosed_eq quadraticRadialFilling_radius_continuous continuous_const

theorem quadraticRadialFilling_openAnnulus_subset_closedAnnulus (ε R : ℝ) :
    quadraticRadialFillingOpenAnnulus ε R ⊆
      quadraticRadialFillingClosedAnnulus ε R :=
  fun _ hp => ⟨hp.1.le, hp.2.le⟩

/-- Physical radius bounds each Cartesian coordinate. This uses the actual
square-root radius, without identifying the coordinate max norm with it. -/
theorem quadraticRadialFilling_abs_coord_le_radius (p : Coord) (i : Fin 2) :
    |p i| ≤ planarRadius p := by
  have hr : 0 ≤ planarRadius p := Real.sqrt_nonneg _
  have hsq : planarRadius p ^ 2 = p 0 ^ 2 + p 1 ^ 2 :=
    Real.sq_sqrt (by positivity)
  apply (sq_le_sq₀ (abs_nonneg (p i)) hr).mp
  rw [sq_abs]
  fin_cases i
  · change p 0 ^ 2 ≤ planarRadius p ^ 2
    nlinarith [sq_nonneg (p 1)]
  · change p 1 ^ 2 ≤ planarRadius p ^ 2
    nlinarith [sq_nonneg (p 0)]

/-- Each actual closed radial band is compact, including the empty cases. -/
theorem quadraticRadialFilling_closedAnnulus_isCompact (ε R : ℝ) :
    IsCompact (quadraticRadialFillingClosedAnnulus ε R) := by
  have hbound : quadraticRadialFillingClosedAnnulus ε R ⊆
      Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R) := by
    intro p hp
    have hc (i : Fin 2) : |p i| ≤ R :=
      (quadraticRadialFilling_abs_coord_le_radius p i).trans hp.2
    exact ⟨fun i => (abs_le.mp (hc i)).1, fun i => (abs_le.mp (hc i)).2⟩
  exact isCompact_Icc.of_isClosed_subset
    (quadraticRadialFilling_closedAnnulus_isClosed ε R) hbound

theorem quadraticRadialFilling_openAnnulus_closure_subset (ε R : ℝ) :
    closure (quadraticRadialFillingOpenAnnulus ε R) ⊆
      quadraticRadialFillingClosedAnnulus ε R :=
  closure_minimal (quadraticRadialFilling_openAnnulus_subset_closedAnnulus ε R)
    (quadraticRadialFilling_closedAnnulus_isClosed ε R)

theorem quadraticRadialFilling_openAnnulus_closure_isCompact (ε R : ℝ) :
    IsCompact (closure (quadraticRadialFillingOpenAnnulus ε R)) :=
  (quadraticRadialFilling_closedAnnulus_isCompact ε R).of_isClosed_subset
    isClosed_closure (quadraticRadialFilling_openAnnulus_closure_subset ε R)

/-- The actual annulus has no additional frontier beyond its two physical
radius levels. A later degree theorem must still prove the image and count. -/
theorem quadraticRadialFilling_openAnnulus_frontier_subset (ε R : ℝ) :
    frontier (quadraticRadialFillingOpenAnnulus ε R) ⊆
      quadraticRadialFillingRadiusLevel ε ∪ quadraticRadialFillingRadiusLevel R := by
  intro p hp
  change p ∈ frontier ({p : Coord | ε < planarRadius p} ∩
    {p : Coord | planarRadius p < R}) at hp
  rcases frontier_inter_subset {p : Coord | ε < planarRadius p}
      {p : Coord | planarRadius p < R} hp with hp | hp
  · exact Or.inl ((frontier_lt_subset_eq continuous_const
      quadraticRadialFilling_radius_continuous hp.1).symm)
  · exact Or.inr (frontier_lt_subset_eq quadraticRadialFilling_radius_continuous
      continuous_const hp.2)

theorem quadraticRadialFilling_radiusLevel_isCompact (r : ℝ) :
    IsCompact (quadraticRadialFillingRadiusLevel r) :=
  (quadraticRadialFilling_closedAnnulus_isCompact r r).of_isClosed_subset
    (quadraticRadialFilling_radiusLevel_isClosed r)
    (fun _ hp => ⟨hp.ge, hp.le⟩)

/-- Actual polar parametrization lands on the stated physical radius level. -/
theorem quadraticRadialFilling_radiusLevel_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    saddlePolarChart ![r, θ] ∈ quadraticRadialFillingRadiusLevel r := by
  exact angularDescent_radius_polar (by simpa using hr)

theorem quadraticRadialFilling_openAnnulus_maps_radius (ε R : ℝ) :
    MapsTo planarRadius (quadraticRadialFillingOpenAnnulus ε R) (Ioo ε R) :=
  fun _ hp => hp

theorem quadraticRadialFilling_closedAnnulus_maps_radius (ε R : ℝ) :
    MapsTo planarRadius (quadraticRadialFillingClosedAnnulus ε R) (Icc ε R) :=
  fun _ hp => hp

/-- Limits of actual interior points stay in the compact closed band. -/
theorem quadraticRadialFilling_closedAnnulus_mem_of_tendsto
    {α : Type*} {l : Filter α} [NeBot l] {p : α → Coord} {x : Coord}
    {ε R : ℝ} (hlim : Tendsto p l (𝓝 x))
    (hmem : ∀ᶠ a in l, p a ∈ quadraticRadialFillingOpenAnnulus ε R) :
    x ∈ quadraticRadialFillingClosedAnnulus ε R :=
  (quadraticRadialFilling_closedAnnulus_isClosed ε R).mem_of_tendsto hlim
    (hmem.mono (fun _ hp =>
      quadraticRadialFilling_openAnnulus_subset_closedAnnulus ε R hp))

/-- Any actual continuous map on the source band has compact band image. -/
theorem quadraticRadialFilling_closedAnnulus_image_isCompact
    {Y : Type*} [TopologicalSpace Y] {F : Coord → Y} {ε R : ℝ}
    (hF : ContinuousOn F (quadraticRadialFillingClosedAnnulus ε R)) :
    IsCompact (F '' quadraticRadialFillingClosedAnnulus ε R) :=
  (quadraticRadialFilling_closedAnnulus_isCompact ε R).image_of_continuousOn hF

end
end TightVer401
