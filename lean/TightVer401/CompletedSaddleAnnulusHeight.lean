import TightVer401.QuadraticRadialFillingBoundary
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Actual critical-point-free annular graph height bounds. These are
conditional calculus helpers, not the support completion existence theorem. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

private theorem completedSaddleAnnulusHeight_band_mem_nhds {A RN : ℝ}
    {x : Coord} (hx : x ∈ quadraticRadialFillingOpenAnnulus A RN) :
    quadraticRadialFillingClosedAnnulus A RN ∈ 𝓝 x :=
  Filter.mem_of_superset ((quadraticRadialFilling_openAnnulus_isOpen A RN).mem_nhds hx)
    (quadraticRadialFilling_openAnnulus_subset_closedAnnulus A RN)

private theorem completedSaddleAnnulusHeight_extremum_boundary
    {A RN : ℝ} {Z : Coord → ℝ}
    (hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0)
    {x : Coord} (hx : x ∈ quadraticRadialFillingClosedAnnulus A RN)
    (hExtr : IsMinOn Z (quadraticRadialFillingClosedAnnulus A RN) x ∨
      IsMaxOn Z (quadraticRadialFillingClosedAnnulus A RN) x) :
    planarRadius x = A ∨ planarRadius x = RN := by
  by_cases hA : planarRadius x = A
  · exact Or.inl hA
  by_cases hRN : planarRadius x = RN
  · exact Or.inr hRN
  have hi : x ∈ quadraticRadialFillingOpenAnnulus A RN :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hA), lt_of_le_of_ne hx.2 hRN⟩
  have hz : fderiv ℝ Z x = 0 := by
    rcases hExtr with hmin | hmax
    · exact (hmin.isLocalMin (completedSaddleAnnulusHeight_band_mem_nhds hi)).fderiv_eq_zero
    · exact (hmax.isLocalMax (completedSaddleAnnulusHeight_band_mem_nhds hi)).fderiv_eq_zero
  exact (hRegular x hi hz).elim

theorem completedSaddleAnnulusHeight_closed_bounds {A RN d0 dInfinity : ℝ}
    {Z : Coord → ℝ}
    (hZ : ContinuousOn Z (quadraticRadialFillingClosedAnnulus A RN))
    (hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0)
    (hInner : ∀ x : Coord, planarRadius x = A → Z x = dInfinity)
    (hOuter : ∀ x : Coord, planarRadius x = RN → Z x = d0) :
    ∀ x ∈ quadraticRadialFillingClosedAnnulus A RN,
      min d0 dInfinity ≤ Z x ∧ Z x ≤ max d0 dInfinity := by
  intro x hx
  have hK := quadraticRadialFilling_closedAnnulus_isCompact A RN
  obtain ⟨a,ha,hmin⟩ := hK.exists_isMinOn ⟨x,hx⟩ hZ
  obtain ⟨b,hb,hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hZ
  constructor
  · have hboundary := completedSaddleAnnulusHeight_extremum_boundary hRegular ha (Or.inl hmin)
    have haLow : min d0 dInfinity ≤ Z a := by
      rcases hboundary with hi | ho
      · rw [hInner a hi]; exact min_le_right _ _
      · rw [hOuter a ho]; exact min_le_left _ _
    exact haLow.trans (hmin hx)
  · have hboundary := completedSaddleAnnulusHeight_extremum_boundary hRegular hb (Or.inr hmax)
    have hbHigh : Z b ≤ max d0 dInfinity := by
      rcases hboundary with hi | ho
      · rw [hInner b hi]; exact le_max_right _ _
      · rw [hOuter b ho]; exact le_max_left _ _
    exact (hmax hx).trans hbHigh

theorem completedSaddleAnnulusHeight_open_bounds {A RN d0 dInfinity : ℝ}
    {Z : Coord → ℝ}
    (hZ : ContinuousOn Z (quadraticRadialFillingClosedAnnulus A RN))
    (hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0)
    (hInner : ∀ x : Coord, planarRadius x = A → Z x = dInfinity)
    (hOuter : ∀ x : Coord, planarRadius x = RN → Z x = d0) :
    ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      min d0 dInfinity < Z x ∧ Z x < max d0 dInfinity := by
  have hBounds := completedSaddleAnnulusHeight_closed_bounds hZ hRegular hInner hOuter
  intro x hx
  have hxK := quadraticRadialFilling_openAnnulus_subset_closedAnnulus A RN hx
  have hb := hBounds x hxK
  constructor
  · by_contra hn
    have he : Z x = min d0 dInfinity := le_antisymm (le_of_not_gt hn) hb.1
    have hmin : IsMinOn Z (quadraticRadialFillingClosedAnnulus A RN) x := by
      intro y hy
      rw [he]
      exact (hBounds y hy).1
    exact hRegular x hx
      (hmin.isLocalMin (completedSaddleAnnulusHeight_band_mem_nhds hx)).fderiv_eq_zero
  · by_contra hn
    have he : Z x = max d0 dInfinity := le_antisymm hb.2 (le_of_not_gt hn)
    have hmax : IsMaxOn Z (quadraticRadialFillingClosedAnnulus A RN) x := by
      intro y hy
      rw [he]
      exact (hBounds y hy).2
    exact hRegular x hx
      (hmax.isLocalMax (completedSaddleAnnulusHeight_band_mem_nhds hx)).fderiv_eq_zero

/-- The literal outer quadratic height collar forces the order of the two
boundary heights. Positive completion height is derived, not assumed. -/
theorem completedSaddleAnnulusHeight_separation {A RN μ d0 dInfinity ε : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ) (hε : 0 < ε)
    {Z : Coord → ℝ}
    (hZ : ContinuousOn Z (quadraticRadialFillingClosedAnnulus A RN))
    (hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0)
    (hInner : ∀ x : Coord, planarRadius x = A → Z x = dInfinity)
    (hOuter : ∀ x : Coord, planarRadius x = RN → Z x = d0)
    (hCollar : ∀ x : Coord, RN-ε < planarRadius x → planarRadius x < RN →
      Z x = d0 + (RN-planarRadius x)^2/(2*μ)) : d0 < dInfinity := by
  let δ := min ε ((RN-A)/2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδA : δ ≤ (RN-A)/2 := min_le_right _ _
  let r := RN-δ/2
  have hrA : A < r := by dsimp [r]; linarith
  have hr : 0 < r := hA.trans hrA
  have hrRN : r < RN := by dsimp [r]; linarith
  have hrε : RN-ε < r := by dsimp [r]; linarith
  let x : Coord := ![r,0]
  have hxr : planarRadius x = r := by
    simp [x,planarRadius,Real.sqrt_sq hr.le]
  have hx : x ∈ quadraticRadialFillingClosedAnnulus A RN := by
    constructor <;> rw [hxr]
    · exact hrA.le
    · exact hrRN.le
  have hlarge : d0 < Z x := by
    rw [hCollar x (by rwa [hxr]) (by rwa [hxr]), hxr]
    have hp : 0 < (RN-r)^2/(2*μ) := div_pos (sq_pos_of_pos (sub_pos.mpr hrRN)) (by positivity)
    linarith
  have hbound := (completedSaddleAnnulusHeight_closed_bounds hZ hRegular hInner hOuter x hx).2
  by_contra hn
  rw [max_eq_left (le_of_not_gt hn)] at hbound
  exact not_lt_of_ge hbound hlarge

end
end TightVer401
