import TightVer401.CompletedSaddleAnnulusQuadraticHeight
import TightVer401.CompletedSaddleAnnulusNeckHeight
import TightVer401.CompletedSaddleAnnulusHeightResolution

/-! Resolve the scalar height of the same actual completed potential and
actual gradient inverse. The scalar terminal germs, not supplied graph-height
formulas, yield both collars. Upstream completion existence remains separate. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusActualHeightWidth (A RN μ B ε L : ℝ) : ℝ :=
  min ((RN - A) / 2) (min (μ * ε / 2) ((B / L ^ 2) / 2))

theorem completedSaddleAnnulusActualHeightWidth_pos
    {A RN μ B ε L : ℝ} (hARN : A < RN) (hμ : 0 < μ)
    (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L) :
    0 < completedSaddleAnnulusActualHeightWidth A RN μ B ε L := by
  unfold completedSaddleAnnulusActualHeightWidth
  exact lt_min (by linarith) (lt_min (by positivity) (by positivity))

theorem completedSaddleAnnulusActualHeightWidth_lt_gap
    {A RN μ B ε L : ℝ} (hARN : A < RN) :
    completedSaddleAnnulusActualHeightWidth A RN μ B ε L < RN - A := by
  have hBound : completedSaddleAnnulusActualHeightWidth A RN μ B ε L ≤
      (RN - A) / 2 := min_le_left _ _
  linarith

/-- Both literal actual graph-height collars are derived from the same
scalar potential, not imposed as graph-height or boundary-extension data. -/
theorem completedSaddleAnnulusActualHeight_collars
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ B ε L d0 dInfinity : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
    (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity) :
    (∀ x : Coord, A < planarRadius x →
      planarRadius x < A + completedSaddleAnnulusActualHeightWidth A RN μ B ε L →
      completedSaddleAnnulusGraphHeight G e x =
        dInfinity - 2 * Real.sqrt (B * (planarRadius x - A))) ∧
    (∀ x : Coord, RN - completedSaddleAnnulusActualHeightWidth A RN μ B ε L < planarRadius x →
      planarRadius x < RN → completedSaddleAnnulusGraphHeight G e x =
        d0 + (RN - planarRadius x) ^ 2 / (2 * μ)) := by
  let δ := completedSaddleAnnulusActualHeightWidth A RN μ B ε L
  have hδgap : δ < RN - A := completedSaddleAnnulusActualHeightWidth_lt_gap hARN
  have hδμ : δ ≤ μ * ε / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ (B / L ^ 2) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hBL : 0 < B / L ^ 2 := div_pos hB (sq_pos_of_pos hL)
  constructor
  · intro x hxA hxδ
    change planarRadius x < A + δ at hxδ
    have hxRN : planarRadius x < RN := by linarith
    have hxTarget : x ∈ e.target := by rw [hTarget]; exact ⟨hxA,hxRN⟩
    exact completedSaddleAnnulusNeck_graph_height e hB hL hSource heG hInfinity
      hxTarget (hA.trans hxA) (sub_pos.mpr hxA) (by linarith)
  · intro x hxδ hxRN
    change RN - δ < planarRadius x at hxδ
    have hxA : A < planarRadius x := by linarith
    have hxTarget : x ∈ e.target := by rw [hTarget]; exact ⟨hxA,hxRN⟩
    exact completedSaddleAnnulusQuadratic_graph_height hμ hQuadratic e hSource heG
      hxTarget (hA.trans hxA) (sub_pos.mpr hxRN) (by nlinarith [mul_pos hμ hε])

/-- The named height-separation consumer: construct closed-band continuity,
actual regularity, positive height separation and actual height bounds from
ordinary scalar terminal data and the actual gradient inverse. -/
theorem completedSaddleAnnulusActualHeight_resolution
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ B ε L d0 dInfinity : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
    (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity) :
    ContinuousOn (completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e))
      (quadraticRadialFillingClosedAnnulus A RN) ∧
    (∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      fderiv ℝ (completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e)) x ≠ 0) ∧
    d0 < dInfinity ∧
    (∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      d0 < completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x ∧
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x < dInfinity) ∧
    (∀ x ∈ quadraticRadialFillingClosedAnnulus A RN,
      d0 ≤ completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x ∧
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x ≤ dInfinity) := by
  let δ := completedSaddleAnnulusActualHeightWidth A RN μ B ε L
  have hδ : 0 < δ := completedSaddleAnnulusActualHeightWidth_pos hARN hμ hB hε hL
  have hδgap : δ < RN - A := completedSaddleAnnulusActualHeightWidth_lt_gap hARN
  obtain ⟨hInner,hOuter⟩ := completedSaddleAnnulusActualHeight_collars e
    hA hARN hμ hB hε hL hSource hTarget heG hQuadratic hInfinity
  have hZ : ContinuousOn (completedSaddleAnnulusGraphHeight G e)
      (quadraticRadialFillingOpenAnnulus A RN) := by
    rw [← hTarget]
    exact (completedSaddleAnnulusGraphHeight_contDiffOn e hG hi).continuousOn
  have hPuncture : ∀ p ∈ e.source, 0 < planarRadius p := by
    intro p hp
    rwa [hSource] at hp
  have hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      fderiv ℝ (completedSaddleAnnulusGraphHeight G e) x ≠ 0 := by
    intro x hx
    apply completedSaddleAnnulusGraphHeight_fderiv_ne_zero e hG hi heG hPuncture
    rwa [hTarget]
  have hContinuous := completedSaddleAnnulusHeightResolved_continuousOn
    hARN hB hδ hδgap hZ hInner hOuter
  have hResolvedRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      fderiv ℝ (completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e)) x ≠ 0 :=
    completedSaddleAnnulusHeightResolved_regular hRegular
  have hSep : d0 < dInfinity := completedSaddleAnnulusHeightResolved_separation
    hA hARN hB hμ hδ hδgap hZ hRegular hInner hOuter
  have hInnerBoundary : ∀ x : Coord, planarRadius x = A →
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x = dInfinity :=
    fun _ hx => completedSaddleAnnulusHeightResolved_inner_boundary hx
  have hOuterBoundary : ∀ x : Coord, planarRadius x = RN →
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) x = d0 :=
    fun _ hx => completedSaddleAnnulusHeightResolved_outer_boundary hARN hx
  refine ⟨hContinuous,hResolvedRegular,hSep,?_,?_⟩
  · intro x hx
    simpa only [min_eq_left hSep.le,max_eq_right hSep.le] using
      completedSaddleAnnulusHeight_open_bounds hContinuous hResolvedRegular
        hInnerBoundary hOuterBoundary x hx
  · intro x hx
    simpa only [min_eq_left hSep.le,max_eq_right hSep.le] using
      completedSaddleAnnulusHeight_closed_bounds hContinuous hResolvedRegular
        hInnerBoundary hOuterBoundary x hx

end
end TightVer401

