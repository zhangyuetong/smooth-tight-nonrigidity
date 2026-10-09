import TightVer401.CompletedSaddleAnnulusCylinderMap

/-! Injectivity of the actual resolved-height cylinder on its actual closed
strip. No cylinder injection or height-output premise is supplied. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem completedSaddleAnnulusCylinderMap_plane_eq_of_eq
    {G : Coord → ℝ} {e : OpenPartialHomeomorph Coord Coord}
    {A RN d0 dInfinity : ℝ} {β : ℝ → ℝ}
    {p s : AddCircle (2 * Real.pi) × ℝ}
    (he : completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p =
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β s) :
    completedSaddleAnnulusCylinderPlanePoint
      (β (completedSaddleAnnulusCylinderPhase p.2)) p.1 =
    completedSaddleAnnulusCylinderPlanePoint
      (β (completedSaddleAnnulusCylinderPhase s.2)) s.1 := by
  ext i
  have hi := congrArg (fun v : Ambient => -(v i.castSucc)) he
  fin_cases i <;> unfold completedSaddleAnnulusCylinderMap at hi <;>
    split_ifs at hi <;> simpa [completedSaddleAnnulusCylinderPlanePoint,
      revolutionCircleRadial,revolutionAxis] using hi

private theorem completedSaddleAnnulusCylinderMap_signs_of_height_bound
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hBound : ∀ y : Coord, A < planarRadius y → planarRadius y ≤ RN →
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) y < dInfinity) :
    ∀ p ∈ (univ ×ˢ Icc (0 : ℝ) Real.pi),
      (p.2 < Real.pi/2 → completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 < 0) ∧
      (Real.pi/2 < p.2 → 0 < completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2) := by
  intro p hp
  have hpPhase := completedSaddleAnnulusCylinderPhase_mem hp.2
  have hmid : Real.pi/2 ∈ Icc (Real.pi/2) Real.pi := ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hrange := completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hp.2
  have hrpos : 0 < β (completedSaddleAnnulusCylinderPhase p.2) := hA.trans_le hrange.1
  have hAbove (hu : Real.pi/2 < completedSaddleAnnulusCylinderPhase p.2) :
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e)
        (completedSaddleAnnulusCylinderPlanePoint
          (β (completedSaddleAnnulusCylinderPhase p.2)) p.1) < dInfinity := by
    apply hBound
    · rw [completedSaddleAnnulusCylinderPlanePoint_radius hrpos,← hβA]
      exact hMono hmid hpPhase hu
    · rw [completedSaddleAnnulusCylinderPlanePoint_radius hrpos]
      exact hrange.2
  constructor
  · intro hu
    have hphase : Real.pi/2 < completedSaddleAnnulusCylinderPhase p.2 := by
      rw [completedSaddleAnnulusCylinderPhase_lower hu.le]
      linarith
    have hz := hAbove hphase
    simpa [completedSaddleAnnulusCylinderMap,revolutionCircleRadial,revolutionAxis,
      if_pos hu.le] using sub_neg.mpr hz
  · intro hu
    have hphase : Real.pi/2 < completedSaddleAnnulusCylinderPhase p.2 := by
      rw [completedSaddleAnnulusCylinderPhase_upper hu.le]
      exact hu
    have hz := hAbove hphase
    simpa [completedSaddleAnnulusCylinderMap,revolutionCircleRadial,revolutionAxis,
      if_neg (not_le_of_gt hu)] using sub_pos.mpr hz

section ActualData
variable {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
variable {A RN μ B ε L d0 dInfinity : ℝ}
variable (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
variable (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
variable (hSource : e.source = {p : Coord | 0 < planarRadius p})
variable (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
variable (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
variable (heG : ∀ p ∈ e.source, e p = planarGradient G p)
variable (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
  G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
variable (hInfinity : ∀ p : Coord, L < planarRadius p →
  G p = A * planarRadius p - B / planarRadius p + dInfinity)
variable {β : ℝ → ℝ} (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
variable (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
include hA hARN hμ hB hε hL hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN

/-- The actual closed-cylinder height has the required sheet signs, derived
from the same scalar terminal data and actual gradient inverse. -/
theorem completedSaddleAnnulusCylinderMap_height_signs :
    ∀ p ∈ (univ ×ˢ Icc (0 : ℝ) Real.pi),
      (p.2 < Real.pi/2 → completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 < 0) ∧
      (Real.pi/2 < p.2 → 0 < completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2) := by
  have hHeight := completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity
  have hBound : ∀ y : Coord, A < planarRadius y → planarRadius y ≤ RN →
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) y < dInfinity := by
    intro y hyA hyRN
    by_cases ho : planarRadius y = RN
    · rw [completedSaddleAnnulusHeightResolved_outer_boundary hARN ho]
      exact hHeight.2.2.1
    · exact (hHeight.2.2.2.1 y ⟨hyA,lt_of_le_of_ne hyRN ho⟩).2
  exact completedSaddleAnnulusCylinderMap_signs_of_height_bound G e hA hMono hβA hβRN hBound

/-- The physical height is zero exactly at the actual central neck circle. -/
theorem completedSaddleAnnulusCylinderMap_height_zero_iff
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ (univ ×ˢ Icc (0 : ℝ) Real.pi)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 = 0 ↔ p.2 = Real.pi/2 := by
  have hs := completedSaddleAnnulusCylinderMap_height_signs e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN p hp
  constructor
  · intro hz
    rcases lt_trichotomy p.2 (Real.pi/2) with hlt | heq | hgt
    · have hneg := hs.1 hlt
      linarith
    · exact heq
    · have hpos := hs.2 hgt
      linarith
  · intro hm
    have hpEq : p = (p.1,Real.pi/2) := Prod.ext rfl hm
    rw [hpEq,completedSaddleAnnulusCylinderMap_neck G e hA hβA]
    simp [revolutionCircleRadial]

/-- Actual closed-cylinder injectivity. Horizontal coordinates recover
radius and angle; actual sheet-height signs rule out the reflected phase. -/
theorem completedSaddleAnnulusCylinderMap_injOn :
    InjOn (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (univ ×ˢ Icc (0 : ℝ) Real.pi) := by
  have hSigns := completedSaddleAnnulusCylinderMap_height_signs e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN
  intro p hp s hs he
  have hpRadius := completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hp.2
  have hsRadius := completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hs.2
  have hpPos := hA.trans_le hpRadius.1
  have hsPos := hA.trans_le hsRadius.1
  have hPlane := completedSaddleAnnulusCylinderMap_plane_eq_of_eq he
  have hRadius := congrArg planarRadius hPlane
  rw [completedSaddleAnnulusCylinderPlanePoint_radius hpPos,
    completedSaddleAnnulusCylinderPlanePoint_radius hsPos] at hRadius
  have hc := congrFun hPlane 0
  have hsn := congrFun hPlane 1
  change -(β (completedSaddleAnnulusCylinderPhase p.2)) * Real.Angle.cos p.1 =
    -(β (completedSaddleAnnulusCylinderPhase s.2)) * Real.Angle.cos s.1 at hc
  change -(β (completedSaddleAnnulusCylinderPhase p.2)) * Real.Angle.sin p.1 =
    -(β (completedSaddleAnnulusCylinderPhase s.2)) * Real.Angle.sin s.1 at hsn
  rw [← hRadius] at hc hsn
  have hCircle : p.1 = s.1 := revolutionAngle_cos_sin_injective
    (mul_left_cancel₀ (neg_ne_zero.mpr hpPos.ne') hc)
    (mul_left_cancel₀ (neg_ne_zero.mpr hpPos.ne') hsn)
  have hPhase := hMono.injOn (completedSaddleAnnulusCylinderPhase_mem hp.2)
    (completedSaddleAnnulusCylinderPhase_mem hs.2) hRadius
  have hHeightEq := congrArg (fun v : Ambient => v 2) he
  by_cases hpSide : p.2 ≤ Real.pi/2
  · by_cases hsSide : s.2 ≤ Real.pi/2
    · rw [completedSaddleAnnulusCylinderPhase_lower hpSide,
        completedSaddleAnnulusCylinderPhase_lower hsSide] at hPhase
      exact Prod.ext hCircle (by linarith)
    · have hsAbove : Real.pi/2 < s.2 := lt_of_not_ge hsSide
      rw [completedSaddleAnnulusCylinderPhase_lower hpSide,
        completedSaddleAnnulusCylinderPhase_upper hsAbove.le] at hPhase
      have hpBelow : p.2 < Real.pi/2 := by linarith
      have hneg := (hSigns p hp).1 hpBelow
      have hpos := (hSigns s hs).2 hsAbove
      linarith
  · have hpAbove : Real.pi/2 < p.2 := lt_of_not_ge hpSide
    by_cases hsSide : s.2 ≤ Real.pi/2
    · rw [completedSaddleAnnulusCylinderPhase_upper hpAbove.le,
        completedSaddleAnnulusCylinderPhase_lower hsSide] at hPhase
      have hsBelow : s.2 < Real.pi/2 := by linarith
      have hpos := (hSigns p hp).2 hpAbove
      have hneg := (hSigns s hs).1 hsBelow
      linarith
    · have hsAbove : Real.pi/2 < s.2 := lt_of_not_ge hsSide
      rw [completedSaddleAnnulusCylinderPhase_upper hpAbove.le,
        completedSaddleAnnulusCylinderPhase_upper hsAbove.le] at hPhase
      exact Prod.ext hCircle hPhase

end ActualData
end
end TightVer401
