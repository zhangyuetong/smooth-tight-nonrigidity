import TightVer401.CompletedSaddleAnnulusCylinderMap

/-! Uniform literal closed-strip collars of the actual resolved cylinder.
The identities follow from its scalar quadratic germ and the same beta germ. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem completedSaddleAnnulusCylinderMap_south_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN)
    (hμ : 0 < μ) (hε : 0 < ε) (hh : 0 < dInfinity-d0)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {β : ℝ → ℝ}
    (hβ : β =ᶠ[𝓝 Real.pi] (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2))) :
    ∃ δ > 0, δ < Real.pi/2 ∧ ∀ q : AddCircle (2*Real.pi), ∀ u ∈ Icc (0:ℝ) δ,
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
        completedSaddleAnnulusSouthCollar RN μ (dInfinity-d0) (q,u) := by
  let t := completedSaddleAnnulusSouthTransverse (dInfinity-d0) μ
  have ht : Continuous t := (completedSaddleAnnulusSouthTransverse_contDiff _ _).continuous
  have ht0 : t 0 = 0 := completedSaddleAnnulusSouthTransverse_zero _ _
  have hOuter : ∀ᶠ u in 𝓝 (0:ℝ), A < RN+μ*t u :=
    (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul ht))).mem_nhds
      (by change A < RN+μ*t 0; simpa only [ht0,mul_zero,add_zero] using hARN)
  have hNear : ∀ᶠ u in 𝓝 (0:ℝ), -t u < ε :=
    (isOpen_lt ht.neg continuous_const).mem_nhds
      (by change -t 0 < ε; simpa only [ht0,neg_zero] using hε)
  have hGerm : ∀ᶠ u in 𝓝 (0:ℝ), u ∈ Icc (0:ℝ) Real.pi →
      ∀ q : AddCircle (2*Real.pi),
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
        completedSaddleAnnulusSouthCollar RN μ (dInfinity-d0) (q,u) := by
    filter_upwards [completedSaddleAnnulusCylinderRadius_south_germ hμ hh hβ,
      hOuter,hNear,isOpen_Iio.mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi/2)]
      with u hRadius hOuter hNear hSide
    change u < Real.pi/2 at hSide
    intro hu q
    have hNonpos : t u ≤ 0 := by
      by_cases hu0 : u = 0
      · simpa only [hu0,ht0] using (le_rfl : (0:ℝ) ≤ 0)
      · exact (completedSaddleAnnulusSouthTransverse_neg hh hμ
          ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),by linarith [hSide,Real.pi_pos]⟩).le
    exact completedSaddleAnnulusCylinderMap_south_formula e hA hμ hSource hTarget
      heG hQuadratic q hSide.le hRadius hNonpos hOuter hNear
  obtain ⟨r,hr,hBall⟩ := Metric.eventually_nhds_iff.mp hGerm
  let δ := min (r/2) (Real.pi/4)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  refine ⟨δ,hδ,lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]),?_⟩
  intro q u hu
  apply hBall (show dist u (0:ℝ) < r from by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hu.1]
    exact lt_of_le_of_lt hu.2 (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    ⟨hu.1,le_trans hu.2 (le_trans (min_le_right _ _) (by linarith [Real.pi_pos]))⟩ q

theorem completedSaddleAnnulusCylinderMap_north_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN)
    (hμ : 0 < μ) (hε : 0 < ε) (hh : 0 < dInfinity-d0)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {β : ℝ → ℝ}
    (hβ : β =ᶠ[𝓝 Real.pi] (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2))) :
    ∃ δ > 0, δ < Real.pi/2 ∧ ∀ q : AddCircle (2*Real.pi), ∀ u ∈ Icc (Real.pi-δ) Real.pi,
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
        completedSaddleAnnulusNorthCollar RN μ (dInfinity-d0) (q,u) := by
  let t := completedSaddleAnnulusNorthTransverse (dInfinity-d0) μ
  have ht : Continuous t := (completedSaddleAnnulusNorthTransverse_contDiff _ _).continuous
  have ht0 : t Real.pi = 0 := completedSaddleAnnulusNorthTransverse_zero _ _
  have hOuter : ∀ᶠ u in 𝓝 Real.pi, A < RN+μ*t u :=
    (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul ht))).mem_nhds
      (by change A < RN+μ*t Real.pi; simpa only [ht0,mul_zero,add_zero] using hARN)
  have hNear : ∀ᶠ u in 𝓝 Real.pi, -t u < ε :=
    (isOpen_lt ht.neg continuous_const).mem_nhds
      (by change -t Real.pi < ε; simpa only [ht0,neg_zero] using hε)
  have hGerm : ∀ᶠ u in 𝓝 Real.pi, u ∈ Icc (0:ℝ) Real.pi →
      ∀ q : AddCircle (2*Real.pi),
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
        completedSaddleAnnulusNorthCollar RN μ (dInfinity-d0) (q,u) := by
    filter_upwards [completedSaddleAnnulusCylinderRadius_north_germ hμ hh hβ,
      hOuter,hNear,isOpen_Ioi.mem_nhds (by linarith [Real.pi_pos] : Real.pi/2 < Real.pi)]
      with u hRadius hOuter hNear hSide
    change Real.pi/2 < u at hSide
    intro hu q
    have hNonpos : t u ≤ 0 := by
      by_cases hu0 : u = Real.pi
      · simpa only [hu0,ht0] using (le_rfl : (0:ℝ) ≤ 0)
      · exact (completedSaddleAnnulusNorthTransverse_neg hh hμ
          ⟨by linarith [hSide,Real.pi_pos],lt_of_le_of_ne hu.2 hu0⟩).le
    exact completedSaddleAnnulusCylinderMap_north_formula e hA hμ hSource hTarget
      heG hQuadratic q hSide hRadius hNonpos hOuter hNear
  obtain ⟨r,hr,hBall⟩ := Metric.eventually_nhds_iff.mp hGerm
  let δ := min (r/2) (Real.pi/4)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  refine ⟨δ,hδ,lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]),?_⟩
  intro q u hu
  apply hBall (show dist u Real.pi < r from by
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu.2)]
    have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    linarith [hu.1]) ⟨by
      have hδπ : δ < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
      linarith [hu.1],hu.2⟩ q

end
end TightVer401
