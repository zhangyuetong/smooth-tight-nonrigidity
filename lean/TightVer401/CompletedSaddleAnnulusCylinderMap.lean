import TightVer401.CompletedSaddleAnnulusGraphCollars
import TightVer401.CompletedSaddleAnnulusCollars
import TightVer401.CompletedSaddleAnnulusRadialParameter
import Mathlib.Topology.Piecewise

/-! The actual native closed-cylinder map constructed from the same resolved
support height. Upstream completion and native rank/curvature are separate. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def completedSaddleAnnulusCylinderPhase (u : ℝ) : ℝ := max u (Real.pi - u)

def completedSaddleAnnulusCylinderPlanePoint (r : ℝ)
    (q : AddCircle (2 * Real.pi)) : Coord :=
  fun i => -r * revolutionCircleRadial q i.castSucc

def completedSaddleAnnulusCylinderMap (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (A RN d0 dInfinity : ℝ)
    (β : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  let r := β (completedSaddleAnnulusCylinderPhase p.2)
  let z := completedSaddleAnnulusHeightResolved A RN d0 dInfinity
    (completedSaddleAnnulusGraphHeight G e) (completedSaddleAnnulusCylinderPlanePoint r p.1)
  r • revolutionCircleRadial p.1 +
    (if p.2 ≤ Real.pi/2 then z - dInfinity else dInfinity - z) • revolutionAxis

theorem completedSaddleAnnulusCylinderPlanePoint_representative (r θ : ℝ) :
    completedSaddleAnnulusCylinderPlanePoint r (periodProjection (2 * Real.pi) θ) =
      completedSaddleAnnulusPolarPoint r θ := by
  ext i
  fin_cases i <;> simp [completedSaddleAnnulusCylinderPlanePoint,
    revolutionCircleRadial_representative,revolutionRadial,
    completedSaddleAnnulusPolarPoint,quadraticRadialFillingCircle_coord,saddlePolarChart]

theorem completedSaddleAnnulusCylinderPlanePoint_radius {r : ℝ} (hr : 0 < r)
    (q : AddCircle (2 * Real.pi)) :
    planarRadius (completedSaddleAnnulusCylinderPlanePoint r q) = r := by
  obtain ⟨θ,rfl⟩ := QuotientAddGroup.mk_surjective q
  change planarRadius (completedSaddleAnnulusCylinderPlanePoint r
    (periodProjection (2 * Real.pi) θ)) = r
  rw [completedSaddleAnnulusCylinderPlanePoint_representative]
  exact completedSaddleAnnulusPolarPoint_radius hr θ

theorem completedSaddleAnnulusCylinderPhase_lower {u : ℝ} (hu : u ≤ Real.pi/2) :
    completedSaddleAnnulusCylinderPhase u = Real.pi - u :=
  max_eq_right (by linarith)

theorem completedSaddleAnnulusCylinderPhase_upper {u : ℝ} (hu : Real.pi/2 ≤ u) :
    completedSaddleAnnulusCylinderPhase u = u := max_eq_left (by linarith)

theorem completedSaddleAnnulusCylinderPhase_continuous :
    Continuous completedSaddleAnnulusCylinderPhase :=
  continuous_id.max (continuous_const.sub continuous_id)

theorem completedSaddleAnnulusCylinderPhase_mem {u : ℝ} (hu : u ∈ Icc 0 Real.pi) :
    completedSaddleAnnulusCylinderPhase u ∈ Icc (Real.pi/2) Real.pi := by
  constructor
  · by_cases h : u ≤ Real.pi/2
    · rw [completedSaddleAnnulusCylinderPhase_lower h]; linarith [hu.1]
    · rw [completedSaddleAnnulusCylinderPhase_upper (le_of_not_ge h)]
      exact le_of_not_ge h
  · exact max_le hu.2 (by linarith [hu.1])

theorem completedSaddleAnnulusCylinderMap_radius_mem {A RN : ℝ} {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {u : ℝ} (hu : u ∈ Icc 0 Real.pi) :
    β (completedSaddleAnnulusCylinderPhase u) ∈ Icc A RN := by
  have hp := completedSaddleAnnulusCylinderPhase_mem hu
  have hmid : Real.pi/2 ∈ Icc (Real.pi/2) Real.pi := ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hend : Real.pi ∈ Icc (Real.pi/2) Real.pi := ⟨by linarith [Real.pi_pos],le_rfl⟩
  constructor
  · rw [← hβA]
    exact hMono.monotoneOn hmid hp hp.1
  · rw [← hβRN]
    exact hMono.monotoneOn hp hend hp.2

theorem completedSaddleAnnulusCylinderMap_neck
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hβA : β (Real.pi/2) = A) (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,Real.pi/2) =
      A • revolutionCircleRadial q := by
  have hp := completedSaddleAnnulusCylinderPlanePoint_radius hA q
  simp only [completedSaddleAnnulusCylinderMap,
    completedSaddleAnnulusCylinderPhase_upper le_rfl,hβA]
  rw [completedSaddleAnnulusHeightResolved_inner_boundary hp]
  simp

theorem completedSaddleAnnulusCylinderMap_south_boundary
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hARN : A < RN) (hRN : 0 < RN) {β : ℝ → ℝ}
    (hβRN : β Real.pi = RN) (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,0) =
      RN • revolutionCircleRadial q + (-(dInfinity-d0)) • revolutionAxis := by
  have hp := completedSaddleAnnulusCylinderPlanePoint_radius hRN q
  simp only [completedSaddleAnnulusCylinderMap,
    completedSaddleAnnulusCylinderPhase_lower (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi/2),
    sub_zero,hβRN]
  rw [completedSaddleAnnulusHeightResolved_outer_boundary hARN hp]
  simp only [if_pos (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi/2)]
  congr 1
  ring

theorem completedSaddleAnnulusCylinderMap_north_boundary
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hARN : A < RN) (hRN : 0 < RN) {β : ℝ → ℝ}
    (hβRN : β Real.pi = RN) (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,Real.pi) =
      RN • revolutionCircleRadial q + (dInfinity-d0) • revolutionAxis := by
  have hp := completedSaddleAnnulusCylinderPlanePoint_radius hRN q
  simp only [completedSaddleAnnulusCylinderMap,
    completedSaddleAnnulusCylinderPhase_upper (by linarith [Real.pi_pos] : Real.pi/2 ≤ Real.pi),hβRN]
  rw [completedSaddleAnnulusHeightResolved_outer_boundary hARN hp]
  simp only [if_neg (by linarith [Real.pi_pos] : ¬ Real.pi ≤ Real.pi/2)]

/-- Exact actual neck polynomial on both sheets, including the central circle. -/
theorem completedSaddleAnnulusCylinderMap_neck_formula
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {β : ℝ → ℝ} (q : AddCircle (2 * Real.pi)) {u : ℝ}
    (hβ : β (completedSaddleAnnulusCylinderPhase u) = A+B*(u-Real.pi/2)^2)
    (hNear : B*(u-Real.pi/2)^2 < B/L^2) (hRN : A+B*(u-Real.pi/2)^2 < RN) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
      (A+B*(u-Real.pi/2)^2) • revolutionCircleRadial q +
        (2*B*(u-Real.pi/2)) • revolutionAxis := by
  let r := A+B*(u-Real.pi/2)^2
  let y := completedSaddleAnnulusCylinderPlanePoint r q
  have hr : 0 < r := by dsimp [r]; positivity
  have hyr : planarRadius y = r := completedSaddleAnnulusCylinderPlanePoint_radius hr q
  by_cases hu : u = Real.pi/2
  · subst u
    have hβmid : β (Real.pi/2) = A := by rw [completedSaddleAnnulusCylinderPhase_upper le_rfl] at hβ; simpa using hβ
    simpa using completedSaddleAnnulusCylinderMap_neck G e hA hβmid q
  have hOffset : 0 < planarRadius y - A := by
    rw [hyr]
    dsimp [r]
    nlinarith [mul_pos hB (sq_pos_of_ne_zero (sub_ne_zero.mpr hu))]
  have hyTarget : y ∈ e.target := by
    rw [hTarget]
    exact ⟨by linarith,by simpa only [hyr] using hRN⟩
  have hHeight := completedSaddleAnnulusNeck_graph_height_resolved e hB hL hSource heG hInfinity
    hyTarget (by rw [hyr]; exact hr) hOffset (by rw [hyr]; dsimp [r]; linarith)
  have hQuot : (planarRadius y - A) / B = (u-Real.pi/2)^2 := by
    rw [hyr]
    dsimp [r]
    field_simp [hB.ne']
    <;> ring
  have hResolved : completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) y = dInfinity-2*B*|u-Real.pi/2| := by
    rw [completedSaddleAnnulusHeightResolved_eq_interior (show y ∈
      quadraticRadialFillingOpenAnnulus A RN from by rwa [← hTarget]),
      hHeight,hQuot,Real.sqrt_sq_eq_abs]
  unfold completedSaddleAnnulusCylinderMap
  simp only [hβ]
  change r • revolutionCircleRadial q +
    (if u ≤ Real.pi/2 then completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) y-dInfinity else dInfinity-
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) y) • revolutionAxis = _
  rw [hResolved]
  by_cases hside : u ≤ Real.pi/2
  · rw [if_pos hside,abs_of_nonpos (by linarith : u-Real.pi/2 ≤ 0)]
    congr 1
    ring
  · rw [if_neg hside,abs_of_nonneg (by linarith : 0 ≤ u-Real.pi/2)]
    congr 1
    ring

/-- The actual square germ of beta produces a uniform native-circle neck
identity in a genuine two-sided neighborhood of the middle level. -/
theorem completedSaddleAnnulusCylinderMap_neck_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {β : ℝ → ℝ}
    (hβ : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2)) :
    ∀ᶠ u in 𝓝 (Real.pi/2), ∀ q : AddCircle (2 * Real.pi),
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
        (A+B*(u-Real.pi/2)^2) • revolutionCircleRadial q +
          (2*B*(u-Real.pi/2)) • revolutionAxis := by
  have hm : completedSaddleAnnulusCylinderPhase (Real.pi/2) = Real.pi/2 :=
    completedSaddleAnnulusCylinderPhase_upper le_rfl
  have ht : Tendsto completedSaddleAnnulusCylinderPhase (𝓝 (Real.pi/2)) (𝓝 (Real.pi/2)) := by
    simpa only [hm] using completedSaddleAnnulusCylinderPhase_continuous.tendsto (Real.pi/2)
  have hnearOpen : IsOpen {u : ℝ | B*(u-Real.pi/2)^2 < B/L^2} :=
    isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)) continuous_const
  have houterOpen : IsOpen {u : ℝ | A+B*(u-Real.pi/2)^2 < RN} :=
    isOpen_lt (continuous_const.add (continuous_const.mul
      ((continuous_id.sub continuous_const).pow 2))) continuous_const
  have hmidNear : Real.pi/2 ∈ {u : ℝ | B*(u-Real.pi/2)^2 < B/L^2} := by
    change B * (Real.pi/2-Real.pi/2)^2 < B/L^2
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero]
    exact div_pos hB (sq_pos_of_pos hL)
  have hmidOuter : Real.pi/2 ∈ {u : ℝ | A+B*(u-Real.pi/2)^2 < RN} := by simpa using hARN
  filter_upwards [hβ.comp_tendsto ht,hnearOpen.mem_nhds hmidNear,
    houterOpen.mem_nhds hmidOuter] with u hu hnear houter
  intro q
  apply completedSaddleAnnulusCylinderMap_neck_formula e hA hB hL hSource hTarget heG hInfinity
    q _ hnear houter
  change β (completedSaddleAnnulusCylinderPhase u) =
    A+B*(completedSaddleAnnulusCylinderPhase u-Real.pi/2)^2 at hu
  rw [hu]
  by_cases hs : u ≤ Real.pi/2
  · rw [completedSaddleAnnulusCylinderPhase_lower hs]
    ring
  · rw [completedSaddleAnnulusCylinderPhase_upper (le_of_not_ge hs)]

/-- Both signed endpoint models from the actual scalar quadratic collar,
including the outer boundary. The beta equality is radial parameter data. -/
theorem completedSaddleAnnulusCylinderMap_quadratic_formula
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {β : ℝ → ℝ} (q : AddCircle (2 * Real.pi)) {u t : ℝ}
    (hβ : β (completedSaddleAnnulusCylinderPhase u) = RN+μ*t)
    (ht : t ≤ 0) (hAnear : A < RN+μ*t) (hNear : -t < ε) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
      (RN+μ*t) • revolutionCircleRadial q +
        (if u ≤ Real.pi/2 then -(dInfinity-d0)+μ*t^2/2
          else dInfinity-d0-μ*t^2/2) • revolutionAxis := by
  let y := completedSaddleAnnulusCylinderPlanePoint (RN+μ*t) q
  have hr : 0 < RN+μ*t := hA.trans hAnear
  have hyr : planarRadius y = RN+μ*t := completedSaddleAnnulusCylinderPlanePoint_radius hr q
  have hResolved : completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) y = d0+μ*t^2/2 := by
    by_cases ht0 : t = 0
    · have hARN : A < RN := by simpa [ht0] using hAnear
      have hyrRN : planarRadius y = RN := by simpa [ht0] using hyr
      rw [completedSaddleAnnulusHeightResolved_outer_boundary hARN hyrRN,ht0]
      ring
    have htneg : t < 0 := lt_of_le_of_ne ht ht0
    have hRadiusRN : planarRadius y < RN := by
      rw [hyr]
      nlinarith [mul_neg_of_pos_of_neg hμ htneg]
    have hyTarget : y ∈ e.target := by
      rw [hTarget]
      exact ⟨by rwa [hyr],hRadiusRN⟩
    rw [completedSaddleAnnulusHeightResolved_eq_interior
      (show y ∈ quadraticRadialFillingOpenAnnulus A RN from by rwa [← hTarget]),
      completedSaddleAnnulusQuadratic_graph_height hμ hQuadratic e hSource heG
        hyTarget (by rw [hyr]; exact hr) (sub_pos.mpr hRadiusRN)
        (by rw [hyr]; nlinarith [mul_lt_mul_of_pos_left hNear hμ]),hyr]
    field_simp [hμ.ne']
    <;> ring
  unfold completedSaddleAnnulusCylinderMap
  simp only [hβ]
  change (RN+μ*t) • revolutionCircleRadial q +
    (if u ≤ Real.pi/2 then completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) y-dInfinity else dInfinity-
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) y) • revolutionAxis = _
  rw [hResolved]
  by_cases hs : u ≤ Real.pi/2
  · rw [if_pos hs,if_pos hs]
    congr 1
    ring
  · rw [if_neg hs,if_neg hs]
    congr 1
    ring

/-- Literal northern normalized collar identity for the constructed map. -/
theorem completedSaddleAnnulusCylinderMap_north_formula
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {β : ℝ → ℝ} (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : Real.pi/2 < u)
    (hβ : β (completedSaddleAnnulusCylinderPhase u) =
      RN+μ*completedSaddleAnnulusNorthTransverse (dInfinity-d0) μ u)
    (ht : completedSaddleAnnulusNorthTransverse (dInfinity-d0) μ u ≤ 0)
    (hAnear : A < RN+μ*completedSaddleAnnulusNorthTransverse (dInfinity-d0) μ u)
    (hNear : -completedSaddleAnnulusNorthTransverse (dInfinity-d0) μ u < ε) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
      completedSaddleAnnulusNorthCollar RN μ (dInfinity-d0) (q,u) := by
  rw [completedSaddleAnnulusCylinderMap_quadratic_formula e hA hμ hSource hTarget heG
    hQuadratic q hβ ht hAnear hNear,if_neg (not_le_of_gt hu)]
  rfl

/-- Literal southern normalized collar identity for the constructed map. -/
theorem completedSaddleAnnulusCylinderMap_south_formula
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {β : ℝ → ℝ} (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ≤ Real.pi/2)
    (hβ : β (completedSaddleAnnulusCylinderPhase u) =
      RN+μ*completedSaddleAnnulusSouthTransverse (dInfinity-d0) μ u)
    (ht : completedSaddleAnnulusSouthTransverse (dInfinity-d0) μ u ≤ 0)
    (hAnear : A < RN+μ*completedSaddleAnnulusSouthTransverse (dInfinity-d0) μ u)
    (hNear : -completedSaddleAnnulusSouthTransverse (dInfinity-d0) μ u < ε) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β (q,u) =
      completedSaddleAnnulusSouthCollar RN μ (dInfinity-d0) (q,u) := by
  rw [completedSaddleAnnulusCylinderMap_quadratic_formula e hA hμ hSource hTarget heG
    hQuadratic q hβ ht hAnear hNear,if_pos hu]
  rfl
private theorem completedSaddleAnnulusCylinderMap_continuousOn_of_resolved
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ} (hβ : Continuous β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hResolved : ContinuousOn (completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e)) (quadraticRadialFillingClosedAnnulus A RN)) :
    ContinuousOn (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (univ ×ˢ Icc (0 : ℝ) Real.pi) := by
  let K : Set (AddCircle (2 * Real.pi) × ℝ) := univ ×ˢ Icc (0 : ℝ) Real.pi
  let R : AddCircle (2 * Real.pi) × ℝ → ℝ :=
    fun p => β (completedSaddleAnnulusCylinderPhase p.2)
  let Y : AddCircle (2 * Real.pi) × ℝ → Coord :=
    fun p => completedSaddleAnnulusCylinderPlanePoint (R p) p.1
  let Z : AddCircle (2 * Real.pi) × ℝ → ℝ :=
    fun p => completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) (Y p)
  have hR : Continuous R :=
    hβ.comp (completedSaddleAnnulusCylinderPhase_continuous.comp continuous_snd)
  have hRad : Continuous (fun p : AddCircle (2 * Real.pi) × ℝ => revolutionCircleRadial p.1) :=
    revolutionCircleRadial_contMDiff.continuous.comp continuous_fst
  have hY : Continuous Y := by
    apply continuous_pi
    intro i
    exact hR.neg.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i.castSucc).continuous.comp hRad)
  have hMaps : MapsTo Y K (quadraticRadialFillingClosedAnnulus A RN) := by
    intro p hp
    have hr : R p ∈ Icc A RN :=
      completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hp.2
    have hrpos : 0 < R p := hA.trans_le hr.1
    change A ≤ planarRadius (completedSaddleAnnulusCylinderPlanePoint (R p) p.1) ∧
      planarRadius (completedSaddleAnnulusCylinderPlanePoint (R p) p.1) ≤ RN
    rw [completedSaddleAnnulusCylinderPlanePoint_radius hrpos]
    exact hr
  have hZ : ContinuousOn Z K := hResolved.comp hY.continuousOn hMaps
  have hLower : ContinuousOn (fun p => Z p-dInfinity) K := hZ.sub continuous_const.continuousOn
  have hUpper : ContinuousOn (fun p => dInfinity-Z p) K := continuous_const.continuousOn.sub hZ
  have hSigned : ContinuousOn (fun p : AddCircle (2 * Real.pi) × ℝ =>
      if p.2 ≤ Real.pi/2 then Z p-dInfinity else dInfinity-Z p) K := by
    apply ContinuousOn.if ?_ (hLower.mono inter_subset_left) (hUpper.mono inter_subset_left)
    intro p hp
    have hmid : p.2 = Real.pi/2 :=
      frontier_le_subset_eq continuous_snd continuous_const hp.2
    have hrA : R p = A := by
      change β (completedSaddleAnnulusCylinderPhase p.2) = A
      rw [hmid,completedSaddleAnnulusCylinderPhase_upper le_rfl,hβA]
    have hyrA : planarRadius (Y p) = A := by
      change planarRadius (completedSaddleAnnulusCylinderPlanePoint (R p) p.1) = A
      rw [hrA,completedSaddleAnnulusCylinderPlanePoint_radius hA]
    have hzA : Z p = dInfinity := completedSaddleAnnulusHeightResolved_inner_boundary hyrA
    rw [hzA]
  change ContinuousOn (fun p => R p • revolutionCircleRadial p.1 +
    (if p.2 ≤ Real.pi/2 then Z p-dInfinity else dInfinity-Z p) • revolutionAxis) K
  exact (hR.continuousOn.smul hRad.continuousOn).add
    (hSigned.smul continuous_const.continuousOn)

/-- Actual closed-strip continuity is derived from the scalar terminal data,
not assumed as a completed-cylinder field. -/
theorem completedSaddleAnnulusCylinderMap_continuousOn
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ B ε L d0 dInfinity : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
    (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {β : ℝ → ℝ} (hβ : Continuous β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN) :
    ContinuousOn (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (univ ×ˢ Icc (0 : ℝ) Real.pi) := by
  have hResolved := (completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity).1
  exact completedSaddleAnnulusCylinderMap_continuousOn_of_resolved G e hA hβ
    hMono hβA hβRN hResolved
/-- The certified cosine parameter germ is exactly the root's signed north
radial germ; no graph-height or completed-cylinder field is assumed. -/
theorem completedSaddleAnnulusCylinderRadius_north_germ
    {RN μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h) {β : ℝ → ℝ}
    (hβ : β =ᶠ[𝓝 Real.pi] (fun u => RN-2*Real.sqrt (μ*h)*Real.cos (u/2))) :
    (fun u => β (completedSaddleAnnulusCylinderPhase u)) =ᶠ[𝓝 Real.pi]
      (fun u => RN+μ*completedSaddleAnnulusNorthTransverse h μ u) := by
  have hsqrt : Real.sqrt (μ*h) = μ*Real.sqrt (h/μ) := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_pos hμ hh).le
      (mul_nonneg hμ.le (Real.sqrt_nonneg _))).mpr
    rw [mul_pow,Real.sq_sqrt (div_pos hh hμ).le]
    field_simp [hμ.ne']
    <;> ring
  have hmid : Real.pi/2 < Real.pi := by linarith [Real.pi_pos]
  filter_upwards [hβ,isOpen_Ioi.mem_nhds hmid] with u hu huMid
  rw [completedSaddleAnnulusCylinderPhase_upper huMid.le,hu,hsqrt]
  unfold completedSaddleAnnulusNorthTransverse
  ring

/-- Reflection of the same beta cosine germ gives the literal signed south
radial germ. This is parameter data, not an imposed cylinder collar equality. -/
theorem completedSaddleAnnulusCylinderRadius_south_germ
    {RN μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h) {β : ℝ → ℝ}
    (hβ : β =ᶠ[𝓝 Real.pi] (fun u => RN-2*Real.sqrt (μ*h)*Real.cos (u/2))) :
    (fun u => β (completedSaddleAnnulusCylinderPhase u)) =ᶠ[𝓝 (0:ℝ)]
      (fun u => RN+μ*completedSaddleAnnulusSouthTransverse h μ u) := by
  have hsqrt : Real.sqrt (μ*h) = μ*Real.sqrt (h/μ) := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_pos hμ hh).le
      (mul_nonneg hμ.le (Real.sqrt_nonneg _))).mpr
    rw [mul_pow,Real.sq_sqrt (div_pos hh hμ).le]
    field_simp [hμ.ne']
    <;> ring
  have ht : Tendsto (fun u : ℝ => Real.pi-u) (𝓝 (0:ℝ)) (𝓝 Real.pi) := by
    have hc : Continuous (fun u : ℝ => Real.pi-u) := continuous_const.sub continuous_id
    simpa only [sub_zero] using hc.tendsto (0:ℝ)
  have hmid : (0:ℝ) < Real.pi/2 := by linarith [Real.pi_pos]
  filter_upwards [hβ.comp_tendsto ht,isOpen_Iio.mem_nhds hmid] with u hu huMid
  change β (Real.pi-u) = RN-2*Real.sqrt (μ*h)*Real.cos ((Real.pi-u)/2) at hu
  rw [completedSaddleAnnulusCylinderPhase_lower huMid.le,hu,hsqrt]
  have hcos : Real.cos ((Real.pi-u)/2) = Real.sin (u/2) := by
    rw [show (Real.pi-u)/2 = Real.pi/2-u/2 by ring,Real.cos_sub]
    simp
  rw [hcos]
  unfold completedSaddleAnnulusSouthTransverse
  ring
end
end TightVer401



