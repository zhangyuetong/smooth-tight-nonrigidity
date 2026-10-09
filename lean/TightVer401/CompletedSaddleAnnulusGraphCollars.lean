import TightVer401.CompletedSaddleAnnulusGraphs
import TightVer401.QuadraticRadialFillingCircle

/-! Actual real polar graph collars, derived from the same scalar terminal
 germs and actual gradient inverse. Native quotient transport is separate. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusPolarPoint (r θ : ℝ) : Coord :=
  -seamComplexCoord (quadraticRadialFillingCircle r θ)

def completedSaddleAnnulusNeckRealChart (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (A B dInfinity : ℝ) (q : Coord) : Ambient :=
  completedSaddleAnnulusUpperGraph G e dInfinity
    (completedSaddleAnnulusPolarPoint (A + B * q 1 ^ 2) (q 0))

def completedSaddleAnnulusNorthernRealChart (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (RN μ dInfinity : ℝ) (q : Coord) : Ambient :=
  completedSaddleAnnulusUpperGraph G e dInfinity
    (completedSaddleAnnulusPolarPoint (RN + μ * q 1) (q 0))

theorem completedSaddleAnnulusPolarPoint_complex (r θ : ℝ) :
    completedSaddleAnnulusPolarPoint r θ =
      seamComplexCoord (-quadraticRadialFillingCircle r θ) := by
  rw [completedSaddleAnnulusPolarPoint,map_neg]
theorem completedSaddleAnnulusPolarPoint_radius {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    planarRadius (completedSaddleAnnulusPolarPoint r θ) = r := by
  rw [completedSaddleAnnulusPolarPoint, ← map_neg,quadraticRadialFillingRadius_complex]
  simp [quadraticRadialFillingCircle,norm_circleMap_zero,abs_of_pos hr]

theorem completedSaddleAnnulusUpperGraph_polar (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity r θ : ℝ) :
    completedSaddleAnnulusUpperGraph G e dInfinity (completedSaddleAnnulusPolarPoint r θ) =
      r • revolutionRadial θ +
        (dInfinity - completedSaddleAnnulusGraphHeight G e
          (completedSaddleAnnulusPolarPoint r θ)) • revolutionAxis := by
  rw [completedSaddleAnnulusUpperGraph]
  ext i
  fin_cases i <;>
    simp [completedSaddleAnnulusPolarPoint,quadraticRadialFillingCircle_coord,
      saddlePolarChart,revolutionRadial,revolutionAxis]

/-- Literal neck graph formula on the actual upper graph. -/
theorem completedSaddleAnnulusUpperGraph_neck
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L dInfinity : ℝ} (hA : 0 < A) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    (θ : ℝ) {v : ℝ} (hv : 0 < v) (hNear : B * v ^ 2 < B / L ^ 2)
    (hRN : A + B * v ^ 2 < RN) :
    completedSaddleAnnulusUpperGraph G e dInfinity
      (completedSaddleAnnulusPolarPoint (A + B * v ^ 2) θ) =
      (A + B * v ^ 2) • revolutionRadial θ + (2 * B * v) • revolutionAxis := by
  let y := completedSaddleAnnulusPolarPoint (A + B * v ^ 2) θ
  have hr : 0 < A + B * v ^ 2 := by positivity
  have hyRadius : planarRadius y = A + B * v ^ 2 :=
    completedSaddleAnnulusPolarPoint_radius hr θ
  have hOffset : 0 < planarRadius y - A := by rw [hyRadius]; nlinarith [mul_pos hB (sq_pos_of_pos hv)]
  have hyTarget : y ∈ e.target := by
    rw [hTarget]
    exact ⟨by linarith,by rwa [hyRadius]⟩
  have hHeight := completedSaddleAnnulusNeck_graph_height_resolved e hB hL hSource heG
    hInfinity hyTarget (by rw [hyRadius]; exact hr) hOffset (by rw [hyRadius]; linarith)
  have hQuot : (planarRadius y - A) / B = v ^ 2 := by
    rw [hyRadius]
    field_simp [hB.ne']
    <;> ring
  have hVertical : dInfinity - completedSaddleAnnulusGraphHeight G e y = 2 * B * v := by
    rw [hHeight,hQuot,Real.sqrt_sq hv.le]
    ring
  rw [completedSaddleAnnulusUpperGraph_polar]
  change (A + B * v ^ 2) • revolutionRadial θ +
    (dInfinity - completedSaddleAnnulusGraphHeight G e y) • revolutionAxis = _
  rw [hVertical]

/-- Literal northern parabolic graph formula, from the scalar quadratic
puncture collar. Height is measured from the same dInfinity. -/
theorem completedSaddleAnnulusUpperGraph_northern
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    (θ : ℝ) {t : ℝ} (ht : t < 0) (hAnear : A < RN + μ * t) (hNear : -t < ε) :
    completedSaddleAnnulusUpperGraph G e dInfinity
      (completedSaddleAnnulusPolarPoint (RN + μ * t) θ) =
      (RN + μ * t) • revolutionRadial θ +
        (dInfinity - d0 - μ * t ^ 2 / 2) • revolutionAxis := by
  let y := completedSaddleAnnulusPolarPoint (RN + μ * t) θ
  have hr : 0 < RN + μ * t := hA.trans hAnear
  have hyRadius : planarRadius y = RN + μ * t :=
    completedSaddleAnnulusPolarPoint_radius hr θ
  have hRadiusRN : planarRadius y < RN := by rw [hyRadius]; nlinarith [mul_neg_of_pos_of_neg hμ ht]
  have hyTarget : y ∈ e.target := by
    rw [hTarget]
    exact ⟨by rwa [hyRadius],hRadiusRN⟩
  have hHeight := completedSaddleAnnulusQuadratic_graph_height hμ hQuadratic e hSource heG
    hyTarget (by rw [hyRadius]; exact hr) (sub_pos.mpr hRadiusRN)
    (by rw [hyRadius]; nlinarith [mul_lt_mul_of_pos_left hNear hμ])
  have hVertical : dInfinity - completedSaddleAnnulusGraphHeight G e y =
      dInfinity - d0 - μ * t ^ 2 / 2 := by
    rw [hHeight,hyRadius]
    field_simp [hμ.ne']
    <;> ring
  rw [completedSaddleAnnulusUpperGraph_polar]
  change (RN + μ * t) • revolutionRadial θ +
    (dInfinity - completedSaddleAnnulusGraphHeight G e y) • revolutionAxis = _
  rw [hVertical]

theorem completedSaddleAnnulusNeckRealChart_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L dInfinity : ℝ} (hA : 0 < A) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {q : Coord} (hv : 0 < q 1) (hNear : B * q 1 ^ 2 < B / L ^ 2)
    (hRN : A + B * q 1 ^ 2 < RN) :
    completedSaddleAnnulusNeckRealChart G e A B dInfinity =ᶠ[𝓝 q]
      (fun z => (A + B * z 1 ^ 2) • revolutionRadial (z 0) +
        (2 * B * z 1) • revolutionAxis) := by
  have hV : IsOpen {z : Coord | 0 < z 1 ∧ B * z 1 ^ 2 < B / L ^ 2 ∧
      A + B * z 1 ^ 2 < RN} :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt (continuous_const.mul ((continuous_apply 1).pow 2)) continuous_const).inter
        (isOpen_lt (continuous_const.add (continuous_const.mul
          ((continuous_apply 1).pow 2))) continuous_const))
  filter_upwards [hV.mem_nhds (show q ∈ {z : Coord | 0 < z 1 ∧
    B * z 1 ^ 2 < B / L ^ 2 ∧ A + B * z 1 ^ 2 < RN} from ⟨hv,hNear,hRN⟩)] with z hz
  exact completedSaddleAnnulusUpperGraph_neck e hA hB hL hSource hTarget heG hInfinity
    (z 0) hz.1 hz.2.1 hz.2.2

theorem completedSaddleAnnulusNorthernRealChart_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ ε d0 dInfinity : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    {q : Coord} (ht : q 1 < 0) (hAnear : A < RN + μ * q 1) (hNear : -q 1 < ε) :
    completedSaddleAnnulusNorthernRealChart G e RN μ dInfinity =ᶠ[𝓝 q]
      (fun z => (RN + μ * z 1) • revolutionRadial (z 0) +
        (dInfinity - d0 - μ * z 1 ^ 2 / 2) • revolutionAxis) := by
  have hV : IsOpen {z : Coord | z 1 < 0 ∧ A < RN + μ * z 1 ∧ -z 1 < ε} :=
    (isOpen_lt (continuous_apply 1) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_const.add
        (continuous_const.mul (continuous_apply 1)))).inter
        (isOpen_lt (continuous_apply 1).neg continuous_const))
  filter_upwards [hV.mem_nhds (show q ∈ {z : Coord | z 1 < 0 ∧
    A < RN + μ * z 1 ∧ -z 1 < ε} from ⟨ht,hAnear,hNear⟩)] with z hz
  exact completedSaddleAnnulusUpperGraph_northern e hA hμ hSource hTarget heG hQuadratic
    (z 0) hz.1 hz.2.1 hz.2.2

end
end TightVer401

