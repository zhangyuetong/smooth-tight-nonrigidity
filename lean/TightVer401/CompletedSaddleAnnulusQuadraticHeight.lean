import TightVer401.CompletedSaddleAnnulusLegendreHeight
import TightVer401.DualRadialQuadraticGerm
import TightVer401.QuadraticRadialFillingBoundaryGerms
import TightVer401.QuadraticRadialFillingBoundary
import TightVer401.QuadraticFillerCartesianGradientAnnulusAlgebra

/-! Derive the actual outer graph-height germ from an actual quadratic scalar
puncture germ and its actual gradient inverse. Upstream completion existence
and boundary resolution are separate constructions. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusQuadraticInverse (RN μ : ℝ) (y : Coord) : Coord :=
  ((RN - planarRadius y) / (μ * planarRadius y)) • y

theorem completedSaddleAnnulusQuadratic_scalar_germ
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    {p : Coord} (hp : 0 < planarRadius p) (hpε : planarRadius p < ε) :
    G =ᶠ[𝓝 p] dualRadialQuadraticPotential (RN / μ) μ d₀ := by
  have hcoef : μ * (RN / μ) = RN := by field_simp [hμ.ne']
  filter_upwards [(quadraticRadialFilling_openAnnulus_isOpen 0 ε).mem_nhds
    (show p ∈ quadraticRadialFillingOpenAnnulus 0 ε from ⟨hp,hpε⟩)] with q hq
  change G q = μ * (RN / μ) * planarRadius q - μ / 2 * planarRadius q ^ 2 + d₀
  rw [hcoef,hLiteral q hq.1 hq.2]
  ring

theorem completedSaddleAnnulusQuadratic_gradient
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    {p : Coord} (hp : 0 < planarRadius p) (hpε : planarRadius p < ε) :
    planarGradient G p = ((RN - μ * planarRadius p) / planarRadius p) • p := by
  rw [quadraticRadialFilling_gradient_eq_of_germ
    (completedSaddleAnnulusQuadratic_scalar_germ hμ hLiteral hp hpε)]
  have hcoef : μ * (RN / μ) = RN := by field_simp [hμ.ne']
  have hpSq : 0 < p 0 ^ 2 + p 1 ^ 2 := Real.sqrt_pos.mp hp
  ext i
  change coordPartial i (dualRadialQuadraticPotential (RN / μ) μ d₀) p =
    ((RN - μ * planarRadius p) / planarRadius p) * p i
  rw [dualRadialQuadraticPotential, radialPlanarPotential_coordPartial
    (dualRadialQuadraticProfile_contDiff (RN / μ) μ d₀).contDiffOn isOpen_univ
    (show p ∈ radialPlanarDomain univ from ⟨hpSq,mem_univ _⟩),
    dualRadialQuadraticProfile_deriv,hcoef]
  ring

theorem completedSaddleAnnulusQuadratic_support
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    {p : Coord} (hp : 0 < planarRadius p) (hpε : planarRadius p < ε) :
    planarSupportMap G p = WithLp.toLp 2
      ![(RN - μ * planarRadius p) * p 0 / planarRadius p,
        (RN - μ * planarRadius p) * p 1 / planarRadius p,
        d₀ + μ / 2 * planarRadius p ^ 2] := by
  have hg := completedSaddleAnnulusQuadratic_scalar_germ hμ hLiteral hp hpε
  have hgrad := quadraticRadialFilling_gradient_eq_of_germ hg
  have h0 := congrFun hgrad 0
  have h1 := congrFun hgrad 1
  change coordPartial 0 G p = coordPartial 0 (dualRadialQuadraticPotential (RN / μ) μ d₀) p at h0
  change coordPartial 1 G p = coordPartial 1 (dualRadialQuadraticPotential (RN / μ) μ d₀) p at h1
  have hmap : planarSupportMap G p =
      planarSupportMap (dualRadialQuadraticPotential (RN / μ) μ d₀) p := by
    unfold planarSupportMap
    rw [hg.eq_of_nhds,h0,h1]
  rw [hmap,dualRadialQuadraticPotential_supportMap (Real.sqrt_pos.mp hp)]
  have hcoef : μ * (RN / μ) = RN := by field_simp [hμ.ne']
  rw [hcoef]

theorem completedSaddleAnnulusQuadratic_inverse_radius
    {RN μ : ℝ} (hμ : 0 < μ) {y : Coord} (hy : 0 < planarRadius y)
    (hRN : planarRadius y < RN) :
    planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) =
      (RN - planarRadius y) / μ := by
  unfold completedSaddleAnnulusQuadraticInverse
  rw [quadraticFillerCartesianGradient_radius_smul
    (div_nonneg (sub_nonneg.mpr hRN.le) (mul_pos hμ hy).le)]
  field_simp [hμ.ne',hy.ne']

theorem completedSaddleAnnulusQuadratic_inverse_gradient
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    {y : Coord} (hy : 0 < planarRadius y)
    (hgap : 0 < RN - planarRadius y) (hclose : RN - planarRadius y < μ * ε) :
    planarGradient G (completedSaddleAnnulusQuadraticInverse RN μ y) = y := by
  have hr := completedSaddleAnnulusQuadratic_inverse_radius (RN := RN) hμ hy (by linarith)
  have hp : 0 < planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) := by
    rw [hr]
    exact div_pos hgap hμ
  have hpε : planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) < ε := by
    rw [hr]
    exact (div_lt_iff₀ hμ).mpr (by simpa [mul_comm] using hclose)
  rw [completedSaddleAnnulusQuadratic_gradient hμ hLiteral hp hpε,hr]
  unfold completedSaddleAnnulusQuadraticInverse
  rw [smul_smul]
  have hcoef : ((RN - μ * ((RN - planarRadius y) / μ)) /
      ((RN - planarRadius y) / μ)) * ((RN - planarRadius y) /
        (μ * planarRadius y)) = 1 := by
    field_simp [hμ.ne',hy.ne',hgap.ne']
    ring
  rw [hcoef,one_smul]

theorem completedSaddleAnnulusQuadratic_actual_inverse
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    (e : OpenPartialHomeomorph Coord Coord)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {y : Coord} (hy : 0 < planarRadius y)
    (hgap : 0 < RN - planarRadius y) (hclose : RN - planarRadius y < μ * ε) :
    e.symm y = completedSaddleAnnulusQuadraticInverse RN μ y := by
  have hr := completedSaddleAnnulusQuadratic_inverse_radius (RN := RN) hμ hy (by linarith)
  have hp : completedSaddleAnnulusQuadraticInverse RN μ y ∈ e.source := by
    rw [hSource]
    change 0 < planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y)
    rw [hr]
    exact div_pos hgap hμ
  have he : e (completedSaddleAnnulusQuadraticInverse RN μ y) = y := by
    rw [heG _ hp]
    exact completedSaddleAnnulusQuadratic_inverse_gradient hμ hLiteral hy hgap hclose
  calc
    e.symm y = e.symm (e (completedSaddleAnnulusQuadraticInverse RN μ y)) :=
      congrArg e.symm he.symm
    _ = completedSaddleAnnulusQuadraticInverse RN μ y := e.left_inv hp

theorem completedSaddleAnnulusQuadratic_graph_height
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    (e : OpenPartialHomeomorph Coord Coord)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {y : Coord} (hyTarget : y ∈ e.target) (hy : 0 < planarRadius y)
    (hgap : 0 < RN - planarRadius y) (hclose : RN - planarRadius y < μ * ε) :
    completedSaddleAnnulusGraphHeight G e y =
      d₀ + (RN - planarRadius y) ^ 2 / (2 * μ) := by
  have hr := completedSaddleAnnulusQuadratic_inverse_radius (RN := RN) hμ hy (by linarith)
  have hp : 0 < planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) := by
    rw [hr]
    exact div_pos hgap hμ
  have hpε : planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) < ε := by
    rw [hr]
    exact (div_lt_iff₀ hμ).mpr (by simpa [mul_comm] using hclose)
  rw [completedSaddleAnnulusGraphHeight_support e heG hyTarget,
    completedSaddleAnnulusQuadratic_actual_inverse hμ hLiteral e hSource heG hy hgap hclose,
    completedSaddleAnnulusQuadratic_support hμ hLiteral hp hpε]
  change d₀ + μ / 2 * planarRadius (completedSaddleAnnulusQuadraticInverse RN μ y) ^ 2 = _
  rw [hr]
  field_simp [hμ.ne']
  <;> ring


theorem completedSaddleAnnulusQuadratic_graph_height_germ
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hμ : 0 < μ)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    (e : OpenPartialHomeomorph Coord Coord)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {y : Coord} (hyTarget : y ∈ e.target) (hy : 0 < planarRadius y)
    (hgap : 0 < RN - planarRadius y) (hclose : RN - planarRadius y < μ * ε) :
    completedSaddleAnnulusGraphHeight G e =ᶠ[𝓝 y]
      (fun z => d₀ + (RN - planarRadius z) ^ 2 / (2 * μ)) := by
  have hV : IsOpen (quadraticRadialFillingOpenAnnulus 0 RN ∩
      {z : Coord | RN - μ * ε < planarRadius z}) :=
    (quadraticRadialFilling_openAnnulus_isOpen 0 RN).inter
      (isOpen_lt continuous_const quadraticRadialFilling_radius_continuous)
  have hyV : y ∈ quadraticRadialFillingOpenAnnulus 0 RN ∩
      {z : Coord | RN - μ * ε < planarRadius z} :=
    ⟨⟨hy,by linarith⟩,show RN - μ * ε < planarRadius y by linarith⟩
  filter_upwards [e.open_target.mem_nhds hyTarget,hV.mem_nhds hyV] with z hz hzV
  exact completedSaddleAnnulusQuadratic_graph_height hμ hLiteral e hSource heG hz
    hzV.1.1 (by linarith [hzV.1.2])
    (by have hlow : RN - μ * ε < planarRadius z := hzV.2; linarith)
/-- A concrete positive width converts an ordinary target outer collar into
all inequalities required by the derived actual height formula. -/
theorem completedSaddleAnnulusQuadratic_outer_collar
    {G : Coord → ℝ} {RN μ ε d₀ : ℝ} (hRN : 0 < RN) (hμ : 0 < μ) (hε : 0 < ε)
    (hLiteral : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d₀)
    (e : OpenPartialHomeomorph Coord Coord)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ e.target,
      RN - δ < planarRadius y → planarRadius y < RN →
      completedSaddleAnnulusGraphHeight G e y =
        d₀ + (RN - planarRadius y) ^ 2 / (2 * μ) := by
  refine ⟨min (RN/2) (μ*ε/2), lt_min (by positivity) (by positivity), ?_⟩
  intro y hyTarget hlow hhigh
  have hδR : min (RN/2) (μ*ε/2) ≤ RN/2 := min_le_left _ _
  have hδε : min (RN/2) (μ*ε/2) ≤ μ*ε/2 := min_le_right _ _
  apply completedSaddleAnnulusQuadratic_graph_height hμ hLiteral e hSource heG hyTarget
  · linarith
  · linarith
  · nlinarith [mul_pos hμ hε]

end
end TightVer401

