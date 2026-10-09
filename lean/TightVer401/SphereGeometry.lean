import TightVer401.SurfaceMetric

/-! Round-sphere identities follow from the actual unit-length constraint
and its differentiated germs, then OpenAI's proved Gauss decomposition. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem sphere_differential_orthogonal {Q : Coord → Ambient} {U : Set Coord} {p : Coord}
    (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (v : Coord) :
    inner ℝ (fderiv ℝ Q p v) (Q p) = 0 := by
  have hd : DifferentiableAt ℝ Q p := ((hQ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (Q q) (Q q)) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hunit q hq
  have hi := fderiv_inner_apply ℝ hd hd v
  rw [he.fderiv_eq] at hi
  have hz : fderiv ℝ (fun _ : Coord => (1 : ℝ)) p = 0 := (hasFDerivAt_const (c := (1 : ℝ)) p).fderiv
  rw [hz] at hi
  simp only [ContinuousLinearMap.zero_apply, real_inner_comm (Q p)] at hi
  rw [real_inner_comm]
  linarith

theorem sphere_isUnitNormal {Q : Coord → Ambient} {U : Set Coord} {p : Coord}
    (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    IsUnitNormalAt Q (Q p) p :=
  ⟨hunit p hp, sphere_differential_orthogonal hQ hU hp hunit⟩

theorem sphere_secondFundamental {Q : Coord → Ambient} {U : Set Coord} {p : Coord}
    (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    secondFundamental Q (Q p) p = -inducedMetric Q p := by
  ext i j
  have hdQ : DifferentiableAt ℝ Q p := ((hQ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdj : DifferentiableAt ℝ (coordPartial j Q) p :=
    (((partial_contDiffOn hQ hU j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (coordPartial j Q q) (Q q)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact sphere_differential_orthogonal hQ hU hq hunit _
  have hi := fderiv_inner_apply ℝ hdj hdQ (Pi.single i (1 : ℝ) : Coord)
  rw [he.fderiv_eq] at hi
  have hz : fderiv ℝ (fun _ : Coord => (0 : ℝ)) p = 0 := (hasFDerivAt_const (c := (0 : ℝ)) p).fderiv
  rw [hz] at hi
  change 0 = inner ℝ (coordPartial j Q p) (coordPartial i Q p) +
    secondFundamental Q (Q p) p i j at hi
  change secondFundamental Q (Q p) p i j = -inner ℝ (coordPartial i Q p) (coordPartial j Q p)
  have hcomm := real_inner_comm (coordPartial j Q p) (coordPartial i Q p)
  linarith

theorem sphere_gauss_decomposition {g : MetricField} {Q : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (i j : Fin 2) :
    coordPartial i (coordPartial j Q) p =
      (∑ k, christoffel g k i j p • coordPartial k Q p) - g p i j • Q p := by
  have hr := normalResidual_eq_secondFundamental_smul hg hQ hU hp
    (sphere_isUnitNormal hQ.1 hU hp hunit) i j
  rw [sphere_secondFundamental hQ.1 hU hp hunit, inducedMetric_eq_of_isometric hQ hp] at hr
  change coordPartial i (coordPartial j Q) p -
    (∑ k, christoffel g k i j p • coordPartial k Q p) = (-g p i j) • Q p at hr
  rw [neg_smul] at hr
  exact sub_eq_iff_eq_add.mp hr |>.trans (by module)

end
end TightVer401
