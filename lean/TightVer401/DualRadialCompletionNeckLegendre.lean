import TightVer401.DualRadialNeckGradientEscape
import TightVer401.PlanarLegendre

/-! Transfer of an actual retained scalar neck collar through an actual local gradient inverse. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem completionNeck_deriv_eq {a B c C : ℝ} {f : ℝ → ℝ}
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c)) {r : ℝ} (hr : r ∈ Ioo a c) :
    deriv f r = deriv (dualRadialNeck C B a) r := by
  have he : f =ᶠ[𝓝 r] dualRadialNeck C B a := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact hneck ht
  exact he.deriv_eq

private theorem completionNeck_target_slope_eq {a B c C : ℝ} (hB : 0 < B)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c))
    (e : OpenPartialHomeomorph Coord Coord)
    (hsource : e.source ⊆ radialPlanarDomain (Ioo a c))
    (hgradient : ∀ x ∈ e.source, e x = planarGradient (radialPlanarPotential f) x)
    {y : Coord} (hy : y ∈ e.target) :
    deriv (dualRadialNeck C B a) (planarRadius (e.symm y)) = planarRadius y := by
  have hx := hsource (e.map_target hy)
  have hd := completionNeck_deriv_eq hneck hx.2
  have hpositive : 0 < deriv f (planarRadius (e.symm y)) := by
    rw [hd]
    exact (dualRadialNeck_strict_derivative_signs C a hB hx.2.1).1
  have hforward : planarGradient (radialPlanarPotential f) (e.symm y) = y :=
    (hgradient _ (e.map_target hy)).symm.trans (e.right_inv hy)
  calc
    deriv (dualRadialNeck C B a) (planarRadius (e.symm y)) =
        deriv f (planarRadius (e.symm y)) := hd.symm
    _ = planarRadius (planarGradient (radialPlanarPotential f) (e.symm y)) := by
      rw [radialPlanarGradient_radius hf isOpen_Ioo hx, abs_of_pos hpositive]
    _ = planarRadius y := congrArg planarRadius hforward

/-- Positive target radius follows from the actual retained neck slope. -/
theorem dualRadialCompletionNeckLegendre_target_radius_pos {a B c C : ℝ}
    (_ha : 0 < a) (hB : 0 < B) (_hac : a < c)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c))
    (e : OpenPartialHomeomorph Coord Coord)
    (hsource : e.source ⊆ radialPlanarDomain (Ioo a c))
    (hgradient : ∀ x ∈ e.source, e x = planarGradient (radialPlanarPotential f) x)
    {y : Coord} (hy : y ∈ e.target) : 0 < planarRadius y := by
  have hx := hsource (e.map_target hy)
  rw [← completionNeck_target_slope_eq hB hf hneck e hsource hgradient hy]
  exact (dualRadialNeck_strict_derivative_signs C a hB hx.2.1).1

/-- The source radius is derived from the actual gradient, rather than prescribed as an inverse input. -/
theorem dualRadialCompletionNeckLegendre_inverse_radius {a B c C : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hac : a < c)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c))
    (e : OpenPartialHomeomorph Coord Coord)
    (hsource : e.source ⊆ radialPlanarDomain (Ioo a c))
    (hgradient : ∀ x ∈ e.source, e x = planarGradient (radialPlanarPotential f) x)
    {y : Coord} (hy : y ∈ e.target) :
    planarRadius (e.symm y) = dualRadialNeckInverseRadius a B (planarRadius y) := by
  have hx := hsource (e.map_target hy)
  exact dualRadialNeck_radius_of_derivative C a hB hx.2.1
    (dualRadialCompletionNeckLegendre_target_radius_pos ha hB hac hf hneck e hsource hgradient hy)
    (completionNeck_target_slope_eq hB hf hneck e hsource hgradient hy)

/-- On the actual inverse target the literal Legendre transform is the existing radial neck dual. -/
theorem dualRadialCompletionNeckLegendre_eqOn {a B c C : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hac : a < c)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c))
    (e : OpenPartialHomeomorph Coord Coord)
    (hsource : e.source ⊆ radialPlanarDomain (Ioo a c))
    (hgradient : ∀ x ∈ e.source, e x = planarGradient (radialPlanarPotential f) x) :
    EqOn (planarLegendre (radialPlanarPotential f) e)
      (radialPlanarPotential (dualRadialNeckLegendreGerm a B C)) e.target := by
  intro y hy
  let q : Coord := e.symm y
  have hqsource : q ∈ e.source := e.map_target hy
  have hq := hsource hqsource
  have hqpos : 0 < planarRadius q := Real.sqrt_pos.mpr hq.1
  have hypos := dualRadialCompletionNeckLegendre_target_radius_pos
    ha hB hac hf hneck e hsource hgradient hy
  have hradius := dualRadialCompletionNeckLegendre_inverse_radius
    ha hB hac hf hneck e hsource hgradient hy
  have hslope : deriv f (planarRadius q) = planarRadius y :=
    (completionNeck_deriv_eq hneck hq.2).trans
      (completionNeck_target_slope_eq hB hf hneck e hsource hgradient hy)
  have hforward : planarGradient (radialPlanarPotential f) q = y :=
    (hgradient q hqsource).symm.trans (e.right_inv hy)
  have hcoordinate (i : Fin 2) : y i = planarRadius y * q i / planarRadius q := by
    calc
      y i = planarGradient (radialPlanarPotential f) q i := congrFun hforward.symm i
      _ = planarRadius y * q i / planarRadius q := by
        change coordPartial i (radialPlanarPotential f) q = _
        rw [radialPlanarPotential_coordPartial hf isOpen_Ioo hq, hslope]
  have hdot : q ⬝ᵥ y = planarRadius y * planarRadius q := by
    simp only [dotProduct, Fin.sum_univ_two]
    rw [hcoordinate 0, hcoordinate 1]
    calc
      _ = planarRadius y * (q 0 ^ 2 + q 1 ^ 2) / planarRadius q := by ring
      _ = planarRadius y * planarRadius q := by
        rw [← planarRadius_sq q]
        field_simp [hqpos.ne'] <;> ring
  change q ⬝ᵥ y - f (planarRadius q) = dualRadialNeckLegendreGerm a B C (planarRadius y)
  rw [hdot, hneck hq.2, hradius]
  simpa only [dualRadialNeckLegendreGerm] using dualRadialNeck_inverse_legendre C a hB hypos

/-- Equality on the actual open inverse target is equality of ordinary ambient germs there. -/
theorem dualRadialCompletionNeckLegendre_germ {a B c C : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hac : a < c)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (hneck : EqOn f (dualRadialNeck C B a) (Ioo a c))
    (e : OpenPartialHomeomorph Coord Coord)
    (hsource : e.source ⊆ radialPlanarDomain (Ioo a c))
    (hgradient : ∀ x ∈ e.source, e x = planarGradient (radialPlanarPotential f) x)
    {y : Coord} (hy : y ∈ e.target) :
    planarLegendre (radialPlanarPotential f) e =ᶠ[𝓝 y]
      radialPlanarPotential (dualRadialNeckLegendreGerm a B C) := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact dualRadialCompletionNeckLegendre_eqOn ha hB hac hf hneck e hsource hgradient hz

end
end TightVer401

