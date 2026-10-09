import TightVer401.AngularDescentCharts

/-! Actual angular descent for data smooth only on its radial cylinder.
Both local argument charts evaluate the SAME periodic map within that cylinder;
no global extension or shrinking of the closed radius-one/radius-two band occurs. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Local scalar angular descent from an actual open radial cylinder. -/
theorem positiveExitSelected_angularDescentPotential_contDiffAt
    {W : Coord → ℝ} {R : Set ℝ} (hR : IsOpen R)
    (hW : ContDiffOn ℝ ∞ W {q : Coord | q 0 ∈ R})
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {p : Coord} (hp : 0 < planarRadius p) (hpR : planarRadius p ∈ R) :
    ContDiffAt ℝ ∞ (angularDescentPotential W) p := by
  have hU : IsOpen {q : Coord | q 0 ∈ R} := hR.preimage (continuous_apply 0)
  have hWlocal (theta : ℝ) : ContDiffAt ℝ ∞ W (![planarRadius p, theta] : Coord) := by
    have hm : (![planarRadius p, theta] : Coord) ∈ {q : Coord | q 0 ∈ R} := hpR
    exact (hW _ hm).contDiffAt (hU.mem_nhds hm)
  have hs : 0 < p 0^2 + p 1^2 := Real.sqrt_pos.mp hp
  have hrad : ContDiffAt ℝ ∞ planarRadius p :=
    planarRadius_contDiffOn.contDiffAt
      ((isOpen_lt continuous_const ((continuous_apply 0).pow 2 |>.add
        ((continuous_apply 1).pow 2))).mem_nhds hs)
  have hz : angularDescentComplex p ≠ 0 :=
    norm_pos_iff.mp ((angularDescentComplex_norm p).symm ▸ hp)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hpos | hneg
  · apply (hWlocal _).comp p
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact hrad
    · exact (angularDescent_arg_contDiffAt hpos).comp p
        angularDescentComplex_contDiff.contDiffAt
  · have hang : ContDiffAt ℝ ∞ (fun q => Complex.arg (-angularDescentComplex q) - Real.pi) p :=
      ((angularDescent_arg_contDiffAt hneg).comp p
        angularDescentComplex_contDiff.neg.contDiffAt).sub contDiffAt_const
    have hlocal : ContDiffAt ℝ ∞
        (fun q => W ![planarRadius q, Complex.arg (-angularDescentComplex q) - Real.pi]) p := by
      apply (hWlocal _).comp p
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact hrad
      · exact hang
    apply hlocal.congr_of_eventuallyEq
    have hc : Continuous planarRadius :=
      Real.continuous_sqrt.comp ((continuous_apply 0).pow 2 |>.add
        ((continuous_apply 1).pow 2))
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hp] with q hq
    exact angularDescentPotential_neg_chart hperiod hq

/-- Coordinatewise descent retains the actual supplied vector-valued cylinder map. -/
def positiveExitSelectedAnnularDescent (W : Coord → Coord) (p : Coord) : Coord :=
  fun a => angularDescentPotential (fun q => W q a) p

def positiveExitSelectedAnnularDescentDomain (R : Set ℝ) : Set Coord :=
  {p | 0 < planarRadius p ∧ planarRadius p ∈ R}

theorem positiveExitSelectedAnnularDescentDomain_isOpen
    {R : Set ℝ} (hR : IsOpen R) : IsOpen (positiveExitSelectedAnnularDescentDomain R) := by
  have hc : Continuous planarRadius :=
    Real.continuous_sqrt.comp ((continuous_apply 0).pow 2 |>.add
      ((continuous_apply 1).pow 2))
  exact (isOpen_lt continuous_const hc).inter (hR.preimage hc)

/-- The descended vector map is smooth on the entire actual radial annulus. -/
theorem positiveExitSelectedAnnularDescent_contDiffOn
    {W : Coord → Coord} {R : Set ℝ} (hR : IsOpen R)
    (hW : ContDiffOn ℝ ∞ W {q : Coord | q 0 ∈ R})
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta]) :
    ContDiffOn ℝ ∞ (positiveExitSelectedAnnularDescent W)
      (positiveExitSelectedAnnularDescentDomain R) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro a
  exact positiveExitSelected_angularDescentPotential_contDiffAt hR
    ((contDiffOn_pi.mp hW) a)
    (fun r theta => congrArg (fun v : Coord => v a) (hperiod r theta)) hp.1 hp.2

/-- Descent reproduces the SAME map on every positive-radius polar representative. -/
theorem positiveExitSelectedAnnularDescent_polar
    {W : Coord → Coord}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    positiveExitSelectedAnnularDescent W (saddlePolarChart q) = W q := by
  ext a
  exact angularDescentPotential_polar
    (fun r theta => congrArg (fun v : Coord => v a) (hperiod r theta)) hq

/-- If the radial cylinder contains radius one through radius two, the
smooth descended domain contains the FULL required closed source band. -/
theorem positiveExitSelectedAnnularDescentDomain_closed_band
    {R : Set ℝ} (hband : Icc (1 : ℝ) 2 ⊆ R) :
    {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆
      positiveExitSelectedAnnularDescentDomain R := by
  intro p hp
  exact ⟨lt_of_lt_of_le zero_lt_one hp.1, hband hp⟩

end
end TightVer401
