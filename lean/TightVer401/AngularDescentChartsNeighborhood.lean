import TightVer401.AngularDescentCharts

/-! Explicit open branch neighborhoods for the constructed Cartesian descent.
This adapter reuses the checked local logarithm-chart smoothness proof. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every punctured Cartesian point has an open neighborhood on which the
potential equals one actual smooth angle-branch expression. The neighborhood
lies in the positive-radius domain; no regularity at the origin is asserted. -/
theorem angularDescentPotential_exists_branch_neighborhood
    {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {p : Coord} (hp : 0 < planarRadius p) :
    ∃ U : Set Coord, ∃ G : Coord → ℝ,
      IsOpen U ∧ p ∈ U ∧ U ⊆ {q | 0 < planarRadius q} ∧
      ContDiffOn ℝ ∞ G U ∧ Set.EqOn (angularDescentPotential W) G U ∧
      (G = (fun q => W ![planarRadius q, Complex.arg (angularDescentComplex q)]) ∨
        G = (fun q => W ![planarRadius q,
          Complex.arg (-angularDescentComplex q) - Real.pi])) := by
  have hopen : IsOpen {q : Coord | 0 < planarRadius q} :=
    isOpen_lt continuous_const (Real.continuous_sqrt.comp
      ((continuous_apply 0).pow 2 |>.add ((continuous_apply 1).pow 2)))
  have hlocal (U : Set Coord) (hU : U ⊆ {q | 0 < planarRadius q}) :
      ContDiffOn ℝ ∞ (angularDescentPotential W) U := by
    intro q hq
    exact (angularDescentPotential_contDiffAt hW hperiod (hU hq)).contDiffWithinAt
  have hz : angularDescentComplex p ≠ 0 :=
    norm_pos_iff.mp ((angularDescentComplex_norm p).symm ▸ hp)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hpos | hneg
  · let U : Set Coord := {q | 0 < planarRadius q} ∩
        angularDescentComplex ⁻¹' Complex.slitPlane
    have hU : U ⊆ {q | 0 < planarRadius q} := fun _ hq => hq.1
    refine ⟨U, angularDescentPotential W,
      hopen.inter (Complex.isOpen_slitPlane.preimage
        angularDescentComplex_contDiff.continuous),
      ⟨hp, hpos⟩, hU, hlocal U hU, ?_, Or.inl rfl⟩
    intro q hq
    rfl
  · let U : Set Coord := {q | 0 < planarRadius q} ∩
        (fun q => -angularDescentComplex q) ⁻¹' Complex.slitPlane
    let G : Coord → ℝ := fun q =>
      W ![planarRadius q, Complex.arg (-angularDescentComplex q) - Real.pi]
    have hU : U ⊆ {q | 0 < planarRadius q} := fun _ hq => hq.1
    have heq : Set.EqOn (angularDescentPotential W) G U := by
      intro q hq
      exact angularDescentPotential_neg_chart hperiod hq.1
    have hG : ContDiffOn ℝ ∞ G U := (hlocal U hU).congr
      (fun q hq => (heq hq).symm)
    exact ⟨U, G,
      hopen.inter (Complex.isOpen_slitPlane.preimage
        angularDescentComplex_contDiff.continuous.neg),
      ⟨hp, hneg⟩, hU, hG, heq, Or.inr rfl⟩

end
end TightVer401
