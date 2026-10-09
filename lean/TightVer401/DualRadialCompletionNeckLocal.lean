import TightVer401.DualRadialCompletionNeckLegendre

/-! Local inverse Legendre compatibility is constructed from an ordinary exact
neck collar, independently of global annular degree or completion. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Actual neck derivative signs transfer from the retained open scalar germ. -/
theorem dualRadialCompletion_neck_collar_signs {f : ℝ → ℝ} {a B C c : ℝ}
    (hB : 0 < B) (heq : EqOn f (dualRadialNeck C B a) (Ioo a c))
    {r : ℝ} (hr : r ∈ Ioo a c) :
    0 < deriv f r ∧ deriv (deriv f) r < 0 := by
  have hg : f =ᶠ[𝓝 r] dualRadialNeck C B a := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    exact heq hx
  rw [hg.deriv.deriv_eq, hg.deriv_eq]
  exact dualRadialNeck_strict_derivative_signs C a hB hr.1

/-- Actual Cartesian saddle sign follows from the neck germ; it is not an input. -/
theorem dualRadialCompletion_neck_collar_hessian_det_neg {f : ℝ → ℝ}
    {a B C c : ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c)) (hB : 0 < B)
    (heq : EqOn f (dualRadialNeck C B a) (Ioo a c)) {p : Coord}
    (hp : p ∈ radialPlanarDomain (Ioo a c)) :
    (planarHessian (radialPlanarPotential f) p).det < 0 := by
  have hs := dualRadialCompletion_neck_collar_signs hB heq hp.2
  exact radialPlanarPotential_hessian_det_neg hf isOpen_Ioo hp
    (mul_neg_of_pos_of_neg hs.1 hs.2)

/-- An actual smooth local gradient inverse and exact terminal dual germ are
constructed from an ordinary smooth scalar neck collar. -/
theorem exists_dualRadialCompletion_neck_local_legendre {f : ℝ → ℝ}
    {a B C c : ℝ} (ha : 0 < a) (hB : 0 < B) (hac : a < c)
    (hf : ContDiffOn ℝ ∞ f (Ioo a c))
    (heq : EqOn f (dualRadialNeck C B a) (Ioo a c)) {p : Coord}
    (hp : p ∈ radialPlanarDomain (Ioo a c)) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ radialPlanarDomain (Ioo a c) ∧
      (e : Coord → Coord) = planarGradient (radialPlanarPotential f) ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (planarLegendre (radialPlanarPotential f) e) e.target ∧
      EqOn (planarLegendre (radialPlanarPotential f) e)
        (radialPlanarPotential (dualRadialNeckLegendreGerm a B C)) e.target ∧
      ∀ y ∈ e.target, planarLegendre (radialPlanarPotential f) e =ᶠ[𝓝 y]
        radialPlanarPotential (dualRadialNeckLegendreGerm a B C) := by
  obtain ⟨e, hep, hes, hegradient, hi⟩ := planarGradient_exists_smooth_local_inverse
    (radialPlanarPotential_contDiffOn hf) (radialPlanarDomain_isOpen isOpen_Ioo)
    (fun q hq => (dualRadialCompletion_neck_collar_hessian_det_neg hf hB heq hq).ne) hp
  have hgradient : ∀ q ∈ e.source,
      e q = planarGradient (radialPlanarPotential f) q := fun q _ => congrFun hegradient q
  exact ⟨e, hep, hes, hegradient, hi,
    planarLegendre_contDiffOn e ((radialPlanarPotential_contDiffOn hf).mono hes) hi,
    dualRadialCompletionNeckLegendre_eqOn ha hB hac hf heq e hes hgradient,
    fun _ hy => dualRadialCompletionNeckLegendre_germ ha hB hac hf heq e hes hgradient hy⟩
end
end TightVer401
