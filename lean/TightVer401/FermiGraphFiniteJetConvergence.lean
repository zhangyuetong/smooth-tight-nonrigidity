import TightVer401.FermiGraphSmoothConvergence

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem fermiGraph_uniform_finite_jet_convergence {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hv : ContDiff ℝ ∞ v) (n : ℕ) {P η : ℝ} (hη : 0 < η) :
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ j ≤ n, ∀ r ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ j (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
        iteratedFDeriv ℝ j ζ r‖ < η := by
  induction n with
  | zero =>
    obtain ⟨e,he,hbound⟩ := fermiGraph_uniform_smooth_convergence hζ hv 0 (P := P) hη
    refine ⟨e,he,fun δ hδ j hj r hr => ?_⟩
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact hbound δ hδ r hr
  | succ n ih =>
    obtain ⟨e,he,hbound⟩ := ih
    obtain ⟨e',he',hbound'⟩ := fermiGraph_uniform_smooth_convergence hζ hv (n+1) (P := P) hη
    refine ⟨min e e',lt_min he he',fun δ hδ j hj r hr => ?_⟩
    by_cases hjn : j ≤ n
    · exact hbound δ (hδ.trans_le (min_le_left _ _)) j hjn r hr
    · have heq : j = n+1 := by omega
      subst j
      exact hbound' δ (hδ.trans_le (min_le_right _ _)) r hr

end
end TightVer401
