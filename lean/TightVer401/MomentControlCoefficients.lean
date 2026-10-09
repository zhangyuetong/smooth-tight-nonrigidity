import TightVer401.MomentControlSamples

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

def controlMomentBasis {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)} {S : Set ℝ}
    (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) :
    Module.Basis (Fin (Module.finrank ℝ (momentSampleSpan f S))) ℝ (momentSampleSpan f S) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun j => ⟨realControlMoment f (ψ j), realControlMoment_mem_span (hψ j)⟩)
    (LinearIndependent.of_comp (momentSampleSpan f S).subtype hLI) (by simp)

theorem controlMomentBasis_apply {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)} {S : Set ℝ}
    (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) (j) :
    (controlMomentBasis ψ hψ hLI j : EuclideanSpace ℝ (Fin m)) = realControlMoment f (ψ j) := by
  simp [controlMomentBasis, basisOfLinearIndependentOfCardEqFinrank']

def controlMomentCoordinates {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)} {S : Set ℝ}
    (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) :
    (momentSampleSpan f S) ≃L[ℝ] (Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ) :=
  (controlMomentBasis ψ hψ hLI).equivFunL

theorem controlMomentCoordinates_reconstruct {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {S : Set ℝ} (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) (u : momentSampleSpan f S) :
    ∑ j, controlMomentCoordinates ψ hψ hLI u j • realControlMoment f (ψ j) =
      (u : EuclideanSpace ℝ (Fin m)) := by
  have hs := (controlMomentBasis ψ hψ hLI).sum_equivFun u
  have hval := congrArg (fun v : momentSampleSpan f S => (v : EuclideanSpace ℝ (Fin m))) hs
  simpa only [Submodule.coe_sum, Submodule.coe_smul, controlMomentBasis_apply,
    controlMomentCoordinates, Module.Basis.equivFunL_apply, Module.Basis.equivFun_apply] using hval

theorem controlMomentCoordinates_fixed_bound {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {S : Set ℝ} (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : momentSampleSpan f S,
      (∀ j, |controlMomentCoordinates ψ hψ hLI u j| ≤ C * ‖u‖) ∧
      (∑ j, |controlMomentCoordinates ψ hψ hLI u j|) ≤ C * ‖u‖ := by
  let d := Module.finrank ℝ (momentSampleSpan f S)
  let A := (controlMomentCoordinates ψ hψ hLI).toContinuousLinearMap
  let C := ((d : ℝ) + 1) * ‖A‖ + 1
  have hD : 0 ≤ ‖A‖ := A.opNorm_nonneg
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : ‖A‖ ≤ C := by dsimp [C]; nlinarith
  have hdDC : (d : ℝ) * ‖A‖ ≤ C := by dsimp [C]; nlinarith
  have hraw (u : momentSampleSpan f S) (j) :
      |controlMomentCoordinates ψ hψ hLI u j| ≤ ‖A‖ * ‖u‖ := by
    change |A u j| ≤ _
    calc
      |A u j| = ‖A u j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A u‖ := norm_le_pi_norm _ j
      _ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
  refine ⟨C, hC, fun u => ⟨?_, ?_⟩⟩
  · intro j
    exact (hraw u j).trans (mul_le_mul_of_nonneg_right hDC (norm_nonneg u))
  · calc
      (∑ j, |controlMomentCoordinates ψ hψ hLI u j|) ≤ ∑ j : Fin d, ‖A‖ * ‖u‖ :=
        Finset.sum_le_sum (fun j _ => hraw u j)
      _ = ((d : ℝ) * ‖A‖) * ‖u‖ := by simp; ring
      _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right hdDC (norm_nonneg u)

theorem controlMoment_interval_eq_real {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {L : ℝ} {ψ : ℝ → ℝ} (hψ : Function.support ψ ⊆ Ioo 0 L) :
    (∫ x in 0..L, ψ x • f x) = realControlMoment f ψ := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hxψ : ψ x ≠ 0 := by
    intro hz
    apply hx
    simp [hz]
  exact Ioo_subset_Ioc_self (hψ hxψ)

theorem controlMoment_interval_mem_span {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {L : ℝ} {ψ : ℝ → ℝ} (hψ : Function.support ψ ⊆ Ioo 0 L) :
    (∫ x in 0..L, ψ x • f x) ∈ momentSampleSpan f (Ioo 0 L) := by
  rw [controlMoment_interval_eq_real hψ]
  exact realControlMoment_mem_span hψ

theorem exists_bounded_interval_moment_coordinates {m : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin m)} {L : ℝ}
    (ψ : Fin (Module.finrank ℝ (momentSampleSpan f (Ioo 0 L))) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ Ioo 0 L)
    (hLI : LinearIndependent ℝ (fun j => ∫ x in 0..L, ψ j x • f x)) :
    ∃ T : (momentSampleSpan f (Ioo 0 L)) ≃L[ℝ]
        (Fin (Module.finrank ℝ (momentSampleSpan f (Ioo 0 L))) → ℝ),
      ∃ C : ℝ, 0 < C ∧ ∀ u : momentSampleSpan f (Ioo 0 L),
        (∑ j, T u j • (∫ x in 0..L, ψ j x • f x)) = (u : EuclideanSpace ℝ (Fin m)) ∧
        (∀ j, |T u j| ≤ C * ‖u‖) ∧ (∑ j, |T u j|) ≤ C * ‖u‖ := by
  have hMoment (j) := controlMoment_interval_eq_real (f := f) (hψ j)
  have hLIreal : LinearIndependent ℝ (fun j => realControlMoment f (ψ j)) := by
    simpa only [hMoment] using hLI
  obtain ⟨C, hC, hbound⟩ := controlMomentCoordinates_fixed_bound ψ hψ hLIreal
  refine ⟨controlMomentCoordinates ψ hψ hLIreal, C, hC, fun u => ⟨?_, hbound u⟩⟩
  simpa only [hMoment] using controlMomentCoordinates_reconstruct ψ hψ hLIreal u

end
end TightVer401
