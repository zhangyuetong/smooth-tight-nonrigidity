import TightVer401.FermiPerturbationBounds

/-! The actual coordinate C2 budget controls the contract's operator norms.
The coordinate model has the supremum norm, so the comparison constant is one. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Expand a continuous linear map in the ordinary finite coordinate basis. -/
theorem positiveExit_finiteCoordinate_opNorm_le_sum
    {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ι → ℝ) →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) 
  intro x
  have hx : x = ∑ i, x i • (Pi.single i 1 : ι → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  have hLx : L x = ∑ i, x i • L (Pi.single i 1) := by
    calc
      L x = L (∑ i, x i • (Pi.single i 1 : ι → ℝ)) := congrArg L hx
      _ = ∑ i, x i • L (Pi.single i 1) := by simp
  rw [hLx]
  calc
    ‖∑ i, x i • L (Pi.single i 1)‖ ≤ ∑ i, ‖x i • L (Pi.single i 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖L (Pi.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i, ‖L (Pi.single i 1)‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm

/-- Actual second derivatives evaluated on coordinate vectors are the actual
iterated coordinate partials, with the same ordered indices. -/
theorem positiveExit_secondFDeriv_coordinate {J : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) (q : Coord) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ J) q (Pi.single i 1) (Pi.single j 1) =
      coordPartial i (coordPartial j J) q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ J) q :=
    (hJ.contDiffAt.fderiv_right (m := 1)
      (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).differentiableAt (by norm_num)
  have hEval : HasFDerivAt
      (fun x : Coord => fderiv ℝ J x (Pi.single j 1 : Coord))
      ((fderiv ℝ (fderiv ℝ J) q).flip (Pi.single j 1 : Coord)) q := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hd.hasFDerivAt.clm_apply (hasFDerivAt_const (c := (Pi.single j 1 : Coord)) q)
  change fderiv ℝ (fderiv ℝ J) q (Pi.single i 1) (Pi.single j 1) =
    fderiv ℝ (fun x : Coord => fderiv ℝ J x (Pi.single j 1 : Coord)) q (Pi.single i 1)
  rw [hEval.fderiv]
  rfl

/-- No budget rescaling is required to pass from the proved coordinate bounds
to the actual first and second Frechet derivative operator norms. -/
theorem positiveExit_operatorC2Size_le_coordinateC2Size {J : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) (q : Coord) :
    ‖J q‖ + ‖fderiv ℝ J q‖ + ‖fderiv ℝ (fderiv ℝ J) q‖ ≤
      fermiCoordinateC2Size J q := by
  have hfirst : ‖fderiv ℝ J q‖ ≤ ∑ i, ‖coordPartial i J q‖ := by
    simpa only [coordPartial] using
      positiveExit_finiteCoordinate_opNorm_le_sum (fderiv ℝ J q)
  have hsecond : ‖fderiv ℝ (fderiv ℝ J) q‖ ≤
      ∑ i, ∑ j, ‖coordPartial i (coordPartial j J) q‖ := by
    calc
      ‖fderiv ℝ (fderiv ℝ J) q‖ ≤
          ∑ i, ‖fderiv ℝ (fderiv ℝ J) q (Pi.single i 1)‖ :=
        positiveExit_finiteCoordinate_opNorm_le_sum _
      _ ≤ ∑ i, ∑ j, ‖fderiv ℝ (fderiv ℝ J) q (Pi.single i 1) (Pi.single j 1)‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact positiveExit_finiteCoordinate_opNorm_le_sum _
      _ = ∑ i, ∑ j, ‖coordPartial i (coordPartial j J) q‖ := by
        simp_rw [positiveExit_secondFDeriv_coordinate hJ]
  exact add_le_add (add_le_add (le_refl _) hfirst) hsecond

theorem positiveExit_operatorC2Size_lt_of_coordinateC2Size_lt {J : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) {q : Coord} {η : ℝ}
    (hη : fermiCoordinateC2Size J q < η) :
    ‖J q‖ + ‖fderiv ℝ J q‖ + ‖fderiv ℝ (fderiv ℝ J) q‖ < η :=
  lt_of_le_of_lt (positiveExit_operatorC2Size_le_coordinateC2Size hJ q) hη

end
end TightVer401
