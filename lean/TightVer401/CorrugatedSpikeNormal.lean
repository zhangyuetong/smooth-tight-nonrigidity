import TightVer401.CorrugatedSeedFrameSetup

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem corrugatedSeedArcInverse_nat_cell {N : ℝ} (hN : 1 < N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap N)
    (n : ℕ) (r : ℝ) :
    e.symm (r + (n : ℝ) * corrugatedSeedArcCell N) =
      e.symm r + (n : ℝ) * corrugatedSeedCell N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc,
      corrugatedSeedArcInverse_cell hN e he, ih]
    ring

/-- The actual cell arclength inverse produces an embedded, positively oriented
unit-speed spherical normal on the entire N-cell circle. -/
theorem corrugatedSeed_spike_normal {N : ℕ} (hN : 2 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm)
    (hi : ∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r) :
    let L := (N : ℝ) * corrugatedSeedArcCell (N : ℝ)
    let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
    0 < L ∧ ContDiff ℝ ∞ ζ ∧ Function.Periodic ζ L ∧ Set.InjOn ζ (Ico 0 L) ∧
      (∀ r, inner ℝ (ζ r) (ζ r) = 1) ∧
      (∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) ∧ (∀ r, 0 < ζ r 2) := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNz : N ≠ 0 := by omega
  have hNcell : (N : ℝ) * corrugatedSeedCell (N : ℝ) = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  have hunit := corrugatedSeed_arclength_unit_frame hNr hψ hi
  refine ⟨mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNz)) (corrugatedSeedArcCell_pos hNr),
    (corrugatedSeedSphere_contDiff (N : ℝ)).comp hψ, ?_, ?_, hunit.1, hunit.2, ?_⟩
  · intro r
    change corrugatedSeedSphere (N : ℝ)
      (e.symm (r + (N : ℝ) * corrugatedSeedArcCell (N : ℝ))) =
      corrugatedSeedSphere (N : ℝ) (e.symm r)
    rw [corrugatedSeedArcInverse_nat_cell hNr e he, hNcell, corrugatedSeedSphere_periodic hN]
  · have hj := normalLoop_arclength_reparameterized_injective
      (corrugatedSeedSphericalSpeed_contDiff hNr).continuous
      (corrugatedSeedSphericalSpeed_pos hNr) e he (corrugatedSeedSphere_injOn hNr)
    rw [show rawPrimitive (corrugatedSeedSphericalSpeed (N : ℝ)) (2 * Real.pi) =
      (N : ℝ) * corrugatedSeedArcCell (N : ℝ) from corrugatedSeedArcMap_full_period hN] at hj
    exact hj
  · intro r
    exact corrugatedSeedSphere_north (N : ℝ) (e.symm r)

end
end TightVer401
