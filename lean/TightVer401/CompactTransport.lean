import TightVer401.CharacteristicTransport
import Mathlib.Topology.MetricSpace.Bounded

/-! The compact-support obstruction for translation holonomy, proved for
actual functions and their topological supports. This will be applied to the
transverse transport coordinate in the supported-kernel classification. -/
namespace TightVer401
noncomputable section

theorem period_zero_of_nonzero_compact_support
    {f : ℝ → ℝ} {I : ℝ} (hf : HasCompactSupport f)
    (hperiod : Function.Periodic f I) (hne : f ≠ 0) : I = 0 := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra! hn
    apply hne
    funext x
    exact hn x
  obtain ⟨x, hx⟩ := hex
  let r : ℕ → ℝ := fun n => x + n * I
  have hstep (n) : r (n + 1) = r n + I := by dsimp [r]; push_cast; ring
  have hvalue (n) : f (r n) = f x := by
    induction n with
    | zero => simp [r]
    | succ n ih => rw [hstep, hperiod, ih]
  have hmem (n) : r n ∈ tsupport f := subset_closure (by
    change f (r n) ≠ 0
    rw [hvalue]
    exact hx)
  obtain ⟨C, hC⟩ := hf.isBounded.subset_closedBall (0 : ℝ)
  apply bounded_additive_orbit_period_zero hstep
  intro n
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hC (hmem n)

end
end TightVer401
