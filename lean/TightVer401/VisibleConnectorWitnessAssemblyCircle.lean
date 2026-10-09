import TightVer401.VisibleConnectorContract
import TightVer401.QuadraticRadialFillingBoundaryRadial

/-! The literal full-turn terminal gradient covers the entire physical circle.
Only continuity and the actual phase shift are used, with no filling choice. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped Topology Matrix

/-- Continuous one-turn phase drift reaches every real angle. -/
theorem visibleConnectorWitnessAssembly_phase_surjective
    {theta : ℝ → ℝ} {L : ℝ} (hTheta : Continuous theta)
    (hShift : ∀ s, theta (s+L) = theta s+2*Real.pi) : Surjective theta := by
  have hnat : ∀ n : ℕ, ∀ s : ℝ,
      theta (s+(n:ℝ)*L) = theta s+(n:ℝ)*(2*Real.pi) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,← add_assoc,hShift,ih]
      ring
  intro y
  obtain ⟨n,hn⟩ := exists_nat_gt (|y-theta 0|/(2*Real.pi))
  have habs : |y-theta 0| < (n:ℝ)*(2*Real.pi) := (div_lt_iff₀ Real.two_pi_pos).mp hn
  have hupper : theta ((n:ℝ)*L) = theta 0+(n:ℝ)*(2*Real.pi) := by
    simpa only [zero_add] using hnat n 0
  have hnegative := hnat n (-((n:ℝ)*L))
  rw [neg_add_cancel] at hnegative
  have hlower : theta (-((n:ℝ)*L)) = theta 0-(n:ℝ)*(2*Real.pi) := by linarith
  apply intermediate_value_univ (-((n:ℝ)*L)) ((n:ℝ)*L) hTheta
  rw [hlower,hupper]
  exact ⟨by linarith [neg_abs_le (y-theta 0)],by linarith [le_abs_self (y-theta 0)]⟩

private theorem witnessCircle_polar (R theta : ℝ) :
    R • visibleConnectorUnitDirection theta = saddlePolarChart ![R,theta] := by
  ext i
  fin_cases i <;> simp [visibleConnectorUnitDirection,saddlePolarChart]

/-- Exact physical terminal circle range, independent of any chosen Jordan filling. -/
theorem visibleConnectorWitnessAssembly_terminal_circle_range
    {R L : ℝ} (hR : 0 < R) {theta : ℝ → ℝ} (hTheta : Continuous theta)
    (hShift : ∀ s, theta (s+L) = theta s+2*Real.pi) :
    range (fun s => R • visibleConnectorUnitDirection (theta s)) =
      {y : Coord | planarRadius y = R} := by
  ext y
  constructor
  · rintro ⟨s,rfl⟩
    change planarRadius (R • visibleConnectorUnitDirection (theta s)) = R
    rw [witnessCircle_polar]
    exact angularDescent_radius_polar (q := ![R,theta s]) hR
  · intro hy
    obtain ⟨t,ht⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hy
    obtain ⟨s,hs⟩ := visibleConnectorWitnessAssembly_phase_surjective hTheta hShift t
    refine ⟨s,?_⟩
    change R • visibleConnectorUnitDirection (theta s) = y
    rw [hs,witnessCircle_polar,ht]

/-- Actual trace containment therefore includes every point of the terminal circle. -/
theorem visibleConnectorWitnessAssembly_terminal_circle_subset
    {R L : ℝ} (hR : 0 < R) {theta : ℝ → ℝ} (hTheta : Continuous theta)
    (hShift : ∀ s, theta (s+L) = theta s+2*Real.pi)
    {gamma : ℝ → Coord} (hGamma : ∀ s, gamma s = R • visibleConnectorUnitDirection (theta s))
    {V : Set Coord} (hRange : range gamma ⊆ V) :
    {y : Coord | planarRadius y = R} ⊆ V := by
  have hfun : gamma = fun s => R • visibleConnectorUnitDirection (theta s) := funext hGamma
  rw [hfun,visibleConnectorWitnessAssembly_terminal_circle_range hR hTheta hShift] at hRange
  exact hRange

end
end TightVer401
