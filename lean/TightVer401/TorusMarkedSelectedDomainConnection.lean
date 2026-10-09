import TightVer401.PositiveExitConstructionSelectedHomotopyJoin
import TightVer401.AnnularDegreeGlobal
import TightVer401.DualRadialCompletionTraceDefinitions
import TightVer401.AngularDescentCharts

/-! The actual closed-source-domain gate for the ordinary first-pair caller.
The two positive traces and the literal inner-to-outer homotopy are retained.
No source nesting, inverse, origin enclosure, or annulus-domain conclusion is
an input. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open Set Function Metric OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem selectedDomain_positiveJordan
    {H : ℂ ≃ₜ ℂ} {p : ℝ → ℂ}
    (hp : DualRadialCompletionPositiveTrace H p) :
    PositiveJordanParametrization H p := by
  rcases hp with ⟨hs, hper, hinj, hreg, hboundary, hpositive⟩
  exact ⟨hs, hper, hinj, hreg, hboundary, hpositive⟩

private theorem selectedDomain_complex_inverse (q : Coord) :
    seamComplexCoord (angularDescentComplex q) = q := by
  ext i
  fin_cases i <;> simp [angularDescentComplex, seamComplexCoord_apply]

/-- A literal INNER-to-OUTER source homotopy in the original domain derives
the whole closed-band hypothesis used by the ordinary marked-pair caller.
The loop parameter has already been normalized to period one. -/
theorem selectedSourceHomotopy_closedBand_subset
    {HpPlus HpMinus : ℂ ≃ₜ ℂ} {pPlus pMinus : ℝ → ℂ}
    {U : Set Coord}
    (hpPlus : DualRadialCompletionPositiveTrace HpPlus pPlus)
    (hpMinus : DualRadialCompletionPositiveTrace HpMinus pMinus)
    (houterU : ∀ s, pPlus s ∈ angularDescentComplex '' U)
    (hinnerU : ∀ s, pMinus s ∈ angularDescentComplex '' U)
    (H : C(unitInterval, C(unitInterval, ℂ)))
    (hH0 : ∀ t, H 0 t = pMinus (t : ℝ))
    (hH1 : ∀ t, H 1 t = pPlus (t : ℝ))
    (hclosed : ∀ a, H a 1 = H a 0)
    (hHU : ∀ a t, H a t ∈ angularDescentComplex '' U) :
    seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ U := by
  have ho := selectedDomain_positiveJordan hpPlus
  have hi := selectedDomain_positiveJordan hpMinus
  have hc : HpPlus 0 ∈ jordanInterior HpPlus :=
    ⟨0, mem_ball_self zero_lt_one, rfl⟩
  have hwind : planarFormIntegral
      (annularAngularFormP (id : ℂ → ℂ) (HpPlus 0))
      (annularAngularFormQ (id : ℂ → ℂ) (HpPlus 0)) pPlus = 1 := by
    change planarFormIntegral
      (fun z => circleFDeriv (centeredArgument (HpPlus 0)) z 1)
      (fun z => circleFDeriv (centeredArgument (HpPlus 0)) z Complex.I) pPlus = 1
    simpa only [circleFormIntegral,
      show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using
      annular_positive_source_argument_integral ho
  obtain ⟨R, hR0, hR1, hRc, hRU⟩ :=
    positiveExit_actual_loop_homotopy_symm H hclosed hHU
  have hRplus : R 0 = annularLoopPath pPlus ho.smooth.continuous := by
    apply ContinuousMap.ext
    intro t
    change R 0 t = pPlus (t : ℝ)
    rw [hR0]
    exact hH1 t
  have hRminus : R 1 = annularLoopPath pMinus hi.smooth.continuous := by
    apply ContinuousMap.ext
    intro t
    change R 1 t = pMinus (t : ℝ)
    rw [hR1]
    exact hH0 t
  have hDomain := positiveExit_actual_source_homotopy_closed_annulus_in_domain
    ho.toRegular hi.toRegular houterU hinnerU (HpPlus 0) hc hwind
    R hRplus hRminus hRc hRU
  rintro q ⟨z, hz, rfl⟩
  have hz' : z ∈ annularJordanClosure HpPlus HpMinus := by
    simpa only [annularJordanClosure, jordanInterior] using hz
  obtain ⟨u, hu, he⟩ := hDomain hz'
  rw [← he, selectedDomain_complex_inverse]
  exact hu

/-- The preceding gate for the actual Cartesian gradient inverse source,
with no new inverse or potential selected. -/
theorem selectedSourceHomotopy_closedBand_subset_source
    {HpPlus HpMinus : ℂ ≃ₜ ℂ} {pPlus pMinus : ℝ → ℂ}
    (e0 : OpenPartialHomeomorph Coord Coord)
    (hpPlus : DualRadialCompletionPositiveTrace HpPlus pPlus)
    (hpMinus : DualRadialCompletionPositiveTrace HpMinus pMinus)
    (houterU : ∀ s, pPlus s ∈ angularDescentComplex '' e0.source)
    (hinnerU : ∀ s, pMinus s ∈ angularDescentComplex '' e0.source)
    (H : C(unitInterval, C(unitInterval, ℂ)))
    (hH0 : ∀ t, H 0 t = pMinus (t : ℝ))
    (hH1 : ∀ t, H 1 t = pPlus (t : ℝ))
    (hclosed : ∀ a, H a 1 = H a 0)
    (hHU : ∀ a t, H a t ∈ angularDescentComplex '' e0.source) :
    seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source :=
  selectedSourceHomotopy_closedBand_subset hpPlus hpMinus houterU hinnerU
    H hH0 hH1 hclosed hHU

end
end TightVer401
