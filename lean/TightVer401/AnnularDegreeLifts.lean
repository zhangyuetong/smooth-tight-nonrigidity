import OAI.Analysis.CircleDomains.Topology.CircleLifts

/-!
Dependency-isolated real-circuit lifting from the pinned OpenAI foundation
at upstream commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The existence proof below is the proof of
OAI.Analysis.CircleDomains.Selection.FixedCircuitExclusion.
exists_smooth_real_circuit_lift, with the boundary-exclusion dependencies
removed. The smoothness corollary follows the proof of
OAI.Analysis.CircleDomains.Topology.CircleFormBoundary.
contDiff_real_lift_along, using the already proved
CircleLifts.contDiffOn_circle_lift in place of the equivalent
SmoothRealLift.contDiffOn_real_lift. Both use the actual quotient charts.
No Green identity, winding increment, or global real lift is assumed.
-/
namespace TightVer401
noncomputable section
open Set Function Filter
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff

/-- Quotient-chart smoothness implies continuity. This is the cut-point
argument of pinned CircleDifferential, isolated from its energy imports. -/
theorem annular_smoothCircleOn_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → UnitAddCircle} {O : Set E} (hw : SmoothCircleOn w O) :
    ContinuousOn w O := by
  intro x hx
  let r : ℝ := AddCircle.equivIco 1 0 (w x)
  let a : ℝ := r - 1 / 2
  have hr : r ∈ Ico a (a + 1) := by dsimp [a]; constructor <;> linarith
  have ha : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
  have hcut : w x ≠ (a : UnitAddCircle) := by
    intro heq
    have he : (r : UnitAddCircle) = (a : UnitAddCircle) :=
      AddCircle.coe_equivIco.trans heq
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hr ha).mp he
    dsimp [a] at he'
    linarith
  have heq : (fun y => ((AddCircle.equivIco 1 a (w y) : ℝ) : UnitAddCircle))
      =ᶠ[𝓝 x] w := Filter.Eventually.of_forall (fun _ => AddCircle.coe_equivIco)
  exact (((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp
    (hw x hx a hcut).continuousAt).congr heq).continuousWithinAt

/-- Every continuous actual real lift along a smooth source path is smooth,
by the pinned local quotient-chart proof. -/
theorem annular_contDiff_real_lift_along
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    {v : ℝ → ℝ} (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) : ContDiff ℝ ∞ v := by
  apply contDiffOn_univ.mp
  apply contDiffOn_circle_lift isOpen_univ hv.continuousOn (fun t _ => hproj t)
  intro t _ a ha
  exact (hu (γ t) (hγO t) a ha).comp t hγ.contDiffAt

/-- Actual real-circuit lift obtained from the proved covering-map lifting
on the contractible real line, without the unrelated exclusion/limit chain. -/
theorem annular_exists_smooth_real_circuit_lift
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ ∀ t, (v t : UnitAddCircle) = w (γ t) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  have hc : Continuous (w ∘ γ) :=
    continuous_iff_continuousAt.mpr (fun t =>
      ((annular_smoothCircleOn_continuousOn hw).continuousAt
        (hO.mem_nhds (hγO t))).comp hγ.continuous.continuousAt)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift (w ∘ γ) hc.continuousOn
    (mem_univ 0) ((AddCircle.equivIco (1 : ℝ) 0 (w (γ 0))) : ℝ) (by
      simp only [Function.comp_apply, AddCircle.coe_equivIco])
  have hv' := continuousOn_univ.mp hv
  have hp' : ∀ t, (v t : UnitAddCircle) = w (γ t) := fun t => hp t (mem_univ t)
  exact ⟨v, annular_contDiff_real_lift_along hw hγ hγO hv' hp', hp'⟩

end
end TightVer401
