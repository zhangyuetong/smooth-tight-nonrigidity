import TightVer401.PositiveExitConstructionContract
import TightVer401.DualRadialCompletionConnectorCollar

/-! The ordinary two-exit output supplies a compact closed source annulus
inside its actual smooth saddle domain. Its SAME gradient chart extends to
one open inverse collar, with literal forward and inverse agreement. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

variable {T w delta : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G : Coord → ℝ} {U : Set Coord}
    {e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {he : e.source = univ} {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0}
    {hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w}
    {O : Set Coord} {xi : ℝ}

theorem dualRadialCompletionExitApplication_source_closure_compact
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) :
    IsCompact (closure X.source_annulus) := by
  have hRange : range (fun p : AddCircle T × Icc (0 : ℝ) 1 =>
      (X.source_closure_chart p : Coord)) = closure X.source_annulus := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact (X.source_closure_chart p).property
    · intro hq
      obtain ⟨p, hp⟩ := X.source_closure_chart.surjective ⟨q, hq⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  rw [← hRange]
  exact isCompact_range (continuous_subtype_val.comp X.source_closure_chart.continuous)

theorem dualRadialCompletionExitApplication_source_closure_in_domain
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) :
    closure X.source_annulus ⊆ X.Uexit := by
  have hOpen : IsOpen X.source_annulus := by
    rw [← X.source_chart_target]
    exact X.source_chart.open_target
  intro q hq
  by_cases hqa : q ∈ X.source_annulus
  · exact X.source_annulus_in_domain hqa
  have hFront : q ∈ frontier X.source_annulus := by
    rw [frontier, hOpen.interior_eq]
    exact ⟨hq, hqa⟩
  rw [X.source_boundary_exact] at hFront
  rcases hFront with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact X.inner.p_in_domain (mem_univ s)
  · exact X.outer.p_in_domain (mem_univ s)

theorem exists_dualRadialCompletion_exit_application_collar
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) :
    ∃ E : OpenPartialHomeomorph Coord Coord,
      closure X.source_annulus ⊆ E.source ∧ E.source ⊆ X.Uexit ∧
      ContDiffOn ℝ ∞ X.Gexit E.source ∧
      (∀ p ∈ E.source, (planarHessian X.Gexit p).det < 0) ∧
      (E : Coord → Coord) = planarGradient X.Gexit ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      X.gradient_annulus ⊆ E.target ∧
      EqOn E X.gradient_chart X.source_annulus ∧
      EqOn E.symm X.gradient_chart.symm X.gradient_annulus := by
  have hClosedU := dualRadialCompletionExitApplication_source_closure_in_domain X
  have hInj : InjOn (planarGradient X.Gexit) (closure X.source_annulus) := by
    intro p hp q hq heq
    have heq' : X.gradient_closure_chart ⟨p, hp⟩ =
        X.gradient_closure_chart ⟨q, hq⟩ := by
      apply Subtype.ext
      simpa only [X.gradient_closure_actual] using heq
    exact congrArg Subtype.val (X.gradient_closure_chart.injective heq')
  have hCont : ∀ p ∈ closure X.source_annulus,
      ContinuousAt (planarGradient X.Gexit) p := by
    intro p hp
    exact (planarGradient_contDiffOn X.Gexit_smooth X.Uexit_open).contDiffAt
      (X.Uexit_open.mem_nhds (hClosedU hp)) |>.continuousAt
  have hLocal : ∀ p ∈ closure X.source_annulus,
      ∃ W ∈ 𝓝 p, InjOn (planarGradient X.Gexit) W := by
    intro p hp
    obtain ⟨E, hE, _hEU, hEf, _hEi⟩ := planarGradient_exists_smooth_local_inverse_at
      X.Gexit_smooth X.Uexit_open (hClosedU hp) (X.saddle p (hClosedU hp)).ne
    refine ⟨E.source, E.open_source.mem_nhds hE, ?_⟩
    rw [← hEf]
    exact E.injOn
  obtain ⟨W, hW, hCW, hIW⟩ := hInj.exists_isOpen_superset
    (dualRadialCompletionExitApplication_source_closure_compact X) hCont hLocal
  let Z := W ∩ X.Uexit
  have hZ : IsOpen Z := hW.inter X.Uexit_open
  have hCZ : closure X.source_annulus ⊆ Z := fun p hp => ⟨hCW hp, hClosedU hp⟩
  have hZU : Z ⊆ X.Uexit := inter_subset_right
  have hGZ := X.Gexit_smooth.mono hZU
  have hNZ : ∀ p ∈ Z, (planarHessian X.Gexit p).det < 0 :=
    fun p hp => X.saddle p (hZU hp)
  have hIZ : InjOn (planarGradient X.Gexit) Z := hIW.mono inter_subset_left
  have hJ : ∀ p ∈ Z, annularJacobian (planarGradient X.Gexit) p ≠ 0 := by
    intro p hp
    rw [dualRadialCompletion_gradient_jacobian hGZ hZ hp]
    exact (hNZ p hp).ne
  have hUnique : ∀ y ∈ planarGradient X.Gexit '' Z,
      ∃! p, p ∈ Z ∧ planarGradient X.Gexit p = y := by
    rintro y ⟨p, hp, hpy⟩
    refine ⟨p, ⟨hp, hpy⟩, ?_⟩
    intro q hq
    exact hIZ hq.1 hp (hq.2.trans hpy.symm)
  obtain ⟨E, hEs, _hEt, hEf, hEi⟩ := annular_exists_smooth_image_inverse hZ
    (planarGradient_contDiffOn hGZ hZ) hJ hUnique
  have hCE : closure X.source_annulus ⊆ E.source := by simpa only [hEs] using hCZ
  have hOldSource : ∀ y ∈ X.gradient_annulus,
      X.gradient_chart.symm y ∈ X.source_annulus := by
    intro y hy
    rw [← X.gradient_chart_source]
    exact X.gradient_chart.map_target (by simpa only [X.gradient_chart_target] using hy)
  have hForward : ∀ y ∈ X.gradient_annulus,
      E (X.gradient_chart.symm y) = y := by
    intro y hy
    rw [hEf, ← X.actual_gradient_chart (hOldSource y hy)]
    exact X.gradient_chart.right_inv (by simpa only [X.gradient_chart_target] using hy)
  refine ⟨E, hCE, ?_, ?_, ?_, hEf, hEi, ?_, ?_, ?_⟩
  · simpa only [hEs] using hZU
  · simpa only [hEs] using hGZ
  · simpa only [hEs] using hNZ
  · intro y hy
    rw [← hForward y hy]
    exact E.map_source (hCE (subset_closure (hOldSource y hy)))
  · intro p hp
    rw [hEf]
    exact (X.actual_gradient_chart hp).symm
  · intro y hy
    calc
      E.symm y = E.symm (E (X.gradient_chart.symm y)) :=
        congrArg E.symm (hForward y hy).symm
      _ = X.gradient_chart.symm y := E.left_inv
        (hCE (subset_closure (hOldSource y hy)))

end
end TightVer401
