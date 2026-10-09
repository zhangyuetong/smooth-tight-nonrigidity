import TightVer401.DualRadialCompletionTraceDefinitions
import TightVer401.PositiveExitConstructionContract
import TightVer401.HomeomorphicJordanInside
import TightVer401.PeriodicComplexJordan
import TightVer401.SeamNormalCoordinates
import Mathlib.Topology.Covering.AddCircle

/-! The ordinary completion traces supply the actual connector traces. -/
namespace TightVer401
noncomputable section
open Set Filter Metric MeasureTheory OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology RealInnerProductSpace Matrix

local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- The boundary is that of the supplied homeomorphism, without a new filling choice. -/
theorem dualRadialCompletion_positiveTrace_range {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ}
    (hf : DualRadialCompletionPositiveTrace H f) :
    range f = H '' sphere (0 : ℂ) 1 := by
  have hr : range f = f '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro z ⟨t, rfl⟩
      refine ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
      simpa only [Int.fract, mul_one] using hf.2.1.sub_int_mul_eq (x := t) ⌊t⌋
    · rintro z ⟨t, _, rfl⟩
      exact mem_range_self t
  rw [hr, hf.2.2.2.2.1, ← H.image_frontier, frontier_ball _ one_ne_zero]

/-- A supplied disk containing the origin makes its actual trace nonzero. -/
theorem dualRadialCompletion_positiveTrace_nonzero {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ}
    (hf : DualRadialCompletionPositiveTrace H f)
    (h0 : (0 : ℂ) ∈ H '' ball (0 : ℂ) 1) : ∀ t, f t ≠ 0 := by
  have hO : IsOpen (H '' ball (0 : ℂ) 1) := H.isOpenMap _ isOpen_ball
  intro t ht
  have hb : f t ∈ frontier (H '' ball (0 : ℂ) 1) := by
    rw [← H.image_frontier, frontier_ball _ one_ne_zero,
      ← dualRadialCompletion_positiveTrace_range hf]
    exact mem_range_self t
  rw [ht] at hb
  exact hb.2 (by rwa [hO.interior_eq])

/-- Covering-map uniqueness extends the ordinary one-turn interval lift to
an actual global continuous argument lift. -/
theorem dualRadialCompletion_positiveTrace_turn {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ}
    (hf : DualRadialCompletionPositiveTrace H f)
    (h0 : (0 : ℂ) ∈ H '' ball (0 : ℂ) 1) : HasPositiveArgumentTurn f 1 := by
  have hne := dualRadialCompletion_positiveTrace_nonzero hf h0
  obtain ⟨u, hu, hturn⟩ := hf.2.2.2.2.2 0 h0
  have hu' (t : unitInterval) : (u t : UnitAddCircle) = normalizedArgument (f t) := by
    simpa only [sub_zero] using hu t
  let F : C(ℝ, UnitAddCircle) := ⟨fun t => normalizedArgument (f t),
    continuous_iff_continuousAt.mpr (fun t =>
      (continuousAt_normalizedArgument (hne t)).comp hf.1.continuous.continuousAt)⟩
  obtain ⟨v, ⟨hv0, hv⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      F 0 (u 0) (hu' 0)
  have he : ((↑) : ℝ → UnitAddCircle) ∘ (v ∘ (Subtype.val : unitInterval → ℝ)) =
      ((↑) : ℝ → UnitAddCircle) ∘ u := by
    funext t
    exact (congrFun hv (t : ℝ)).trans (hu' t).symm
  have heq : v ∘ (Subtype.val : unitInterval → ℝ) = u :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (v.continuous.comp continuous_subtype_val) u.continuous he 0 hv0
  have hdir (z : ℂ) : AddCircle.toCircle (normalizedArgument z) = complexCircleDirection z := by
    rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk, div_one]
    simp only [complexCircleDirection]
    congr 1
    field_simp
  refine ⟨fun t => 2 * Real.pi * v t, continuous_const.mul v.continuous, ?_, ?_⟩
  · intro t
    have hc := congrArg (AddCircle.toCircle (T := (1 : ℝ))) (congrFun hv t)
    change AddCircle.toCircle ((v t : ℝ) : UnitAddCircle) =
      AddCircle.toCircle (normalizedArgument (f t)) at hc
    rw [AddCircle.toCircle_apply_mk, div_one, hdir] at hc
    exact hc.symm
  · have hv1 : v 1 = u 1 := congrFun heq 1
    change 2 * Real.pi * v 1 - 2 * Real.pi * v 0 = 2 * Real.pi
    rw [hv1, hv0, hturn]
    ring

private theorem completion_exit_complexTrace (f : ℝ → ℂ) :
    positiveExitComplexTrace (seamComplexCoord ∘ f) = f := by
  funext t
  apply Complex.ext <;> rfl

private theorem completion_exit_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (seamComplexCoord ∘ f) t = seamComplexCoord (deriv f t) :=
  (seamComplexCoord.hasFDerivAt.comp_hasDerivAt t
    (hf.differentiable (by simp) t).hasDerivAt).deriv

private theorem completion_exit_dot (z w : ℂ) :
    seamComplexCoord z ⬝ᵥ seamComplexCoord w = inner ℝ z w := by
  rw [Complex.inner]
  simp only [seamComplexCoord_apply, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The actual original potential and chart yield all fields of the frozen
positive-exit trace, with the literal supplied source and gradient loops. -/
theorem dualRadialCompletion_exitTrace {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (hG : ContDiffOn ℝ ∞ G e.source)
    (heG : ∀ q ∈ e.source, e q = planarGradient G q)
    {Hp Hgamma : ℂ ≃ₜ ℂ} {p gamma : ℝ → ℂ}
    (hp : DualRadialCompletionPositiveTrace Hp p)
    (hgamma : DualRadialCompletionPositiveTrace Hgamma gamma)
    (hp0 : (0 : ℂ) ∈ Hp '' ball (0 : ℂ) 1)
    (hgamma0 : (0 : ℂ) ∈ Hgamma '' ball (0 : ℂ) 1)
    (hSource : ∀ t, seamComplexCoord (p t) ∈ e.source)
    (hActual : ∀ t, e (seamComplexCoord (p t)) = seamComplexCoord (gamma t))
    (hPairing : ∀ t, 0 < inner ℝ (deriv p t) (deriv gamma t)) :
    ∃ d : PositiveExitTrace G e.source 1,
      d.p = seamComplexCoord ∘ p ∧ d.gamma = seamComplexCoord ∘ gamma := by
  have hpS : ContDiff ℝ ∞ (seamComplexCoord ∘ p) := seamComplexCoord.contDiff.comp hp.1
  have hgS : ContDiff ℝ ∞ (seamComplexCoord ∘ gamma) := seamComplexCoord.contDiff.comp hgamma.1
  have hpP : Function.Periodic (seamComplexCoord ∘ p) 1 := fun t => congrArg seamComplexCoord (hp.2.1 t)
  have hgP : Function.Periodic (seamComplexCoord ∘ gamma) 1 := fun t => congrArg seamComplexCoord (hgamma.2.1 t)
  have hpI : InjOn (seamComplexCoord ∘ p) (Ico 0 1) := fun _ ht _ hs he =>
    hp.2.2.1 ht hs (seamComplexCoord.injective he)
  have hgI : InjOn (seamComplexCoord ∘ gamma) (Ico 0 1) := fun _ ht _ hs he =>
    hgamma.2.2.1 ht hs (seamComplexCoord.injective he)
  have hgrad : seamComplexCoord ∘ gamma = planarGradient G ∘ (seamComplexCoord ∘ p) := by
    funext t
    exact (hActual t).symm.trans (heG _ (hSource t))
  have hvalue : ContDiff ℝ ∞ (G ∘ (seamComplexCoord ∘ p)) :=
    contDiffOn_univ.mp (hG.comp hpS.contDiffOn (fun t _ => hSource t))
  refine ⟨{
    period_pos := by norm_num
    p := seamComplexCoord ∘ p
    gamma := seamComplexCoord ∘ gamma
    p_smooth := hpS
    gamma_smooth := hgS
    p_periodic := hpP
    gamma_periodic := hgP
    p_in_domain := fun t _ => hSource t
    actual_gradient := hgrad
    source_regular := ?_
    gradient_regular := ?_
    source_injective := periodicComplexCurve_lift_injective hpP hpI
    gradient_injective := periodicComplexCurve_lift_injective hgP hgI
    source_jordan := ?_
    gradient_jordan := ?_
    source_nonzero := ?_
    gradient_nonzero := ?_
    source_turn := ?_
    gradient_turn := ?_
    source_enclosure := ?_
    gradient_enclosure := ?_
    tangent_pairing := ?_
    value_smooth := hvalue
    value_periodic := fun t => congrArg G (hpP t)
    value_derivative := ?_
    zero_action := ?_
  }, rfl, rfl⟩
  · intro t he
    rw [completion_exit_deriv hp.1] at he
    exact hp.2.2.2.1 t (seamComplexCoord.injective (he.trans seamComplexCoord.map_zero.symm))
  · intro t he
    rw [completion_exit_deriv hgamma.1] at he
    exact hgamma.2.2.2.1 t (seamComplexCoord.injective (he.trans seamComplexCoord.map_zero.symm))
  · unfold positiveExitJordanRange
    rw [completion_exit_complexTrace]
    exact periodicComplexCurve_isJordanCurve hp.1 hp.2.1 hp.2.2.1
  · unfold positiveExitJordanRange
    rw [completion_exit_complexTrace]
    exact periodicComplexCurve_isJordanCurve hgamma.1 hgamma.2.1 hgamma.2.2.1
  · intro t he
    exact dualRadialCompletion_positiveTrace_nonzero hp hp0 t
      (seamComplexCoord.injective (he.trans seamComplexCoord.map_zero.symm))
  · intro t he
    exact dualRadialCompletion_positiveTrace_nonzero hgamma hgamma0 t
      (seamComplexCoord.injective (he.trans seamComplexCoord.map_zero.symm))
  · rw [completion_exit_complexTrace]
    exact dualRadialCompletion_positiveTrace_turn hp hp0
  · rw [completion_exit_complexTrace]
    exact dualRadialCompletion_positiveTrace_turn hgamma hgamma0
  · change jordanComplexCoordinates.symm (0 : ℂ) ∈
      Schoenflies.inside (positiveExitJordanRange (seamComplexCoord ∘ p))
    unfold positiveExitJordanRange
    rw [completion_exit_complexTrace]
    exact homeomorphic_filling_mem_inside (dualRadialCompletion_positiveTrace_range hp) hp0
  · change jordanComplexCoordinates.symm (0 : ℂ) ∈
      Schoenflies.inside (positiveExitJordanRange (seamComplexCoord ∘ gamma))
    unfold positiveExitJordanRange
    rw [completion_exit_complexTrace]
    exact homeomorphic_filling_mem_inside (dualRadialCompletion_positiveTrace_range hgamma) hgamma0
  · intro t
    rw [completion_exit_deriv hp.1, completion_exit_deriv hgamma.1, completion_exit_dot]
    exact hPairing t
  · intro t
    rw [hgrad]
    exact planarTrace_value_deriv hG e.open_source (hSource t)
      (hpS.differentiable (by simp) t)
  · rw [hgrad]
    exact planarTrace_periodic_action_zero hG e.open_source hpS (fun t _ => hSource t) hpP

end
end TightVer401
