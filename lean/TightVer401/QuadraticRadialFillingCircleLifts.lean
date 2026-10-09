import TightVer401.CircleDiskWinding

/-! Actual global real lifts and integer deck periods of circle-valued maps.
The construction uses the same covering mechanism as the pinned OpenAI
CircleLifts source, without assuming any lift or integer multiplicity. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped Topology

theorem quadraticRadialFillingCircle_exists_real_lift {f : ℝ → Circle}
    (hf : Continuous f) :
    ∃ u : ℝ → ℝ, Continuous u ∧ ∀ t, Circle.exp (u t) = f t := by
  let F : C(ℝ, Circle) := ⟨f, hf⟩
  obtain ⟨u, ⟨_, hu⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0
      ((f 0 : ℂ).arg) (Circle.exp_arg (f 0))
  exact ⟨u, u.continuous, fun t => congrFun hu t⟩

theorem quadraticRadialFillingCircle_lift_integer_deck
    {f : ℝ → Circle} {u : ℝ → ℝ} {L : ℝ}
    (hu : Continuous u) (hproj : ∀ t, Circle.exp (u t) = f t)
    (hper : Function.Periodic f L) :
    ∃ k : ℤ, ∀ t, u (t + L) = u t + (k : ℝ) * (2 * Real.pi) := by
  have he : Circle.exp (u L) = Circle.exp (u 0) := by
    rw [hproj L, hproj 0]
    simpa only [zero_add] using hper 0
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
  refine ⟨k, ?_⟩
  have hp : Circle.exp ∘ (fun t => u (t + L)) =
      Circle.exp ∘ (fun t => u t + (k : ℝ) * (2 * Real.pi)) := by
    funext t
    simp only [Function.comp_apply, Circle.exp_add,
      Circle.exp_int_mul_two_pi, mul_one, hproj]
    exact hper t
  have hu₁ : Continuous (fun t => u (t + L)) := hu.comp (continuous_id.add continuous_const)
  have hu₂ : Continuous (fun t => u t + (k : ℝ) * (2 * Real.pi)) := hu.add continuous_const
  have hEq := Circle.isCoveringMap_exp.eq_of_comp_eq hu₁ hu₂ hp 0
    (by simpa only [zero_add] using hk)
  exact congrFun hEq

end
end TightVer401
