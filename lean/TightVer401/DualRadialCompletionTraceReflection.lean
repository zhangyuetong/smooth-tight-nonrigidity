import TightVer401.DualRadialCompletionTraceDefinitions
import TightVer401.CorrugatedSeedVisiblePairs
import Mathlib.Topology.UnitInterval

/-! Reflection and parameter reversal preserve the ordinary positive trace
for the same actual reflected homeomorphic filling. No new Jordan choice. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology ComplexConjugate

/-- Conjugation negates the existing argument in turns, including at zero. -/
theorem dualRadialCompletionTraceReflection_normalizedArgument_conj (z : ℂ) :
    normalizedArgument (conj z) = -normalizedArgument z := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (conj z) : Real.Angle) = -e (Complex.arg z : Real.Angle)
  rw [Complex.arg_conj_coe_angle]
  exact e.map_neg _

private theorem traceReflection_shift {f : ℝ → ℂ} (hp : Function.Periodic f 1) (t : ℝ) :
    f (1 - t) = f (-t) := by
  simpa only [sub_eq_add_neg, add_comm] using hp (-t)

private theorem traceReflection_injOn {f : ℝ → ℂ} (hp : Function.Periodic f 1)
    (hi : InjOn f (Ico 0 1)) : InjOn (corrugatedReverseReflect f) (Ico 0 1) := by
  intro a ha b hb he
  have hValues : f (-a) = f (-b) := by
    apply Complex.conjCLE.injective
    exact he
  by_cases ha0 : a = 0
  · subst a
    by_cases hb0 : b = 0
    · exact hb0.symm
    · have hbPositive : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
      have hbReflected : 1 - b ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith⟩
      have hValues' : f 0 = f (1 - b) := by
        rw [traceReflection_shift hp b]
        simpa only [neg_zero] using hValues
      have hParameters := hi ⟨le_rfl, by norm_num⟩ hbReflected hValues'
      exfalso
      linarith [hb.2]
  · have haPositive : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have haReflected : 1 - a ∈ Ico (0 : ℝ) 1 := ⟨by linarith [ha.2], by linarith⟩
    by_cases hb0 : b = 0
    · subst b
      have hValues' : f (1 - a) = f 0 := by
        rw [traceReflection_shift hp a]
        simpa only [neg_zero] using hValues
      have hParameters := hi haReflected ⟨le_rfl, by norm_num⟩ hValues'
      exfalso
      linarith [ha.2]
    · have hbPositive : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
      have hbReflected : 1 - b ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith⟩
      have hValues' : f (1 - a) = f (1 - b) := by
        rw [traceReflection_shift hp a, traceReflection_shift hp b]
        exact hValues
      have hParameters := hi haReflected hbReflected hValues'
      linarith

private theorem traceReflection_image_Icc {f : ℝ → ℂ} (hp : Function.Periodic f 1) :
    corrugatedReverseReflect f '' Icc (0 : ℝ) 1 =
      Complex.conjCLE.toHomeomorph '' (f '' Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨f (1 - t), ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩, ?_⟩
    change conj (f (1 - t)) = conj (f (-t))
    rw [traceReflection_shift hp t]
  · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    change conj (f (-(1 - t))) = conj (f t)
    have he : -(1 - t) = t - 1 := by ring
    rw [he, hp.sub_eq]

/-- All six ordinary positive trace fields transfer to the existing conjugated
filling and the existing reflected/reversed loop. -/
theorem dualRadialCompletionTraceReflection_positive
    {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ} (hTrace : DualRadialCompletionPositiveTrace H f) :
    DualRadialCompletionPositiveTrace (H.trans Complex.conjCLE.toHomeomorph)
      (corrugatedReverseReflect f) := by
  rcases hTrace with ⟨hf, hp, hi, hRegular, hBoundary, hPositive⟩
  refine ⟨corrugatedReverseReflect_contDiff hf, corrugatedReverseReflect_periodic hp,
    traceReflection_injOn hp hi, ?_, ?_, ?_⟩
  · intro t
    have hD := corrugatedReverseReflect_hasDerivAt
      ((hf.differentiable (by simp) (-t)).hasDerivAt)
    rw [hD.deriv]
    simpa using hRegular (-t)
  · calc
      corrugatedReverseReflect f '' Icc (0 : ℝ) 1 =
          Complex.conjCLE.toHomeomorph '' (f '' Icc (0 : ℝ) 1) := traceReflection_image_Icc hp
      _ = Complex.conjCLE.toHomeomorph '' frontier (H '' ball (0 : ℂ) 1) := by rw [hBoundary]
      _ = frontier ((H.trans Complex.conjCLE.toHomeomorph) '' ball (0 : ℂ) 1) := by
        rw [Complex.conjCLE.toHomeomorph.image_frontier]
        congr 1
        rw [image_image]
        rfl
  · rintro z ⟨w, hw, rfl⟩
    change ∃ v : C(unitInterval, ℝ),
      (∀ t, (v t : UnitAddCircle) = normalizedArgument (corrugatedReverseReflect f t - conj (H w))) ∧
        v 1 = v 0 + 1
    obtain ⟨u, hu, hTurn⟩ := hPositive (H w) ⟨w, hw, rfl⟩
    let v : C(unitInterval, ℝ) :=
      ⟨fun t => -u (unitInterval.symm t), (u.continuous.comp unitInterval.continuous_symm).neg⟩
    refine ⟨v, ?_, ?_⟩
    · intro t
      calc
        (v t : UnitAddCircle) = -(u (unitInterval.symm t) : UnitAddCircle) := by
          change ((-u (unitInterval.symm t) : ℝ) : UnitAddCircle) = -(u (unitInterval.symm t) : UnitAddCircle)
          exact AddCircle.coe_neg (1 : ℝ)
        _ = -normalizedArgument (f (unitInterval.symm t) - H w) := congrArg Neg.neg (hu _)
        _ = -normalizedArgument (f (-(t : ℝ)) - H w) := by
          rw [unitInterval.coe_symm_eq, traceReflection_shift hp (t : ℝ)]
        _ = normalizedArgument (conj (f (-(t : ℝ)) - H w)) :=
          (dualRadialCompletionTraceReflection_normalizedArgument_conj _).symm
        _ = normalizedArgument (corrugatedReverseReflect f t - conj (H w)) := by
          rw [map_sub]
          rfl
    · change -u (unitInterval.symm 1) = -u (unitInterval.symm 0) + 1
      rw [unitInterval.symm_one, unitInterval.symm_zero, hTurn]
      ring

end
end TightVer401
