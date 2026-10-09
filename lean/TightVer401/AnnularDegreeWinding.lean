import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic
import TightVer401.CircleDiskWinding
import TightVer401.NativePlanarSchoenflies

/-! Actual winding in integer turns, through the pinned OpenAI covering-lift
increment. Normalization uses the actual difference from the target point.
No equality with a signed preimage count is postulated here.
-/
namespace TightVer401
noncomputable section
open Set Function
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology

/-- Actual unit direction from a target avoided by a continuous planar path. -/
def annularDirectionPath (γ : C(unitInterval, ℂ)) (y : ℂ)
    (hy : ∀ t, γ t ≠ y) : C(unitInterval, UnitAddCircle) :=
  ⟨fun t => normalizedArgument (γ t - y), by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hsub : ContinuousAt (fun s : unitInterval => γ s - y) t :=
      γ.continuous.continuousAt.sub continuousAt_const
    have harg : ContinuousAt normalizedArgument (γ t - y) :=
      continuousAt_normalizedArgument (sub_ne_zero.mpr (hy t))
    exact harg.comp (f := fun s : unitInterval => γ s - y) hsub⟩

theorem annularDirectionPath_closes (γ : C(unitInterval, ℂ))
    (hγ : γ 1 = γ 0) (y : ℂ) (hy : ∀ t, γ t ≠ y) :
    annularDirectionPath γ y hy 1 = annularDirectionPath γ y hy 0 := by
  unfold annularDirectionPath
  simp only [ContinuousMap.coe_mk]
  rw [hγ]

theorem annular_winding_exists_integer (γ : C(unitInterval, ℂ))
    (hγ : γ 1 = γ 0) (y : ℂ) (hy : ∀ t, γ t ≠ y) :
    ∃ m : ℤ, circlePathIncrement (annularDirectionPath γ y hy) = (m : ℝ) :=
  circlePathIncrement_integer _ (annularDirectionPath_closes γ hγ y hy)

/-- Winding of an actual loop about an avoided point, measured in turns. -/
def annularWinding (γ : C(unitInterval, ℂ)) (hγ : γ 1 = γ 0)
    (y : ℂ) (hy : ∀ t, γ t ≠ y) : ℤ :=
  Classical.choose (annular_winding_exists_integer γ hγ y hy)

theorem annularWinding_eq_increment (γ : C(unitInterval, ℂ)) (hγ : γ 1 = γ 0)
    (y : ℂ) (hy : ∀ t, γ t ≠ y) :
    (annularWinding γ hγ y hy : ℝ) = circlePathIncrement (annularDirectionPath γ y hy) :=
  (Classical.choose_spec (annular_winding_exists_integer γ hγ y hy)).symm

/-- Independence of the chosen real lift follows from the pinned covering
uniqueness theorem; no argument-branch or integral identity is assumed. -/
theorem annularWinding_eq_lift (γ : C(unitInterval, ℂ)) (hγ : γ 1 = γ 0)
    (y : ℂ) (hy : ∀ t, γ t ≠ y) (u : C(unitInterval, ℝ))
    (hu : ∀ t, (u t : UnitAddCircle) = annularDirectionPath γ y hy t) :
    (annularWinding γ hγ y hy : ℝ) = u 1 - u 0 := by
  rw [annularWinding_eq_increment, circlePathIncrement_eq_lift _ u hu]

theorem annularWinding_zero_of_closed_lift
    (γ : C(unitInterval, ℂ)) (hγ : γ 1 = γ 0)
    (y : ℂ) (hy : ∀ t, γ t ≠ y) (u : C(unitInterval, ℝ))
    (hu : ∀ t, (u t : UnitAddCircle) = annularDirectionPath γ y hy t)
    (hc : u 1 = u 0) : annularWinding γ hγ y hy = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, annularWinding_eq_lift γ hγ y hy u hu, hc, sub_self]

end
end TightVer401
