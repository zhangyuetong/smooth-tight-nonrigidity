import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Fixed-dimensional Sard adapters for the height route. These statements use
actual derivatives. No regular-value or Gauss-tightness theorem is assumed. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- The image of the actual critical points in any differentiability domain
has Haar measure zero. No openness or measurability of that domain is needed. -/
theorem gaussTightness_critical_image_null {f : V → V} {s : Set V}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => fderiv ℝ f x)
  · intro x hx
    exact (hf x hx.1).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact hx.2

include μ in
/-- Simultaneously avoid all critical images in a countable atlas. The maps
share the same target coordinate space; their source domains may differ. -/
theorem gaussTightness_dense_regular_values {ι : Type*} [Countable ι]
    (f : ι → V → V) (s : ι → Set V)
    (hf : ∀ i x, x ∈ s i → DifferentiableAt ℝ (f i) x) :
    Dense {y | ∀ i x, x ∈ s i → f i x = y → (fderiv ℝ (f i) x).det ≠ 0} := by
  let C : ι → Set V := fun i => f i '' {x | x ∈ s i ∧ (fderiv ℝ (f i) x).det = 0}
  have hC : ∀ i, μ (C i) = 0 := fun i =>
    gaussTightness_critical_image_null μ (hf i)
  have hnull : μ (⋃ i, C i) = 0 := measure_iUnion_null hC
  have hae : ∀ᵐ y ∂μ, y ∉ ⋃ i, C i := by
    exact ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using hnull)
  apply μ.dense_of_ae
  filter_upwards [hae] with y hy
  intro i x hx hxy hdet
  apply hy
  exact mem_iUnion.mpr ⟨i, ⟨x, ⟨hx, hdet⟩, hxy⟩⟩

end
end TightVer401
