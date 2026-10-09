import TightVer401.NativeCircleJordan
import Schoenflies.JordanSchoenflies

/-! The relative extension argument of OpenAI's pinned PlanarSchoenfliesProof,
using the already checked coordinate adapter and exact pinned external theorem.
Unrelated regular-level classification interfaces are not needed by this proof. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped Topology

theorem exists_complex_schoenflies (γ : Circle → ℂ)
    (hγ : Continuous γ) (hinj : Injective γ) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle, H (z : ℂ) = γ z := by
  let e : ℂ ≃ₜ Schoenflies.Plane := jordanComplexCoordinates.toHomeomorph.symm
  let c0 : Circle → Schoenflies.Plane := fun z => e (z : ℂ)
  let c1 : Circle → Schoenflies.Plane := fun z => e (γ z)
  have hc0 : Continuous c0 := e.continuous.comp continuous_subtype_val
  have hi0 : Injective c0 := e.injective.comp Subtype.val_injective
  have hc1 : Continuous c1 := e.continuous.comp hγ
  have hi1 : Injective c1 := e.injective.comp hinj
  let e0 : Circle ≃ₜ range c0 := (hc0.isClosedEmbedding hi0).isEmbedding.toHomeomorph
  let e1 : Circle ≃ₜ range c1 := (hc1.isClosedEmbedding hi1).isEmbedding.toHomeomorph
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (circle_embedding_range_isJordanCurve c0 hc0 hi0)
    (circle_embedding_range_isJordanCurve c1 hc1 hi1) (e0.symm.trans e1)
  refine ⟨e.trans (F.trans e.symm), ?_⟩
  intro z
  have hh : F (e (z : ℂ)) = e (γ z) := by
    simpa only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
      e0, e1, Topology.IsEmbedding.toHomeomorph_apply_coe, c0, c1] using hF (e0 z)
  change e.symm (F (e (z : ℂ))) = γ z
  rw [hh, e.symm_apply_apply]
end
end TightVer401
