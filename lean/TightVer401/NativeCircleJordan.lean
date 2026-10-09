import OAI.Analysis.CircleDomains.Topology.CircleIntervalTraversal
import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Schoenflies.Curve

/-! Native circle embeddings are genuine Jordan curves. The interval traversal
and physical plane coordinates are the exact pinned OpenAI definitions.
The proof is the range conversion used in OpenAI's PlanarSchoenfliesProof;
no Jordan separation or extension conclusion is assumed here. -/
namespace TightVer401
noncomputable section
open Set Function
open OAI.CircleDomainRigidity
open scoped Topology

theorem circle_embedding_range_isJordanCurve (γ : Circle → Schoenflies.Plane)
    (hγ : Continuous γ) (hinj : Injective γ) :
    Schoenflies.IsJordanCurve (range γ) := by
  refine ⟨γ ∘ standardCircleTraversal, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hγ.comp continuous_standardCircleTraversal).continuousOn
  · exact congrArg γ standardCircleTraversal_closes
  · exact hinj.injOn.comp standardCircleTraversal_injOn (mapsTo_univ _ _)
  · rw [image_comp, standardCircleTraversal_image, image_univ]

theorem addCircle_embedding_range_isJordanCurve (L : ℝ) (hL : L ≠ 0)
    (γ : AddCircle L → Schoenflies.Plane) (hγ : Continuous γ) (hinj : Injective γ) :
    Schoenflies.IsJordanCurve (range γ) := by
  let e := AddCircle.homeomorphCircle hL
  have hj := circle_embedding_range_isJordanCurve (γ ∘ e.symm)
    (hγ.comp e.symm.continuous) (hinj.comp e.symm.injective)
  simpa only [range_comp, e.symm.surjective.range_eq, image_univ] using hj

def jordanComplexCoordinates : Schoenflies.Plane ≃L[ℝ] ℂ :=
  euclideanPlaneCoordinates.trans Complex.equivRealProdCLM.symm

@[simp] theorem jordanComplexCoordinates_apply (x : Schoenflies.Plane) :
    jordanComplexCoordinates x = (⟨x 0, x 1⟩ : ℂ) := rfl

theorem addCircle_complex_embedding_range_isJordanCurve (L : ℝ) (hL : L ≠ 0)
    (γ : AddCircle L → ℂ) (hγ : Continuous γ) (hinj : Injective γ) :
    Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ γ)) := by
  exact addCircle_embedding_range_isJordanCurve L hL _
    (jordanComplexCoordinates.symm.continuous.comp hγ)
    (jordanComplexCoordinates.symm.injective.comp hinj)

end
end TightVer401
