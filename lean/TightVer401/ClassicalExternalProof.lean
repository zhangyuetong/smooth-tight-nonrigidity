import TightVer401.ClassicalPositiveGaussTightnessProof
import TightVer401.ClassicalCoincidentEmbeddingFixedOpenProof

/-! Closed proofs of the two geometric statements in the retained background
interface. Conditional consumers remain reusable; their bundle now has an
explicit proved inhabitant. -/
namespace TightVer401

theorem classicalExternalResults_proved : ClassicalExternalResults :=
  ⟨classicalPositiveGaussTightness_proved,
    classicalCoincidentEmbeddingFixedOpen_proved⟩

end TightVer401
