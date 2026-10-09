import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TightVer401.BorsukCompatibility

namespace TightVer401
open Set
theorem continuousLinearMap_isOpen_isInvertible
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    IsOpen {f : E →L[𝕜] F | f.IsInvertible} := by
  change IsOpen (range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F))
  exact ContinuousLinearEquiv.isOpen
end TightVer401
