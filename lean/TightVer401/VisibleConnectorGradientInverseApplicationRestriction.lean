import TightVer401.VisibleConnectorGradientInverseApplicationGlobal
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Literal restriction of the enlarged SAME gradient inverse. Its inverse
function remains exactly the enlarged inverse, not another selected inverse. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def visibleConnectorGradientInverseApplication_restricted_chart
    (E : OpenPartialHomeomorph Coord Coord) (V : Set Coord) (hV : IsOpen V) :
    OpenPartialHomeomorph Coord Coord := E.restrOpen V hV

/-- Exact source/target and SAME inverse of the restriction, after the actual
ordinary degree producer has supplied the image equality. -/
theorem visibleConnectorGradientInverseApplication_restricted_chart_properties
    {G : Coord → ℝ} {E : OpenPartialHomeomorph Coord Coord} {V W : Set Coord}
    (hV : IsOpen V) (hVE : V ⊆ E.source)
    (hE : (E : Coord → Coord) = planarGradient G)
    (hImage : planarGradient G '' V = W)
    (hES : ContDiffOn ℝ ∞ E E.source) (hEI : ContDiffOn ℝ ∞ E.symm E.target) :
    let P := visibleConnectorGradientInverseApplication_restricted_chart E V hV
    P.source = V ∧ P.target = W ∧ (P : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ P V ∧ ContDiffOn ℝ ∞ P.symm W ∧
      EqOn E P V ∧ EqOn E.symm P.symm W := by
  let P := visibleConnectorGradientInverseApplication_restricted_chart E V hV
  have hPS : P.source = V := by
    change E.source ∩ V = V
    exact inter_eq_right.mpr hVE
  have hPT : P.target = W := by
    rw [← P.image_source_eq_target,hPS]
    change E '' V = W
    rw [hE]
    exact hImage
  have hWT : W ⊆ E.target := by
    rw [← hImage]
    rintro y ⟨z,hz,rfl⟩
    rw [← hE]
    exact E.map_source (hVE hz)
  refine ⟨hPS,hPT,?_,?_,?_,?_,?_⟩
  · exact hE
  · exact hES.mono hVE
  · exact hEI.mono hWT
  · intro z _
    rfl
  · intro z _
    rfl

end
end TightVer401