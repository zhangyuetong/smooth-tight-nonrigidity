import TightVer401.PositiveExitConstructionSelectedSourceGeometryProtectedWinding
import TightVer401.PositiveExitConstructionSelectedSourceGeometryRawConstruction
import TightVer401.PositiveExitConstructionSelectedSourceGeometrySelectedProtectedPair

/-! Set-level placement and selected nesting from actual protected-point
homotopies of the SAME raw and selected boundaries. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

private theorem selectedPlacement_complex_inverse (q : Coord) :
    seamComplexCoord (angularDescentComplex q) = q := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, angularDescentComplex]

/-- Two actual graph-to-raw homotopies transport the whole protected set
from its proved raw annulus into the selected annulus. Boundary separation,
a common enclosed point, and one protected point then force strict selected
nesting. Neither selected placement nor selected nesting is a premise. -/
theorem positiveExitSelected_protected_placement_and_nesting
    {Ro Ri Ho Hi : ℂ ≃ₜ ℂ} {rawOuter rawInner selectedOuter selectedInner : ℝ → ℂ}
    (hRawOuter : PositiveJordanParametrization Ro rawOuter)
    (hRawInner : PositiveJordanParametrization Ri rawInner)
    (hSelectedOuter : PositiveJordanParametrization Ho selectedOuter)
    (hSelectedInner : PositiveJordanParametrization Hi selectedInner)
    {C : Set Coord} (hC : C.Nonempty)
    (hRawC : C ⊆ annularCoordJordanInterior Ro Ri)
    (Outer Inner : C(unitInterval, C(unitInterval, ℂ)))
    (hOuter0 : ∀ t, Outer 0 t = selectedOuter t)
    (hOuter1 : ∀ t, Outer 1 t = rawOuter t)
    (hInner0 : ∀ t, Inner 0 t = selectedInner t)
    (hInner1 : ∀ t, Inner 1 t = rawInner t)
    (hOuterClosed : ∀ a, Outer a 1 = Outer a 0)
    (hInnerClosed : ∀ a, Inner a 1 = Inner a 0)
    (hOuterAvoid : ∀ a t q, q ∈ C → Outer a t ≠ angularDescentComplex q)
    (hInnerAvoid : ∀ a t q, q ∈ C → Inner a t ≠ angularDescentComplex q)
    (hDisjoint : Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior Ho) (hcInner : c ∈ jordanInterior Hi) :
    C ⊆ annularCoordJordanInterior Ho Hi ∧
      closure (jordanInterior Hi) ⊆ jordanInterior Ho := by
  have hO0 : Outer 0 = annularLoopPath selectedOuter hSelectedOuter.smooth.continuous := by
    apply ContinuousMap.ext
    exact hOuter0
  have hO1 : Outer 1 = annularLoopPath rawOuter hRawOuter.smooth.continuous := by
    apply ContinuousMap.ext
    exact hOuter1
  have hI0 : Inner 0 = annularLoopPath selectedInner hSelectedInner.smooth.continuous := by
    apply ContinuousMap.ext
    exact hInner0
  have hI1 : Inner 1 = annularLoopPath rawInner hRawInner.smooth.continuous := by
    apply ContinuousMap.ext
    exact hInner1
  have hSides : ∀ q ∈ C,
      angularDescentComplex q ∈ jordanInterior Ho ∧
      angularDescentComplex q ∉ closure (jordanInterior Hi) := by
    intro q hq
    obtain ⟨z, hz, he⟩ := hRawC hq
    have hyz : angularDescentComplex q = z := by
      apply seamComplexCoord.injective
      rw [selectedPlacement_complex_inverse, he]
    have hraw : angularDescentComplex q ∈ annularJordanInterior Ro Ri := by
      rw [hyz]
      exact hz
    have houter := positiveExit_protected_homotopy_sides_iff
      hSelectedOuter hRawOuter Outer (angularDescentComplex q) hO0 hO1
      hOuterClosed (fun a t => hOuterAvoid a t q hq)
    have hinner := positiveExit_protected_homotopy_sides_iff
      hSelectedInner hRawInner Inner (angularDescentComplex q) hI0 hI1
      hInnerClosed (fun a t => hInnerAvoid a t q hq)
    exact ⟨houter.1.mpr hraw.1, hinner.2.mpr hraw.2⟩
  have hSelectedC : C ⊆ annularCoordJordanInterior Ho Hi := by
    intro q hq
    exact ⟨angularDescentComplex q, hSides q hq, selectedPlacement_complex_inverse q⟩
  refine ⟨hSelectedC, ?_⟩
  rcases disjoint_or_nested_jordanInteriors Ho Hi hDisjoint with hd | hwrong | hright
  · exact False.elim (Set.disjoint_left.mp hd (subset_closure hcOuter) (subset_closure hcInner))
  · obtain ⟨q, hq⟩ := hC
    have hs := hSides q hq
    exact False.elim (hs.2 (subset_closure (hwrong (subset_closure hs.1))))
  · exact hright

end
end TightVer401
