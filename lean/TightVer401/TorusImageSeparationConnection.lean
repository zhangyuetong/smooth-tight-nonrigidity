import TightVer401.TorusMetricBranching
import TightVer401.ClassicalExternal

/-! Actual image inequality for the same protected opposite bending branches.
The classical equal-image fixed-open principle is an explicit parameter.
Embedding of the actual branches is ordinary input to be supplied by the proved
small-amplitude stability application. This is weaker than image noncongruence:
no marking or ambient-congruence reduction is supplied by this leaf. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

/-- Equal actual images would force equality of the actual parametrizations,
contradicting the nonzero protected field at a nonzero amplitude. All branch
forms, open agreement and map separation are derived for the same literal Z. -/
theorem protectedTorus_bending_ranges_ne_of_classical
    (background : ClassicalExternalResults)
    {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (hout : ∃ q, q ∉ e '' tsupport Y)
    {ε : ℝ} (hε : ε ≠ 0)
    (hplusEmbedding : Topology.IsEmbedding (F + ε • protectedTorusBendingField e A Y))
    (hminusEmbedding : Topology.IsEmbedding (F - ε • protectedTorusBendingField e A Y)) :
    range (F + ε • protectedTorusBendingField e A Y) ≠
      range (F - ε • protectedTorusBendingField e A Y) := by
  let Z := protectedTorusBendingField e A Y
  obtain ⟨g, hplus, hminus, _hplusPlane, _hminusPlane, _hg,
    hforms, _hpositive, himm, hU, hmaps⟩ :=
    protectedTorus_metric_branching hX hY hcompact hnonzero e hsupport he A F
      hplacement hF hinj hout hε
  have hp : NativeTorusSmoothEmbedding (F + ε • Z) :=
    ⟨hplus, fun p => (himm p).1, hplusEmbedding⟩
  have hm : NativeTorusSmoothEmbedding (F - ε • Z) :=
    ⟨hminus, fun p => (himm p).2, hminusEmbedding⟩
  intro himage
  have hagree : EqOn (F + ε • Z) (F - ε • Z) (e '' tsupport Y)ᶜ := by
    intro p hpU
    exact (hU.2.2.1 hpU).trans (hU.2.2.2 hpU).symm
  have hequal : F + ε • Z = F - ε • Z :=
    classicalCoincidentEmbeddings_eq background _ _ hp hm
      (fun p v z => (hforms p v z).1) himage (e '' tsupport Y)ᶜ
      hU.1 hU.2.1 hagree
  exact hmaps hequal

end
end TightVer401

