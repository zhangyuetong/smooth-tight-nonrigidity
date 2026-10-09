import TightVer401.TorusSourceGeometry
import TightVer401.NativeProductPlaneCurvature
import TightVer401.SphereCharts

/-! User-authorized classical/external background for the ver500 construction.
These are explicit theorem hypotheses, never axioms or existence grants.
The kernel checks definitions and applications; it does not prove the background
statements merely because their types are checked. See classical-external-results.json. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

/-- Actual OpenAI intrinsic curvature in the native preferred chart at its center. -/
def nativeTorusChartCurvature (X : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) : ℝ :=
  gaussianCurvature (inducedMetric (nativeProductCoordinateMap X p))
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p))

/-- The positive region belongs to the actual map, not a supplied curvature function. -/
def nativeTorusPositiveRegion (X : NonrigidTorusSource → Ambient) : Set NonrigidTorusSource :=
  {p | 0 < nativeTorusChartCurvature X p}

/-- Ordinary actual smooth embedding and immersion premises. -/
def NativeTorusSmoothEmbedding (X : NonrigidTorusSource → Ambient) : Prop :=
  ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X ∧
  (∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) ∧
  Topology.IsEmbedding X

/-- Classical corollary of the Gauss-area formula and Banchoff--Kühnel §1.1:
a one-sheeted positive-curvature Gauss image missing only finitely many sphere
points has positive curvature integral 4π, hence the two-piece property.
The actual smooth global unit normal and its actual differential orthogonality,
exact positive source, exact target, and smooth inverse are APPLICATION obligations. -/
def ClassicalPositiveGaussTightnessClaim : Prop :=
  ∀ (X : NonrigidTorusSource → Ambient), NativeTorusSmoothEmbedding X →
    ∀ (N : NonrigidTorusSource → RoundSphere),
      ContMDiff nativeProductModel (𝓡 2) ∞ N →
      (∀ p (v : ℝ × ℝ), @inner ℝ Ambient _ (N p : Ambient)
        (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0) →
      ∀ (E : Set RoundSphere), E.Finite →
        ∀ (e : OpenPartialHomeomorph NonrigidTorusSource RoundSphere),
          e.source = nativeTorusPositiveRegion X →
          e.target = univ \ E →
          EqOn e N e.source →
          ContMDiffOn nativeProductModel (𝓡 2) ∞ e e.source →
          ContMDiffOn (𝓡 2) nativeProductModel ∞ e.symm e.target →
          IsTightImage X

/-- Classical corollary of the smooth embedding/submanifold theorem and rigidity
of connected Riemannian local isometries fixed on an open set. Equal actual
induced forms produce the common positive metric; the equal-image embeddings
produce its smooth reparametrization. This grants no marked region or noncongruence. -/
def ClassicalCoincidentEmbeddingFixedOpenClaim : Prop :=
  ∀ (X Y : NonrigidTorusSource → Ambient),
    NativeTorusSmoothEmbedding X → NativeTorusSmoothEmbedding Y →
    (∀ p (v w : ℝ × ℝ),
      nativeProductInducedForm X p v w = nativeProductInducedForm Y p v w) →
    range X = range Y →
    ∀ (U : Set NonrigidTorusSource), IsOpen U → U.Nonempty → EqOn X Y U → X = Y

/-- The two named external mathematical statements accepted by the user.
No inhabitant is asserted. Final construction proofs take this as a parameter. -/
structure ClassicalExternalResults : Prop where
  positiveGaussTightness : ClassicalPositiveGaussTightnessClaim
  coincidentEmbeddingFixedOpen : ClassicalCoincidentEmbeddingFixedOpenClaim

/-- A checked application, explicitly conditional on the external background. -/
theorem classicalPositiveGauss_tightness (background : ClassicalExternalResults)
    (X : NonrigidTorusSource → Ambient) (hX : NativeTorusSmoothEmbedding X)
    (N : NonrigidTorusSource → RoundSphere)
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N)
    (horth : ∀ p (v : ℝ × ℝ), @inner ℝ Ambient _ (N p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0)
    (E : Set RoundSphere) (hE : E.Finite)
    (e : OpenPartialHomeomorph NonrigidTorusSource RoundSphere)
    (hsource : e.source = nativeTorusPositiveRegion X) (htarget : e.target = univ \ E)
    (he : EqOn e N e.source)
    (hs : ContMDiffOn nativeProductModel (𝓡 2) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 2) nativeProductModel ∞ e.symm e.target) : IsTightImage X :=
  background.positiveGaussTightness X hX N hN horth E hE e hsource htarget he hs hi

/-- A checked rigidity application with its external parameter retained. -/
theorem classicalCoincidentEmbeddings_eq (background : ClassicalExternalResults)
    (X Y : NonrigidTorusSource → Ambient)
    (hX : NativeTorusSmoothEmbedding X) (hY : NativeTorusSmoothEmbedding Y)
    (hmetric : ∀ p (v w : ℝ × ℝ),
      nativeProductInducedForm X p v w = nativeProductInducedForm Y p v w)
    (himage : range X = range Y) (U : Set NonrigidTorusSource)
    (hU : IsOpen U) (hne : U.Nonempty) (hagree : EqOn X Y U) : X = Y :=
  background.coincidentEmbeddingFixedOpen X Y hX hY hmetric himage U hU hne hagree

end
end TightVer401
