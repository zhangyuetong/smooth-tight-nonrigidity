import TightVer401.ProtectedTorusBranchGaussConnection

/-! Transfer an actual baseline positive-region Gauss diffeomorphism to an
actual native branch with the same entire positive source and baseline map
germs there. The baseline normal is explicitly identified with the canonical
actual derivative cross normal; no baseline construction is assumed here. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Reuse the SAME baseline Gauss map and inverse for the actual branch.
Its global normal is constructed from the branch's actual native differential. -/
def nativeTorusPositiveGaussData_of_branch_germs
    {F : NonrigidTorusSource → Ambient}
    (base : NativeTorusPositiveGaussData F)
    (hcanonical : base.normal = nativeTorusImmersionNormal F base.embedding.2.1)
    (G : NonrigidTorusSource → Ambient) (hG : NativeTorusSmoothEmbedding G)
    (hregion : nativeTorusPositiveRegion G = nativeTorusPositiveRegion F)
    (hgerm : ∀ p ∈ nativeTorusPositiveRegion F, G =ᶠ[𝓝 p] F) :
    NativeTorusPositiveGaussData G := by
  refine {
    embedding := hG
    normal := nativeTorusImmersionNormal G hG.2.1
    normal_smooth := nativeTorusImmersionNormal_contMDiff hG.1 hG.2.1
    normal_orthogonal := nativeTorusImmersionNormal_orthogonal hG.2.1
    exceptional := base.exceptional
    exceptional_finite := base.exceptional_finite
    gauss := base.gauss
    gauss_source := base.gauss_source.trans hregion.symm
    gauss_target := base.gauss_target
    gauss_eq := ?_
    gauss_smooth := base.gauss_smooth
    gauss_inverse_smooth := base.gauss_inverse_smooth }
  intro p hp
  have hpF : p ∈ nativeTorusPositiveRegion F := by
    rwa [base.gauss_source] at hp
  calc
    base.gauss p = base.normal p := base.gauss_eq hp
    _ = nativeTorusImmersionNormal F base.embedding.2.1 p := congrFun hcanonical p
    _ = nativeTorusImmersionNormal G hG.2.1 p :=
      (nativeTorusImmersionNormal_eq_of_eventuallyEq hG.2.1 base.embedding.2.1
        (hgerm p hpF)).symm

/-- Apply the explicit external classical criterion to the actual branch data. -/
theorem nativeTorus_branch_tight_of_classical
    (background : ClassicalExternalResults)
    {F : NonrigidTorusSource → Ambient}
    (base : NativeTorusPositiveGaussData F)
    (hcanonical : base.normal = nativeTorusImmersionNormal F base.embedding.2.1)
    (G : NonrigidTorusSource → Ambient) (hG : NativeTorusSmoothEmbedding G)
    (hregion : nativeTorusPositiveRegion G = nativeTorusPositiveRegion F)
    (hgerm : ∀ p ∈ nativeTorusPositiveRegion F, G =ᶠ[𝓝 p] F) : IsTightImage G :=
  nativeTorusPositiveGaussData_tight_of_classical background
    (nativeTorusPositiveGaussData_of_branch_germs base hcanonical G hG hregion hgerm)

end
end TightVer401
