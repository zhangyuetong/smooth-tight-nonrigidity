import TightVer401.ClassicalExternal

/-! Ordinary classical embedded-image reparameterization, retained as an
additional explicit theorem parameter. The existing ClassicalExternalResults
bundle is unchanged. This file defines no inhabitant of the claim.

Reference: Ralph Cohen, Bundles, Homotopy, and Manifolds, section 3.2.3,
Theorem 3.3 and Proposition 3.4. Two smooth embeddings with the same image
identify the same embedded submanifold; composing their smooth inverses gives
the smooth source homeomorphism below. No metric or curvature conclusion is
part of this background statement. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

/-- Equal actual embedded images admit an actual smooth source
reparameterization. Both directions are smooth for the existing native model.
This is an explicit background premise, not a proved inhabitant. -/
def ClassicalEmbeddedImageReparametrizationClaim : Prop :=
  ∀ (X Y : NonrigidTorusSource → Ambient),
    NativeTorusSmoothEmbedding X → NativeTorusSmoothEmbedding Y →
    range X = range Y →
    ∃ e : NonrigidTorusSource ≃ₜ NonrigidTorusSource,
      ContMDiff nativeProductModel nativeProductModel ∞ e ∧
      ContMDiff nativeProductModel nativeProductModel ∞ e.symm ∧
      ∀ p, Y (e p) = X p

/-- Application of the additional explicit classical premise. Construction,
embedding and image equality remain ordinary actual inputs. -/
theorem classicalEmbeddedImages_reparametrize
    (background : ClassicalEmbeddedImageReparametrizationClaim)
    (X Y : NonrigidTorusSource → Ambient)
    (hX : NativeTorusSmoothEmbedding X) (hY : NativeTorusSmoothEmbedding Y)
    (himage : range X = range Y) :
    ∃ e : NonrigidTorusSource ≃ₜ NonrigidTorusSource,
      ContMDiff nativeProductModel nativeProductModel ∞ e ∧
      ContMDiff nativeProductModel nativeProductModel ∞ e.symm ∧
      ∀ p, Y (e p) = X p :=
  background X Y hX hY himage

end
end TightVer401
