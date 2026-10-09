import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.IdentityBandBendingPullback
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.Support

/-! Literal transport of a protected band field to the native torus.
Smooth extension uses Mathlib's compact-support extension by zero.
The actual strain transfer is assembled separately. -/
open Manifold
open scoped Manifold ContDiff Topology Classical
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

variable {T w : ℝ} [Fact (0 < T)]

/-- The affine translation acts on the surface; only the linear isometry
acts on its bending field. -/
def protectedTorusBendingField
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (q : NonrigidTorusSource) : Ambient :=
  if q ∈ e.target then A.linearIsometryEquiv (Y (e.symm q)) else 0

theorem protectedTorusBendingField_of_mem
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    {q : NonrigidTorusSource} (hq : q ∈ e.target) :
    protectedTorusBendingField e A Y q = A.linearIsometryEquiv (Y (e.symm q)) :=
  if_pos hq

theorem protectedTorusBendingField_of_notMem
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    {q : NonrigidTorusSource} (hq : q ∉ e.target) :
    protectedTorusBendingField e A Y q = 0 :=
  if_neg hq

theorem protectedTorusBendingField_source
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    protectedTorusBendingField e A Y (e p) = A.linearIsometryEquiv (Y p) := by
  rw [protectedTorusBendingField_of_mem e A Y (e.map_source hp), e.left_inv hp]

theorem protectedTorusBendingField_eventually_eq
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    {q : NonrigidTorusSource} (hq : q ∈ e.target) :
    protectedTorusBendingField e A Y =ᶠ[𝓝 q]
      (fun x => A.linearIsometryEquiv (Y (e.symm x))) := by
  filter_upwards [e.open_target.mem_nhds hq] with x hx
  exact protectedTorusBendingField_of_mem e A Y hx

/-- The whole support image is compact even when the chart itself is only
continuous on its open source. -/
theorem protectedTorusBendingField_support_image_isCompact
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source) :
    IsCompact (e '' tsupport Y) :=
  hcompact.image_of_continuousOn (e.continuousOn.mono hsupport)

theorem protectedTorusBendingField_tsupport
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source) :
    tsupport (protectedTorusBendingField e A Y) ⊆ e '' tsupport Y := by
  apply closure_minimal ?_
    (protectedTorusBendingField_support_image_isCompact e hcompact hsupport).isClosed
  intro q hq
  change protectedTorusBendingField e A Y q ≠ 0 at hq
  by_cases ht : q ∈ e.target
  · have hy : Y (e.symm q) ≠ 0 := by
      intro hz
      rw [protectedTorusBendingField_of_mem e A Y ht, hz, map_zero] at hq
      exact hq rfl
    exact ⟨e.symm q, subset_tsupport Y hy, e.right_inv ht⟩
  · exact False.elim (hq (protectedTorusBendingField_of_notMem e A Y ht))

theorem protectedTorusBendingField_hasCompactSupport
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source) :
    HasCompactSupport (protectedTorusBendingField e A Y) :=
  (protectedTorusBendingField_support_image_isCompact e hcompact hsupport).of_isClosed_subset
    (isClosed_tsupport _) (protectedTorusBendingField_tsupport e A hcompact hsupport)

theorem protectedTorusBendingField_eventually_zero
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    {q : NonrigidTorusSource} (hq : q ∉ e '' tsupport Y) :
    protectedTorusBendingField e A Y =ᶠ[𝓝 q] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun h => hq (protectedTorusBendingField_tsupport e A hcompact hsupport h))

theorem protectedTorusBendingField_nonzero
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hsupport : tsupport Y ⊆ e.source) (hnonzero : ∃ p, Y p ≠ 0) :
    ∃ q, protectedTorusBendingField e A Y q ≠ 0 := by
  obtain ⟨p, hp⟩ := hnonzero
  refine ⟨e p, ?_⟩
  rw [protectedTorusBendingField_source e A Y (hsupport (subset_tsupport Y hp))]
  intro hz
  apply hp
  exact A.linearIsometryEquiv.injective (by simpa only [map_zero] using hz)

/-- Reuse compact-support extension by zero on the actual open target
subtype, rather than constructing another extension mechanism. -/
theorem protectedTorusBendingField_contMDiff
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (heI : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (protectedTorusBendingField e A Y) := by
  let U : TopologicalSpace.Opens (AddCircle T × Ioo (0 : ℝ) w) :=
    ⟨e.source, e.open_source⟩
  let V : TopologicalSpace.Opens NonrigidTorusSource := ⟨e.target, e.open_target⟩
  let H : U ≃ₜ V := e.toHomeomorphSourceTarget
  let Ys : U → Ambient := Y ∘ Subtype.val
  let f : V → Ambient := fun q => A.linearIsometryEquiv (Ys (H.symm q))
  have hYs : HasCompactSupport Ys := by
    apply hasCompactSupport_pullback_of_embedding Topology.IsEmbedding.subtypeVal hcompact
    intro p hp
    exact ⟨⟨p, hsupport hp⟩, rfl⟩
  have hfcompact : HasCompactSupport f := by
    exact (hYs.comp_homeomorph H.symm).comp_left A.linearIsometryEquiv.map_zero
  have hi : ContMDiff nativeProductModel nativeProductModel ∞
      (fun q : V => e.symm q.val) :=
    heI.comp_contMDiff (contMDiff_subtype_val (U := V)) (fun q => q.property)
  have hf : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ f := by
    exact A.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap.contMDiff.comp
      (hY.comp hi)
  have hdiff : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (Subtype.val.extend f (fun _ : NonrigidTorusSource => (0 : Ambient))) :=
    ContMDiff.extend_zero hfcompact hf
  have hext : Subtype.val.extend f (fun _ : NonrigidTorusSource => (0 : Ambient)) =
      protectedTorusBendingField e A Y := by
    funext q
    by_cases hq : q ∈ e.target
    · have hv : (Subtype.val.extend f (fun _ : NonrigidTorusSource => (0 : Ambient))) q =
          f ⟨q, hq⟩ :=
        Subtype.val_injective.extend_apply f (fun _ => 0) ⟨q, hq⟩
      rw [hv, protectedTorusBendingField_of_mem e A Y hq]
      rfl
    · rw [Function.extend_apply' f (fun _ : NonrigidTorusSource => (0 : Ambient)) q ?_,
        protectedTorusBendingField_of_notMem e A Y hq]
      rintro ⟨z, hz⟩
      exact hq (hz ▸ z.property)
  rwa [hext] at hdiff

end
end TightVer401
