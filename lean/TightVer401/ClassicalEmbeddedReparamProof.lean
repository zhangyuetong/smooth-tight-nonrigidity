import TightVer401.ClassicalEmbeddedReparam
import TightVer401.ClassicalEmbeddingSmoothFactor
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Homeomorph.Lemmas

/-! Equal-image reparameterization for the actual native smooth embeddings.
The topological identification is the composition of their range homeomorphisms.
Smoothness follows locally from the actual injective differential, without an
external embedded-submanifold or reparameterization premise. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem nativeEmbedding_coordinate_hasFDeriv
    {Y : NonrigidTorusSource → Ambient}
    {q : NonrigidTorusSource}
    (hY : ContMDiffAt nativeProductModel 𝓘(ℝ, Ambient) ∞ Y q) :
    HasFDerivAt (Y ∘ (extChartAt nativeProductModel q).symm)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y q)
      (extChartAt nativeProductModel q q) := by
  have hr : range nativeProductModel = univ :=
    ModelWithCorners.range_eq_univ nativeProductModel
  have h := (hY.mdifferentiableAt (by simp)).hasMFDerivAt.2
  rw [hr] at h
  convert! h.hasFDerivAt_of_univ using 1 <;>
    simp [writtenInExtChartAt, Function.comp_def]

/-- Smoothness of a continuous factor through an actual native immersion. -/
private theorem nativeEmbedding_contMDiff_factor
    {X Y : NonrigidTorusSource → Ambient} {u : NonrigidTorusSource → NonrigidTorusSource}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : NativeTorusSmoothEmbedding Y) (hu : Continuous u)
    (heq : ∀ p, Y (u p) = X p) :
    ContMDiff nativeProductModel nativeProductModel ∞ u := by
  intro p
  let cp := extChartAt nativeProductModel p
  let cq := extChartAt nativeProductModel (u p)
  let a : ℝ × ℝ := cp p
  let f : (ℝ × ℝ) → Ambient := Y ∘ cq.symm
  let g : (ℝ × ℝ) → (ℝ × ℝ) := cq ∘ u ∘ cp.symm
  have hr : range nativeProductModel = univ :=
    ModelWithCorners.range_eq_univ nativeProductModel
  have hcp : cp.symm a = p := cp.left_inv (mem_extChartAt_source p)
  have hga : g a = cq (u p) := by simp only [g, Function.comp_apply, hcp]
  have hf : ContDiffAt ℝ ∞ f (cq (u p)) := by
    have h := (contMDiffAt_iff_source.mp (hY.1 (u p)))
    rw [hr] at h
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Ambient) ∞ f (cq (u p)) := by
      simpa only [f, cq, contMDiffWithinAt_univ] using h
    exact h'.contDiffAt
  have hd := nativeEmbedding_coordinate_hasFDeriv (hY.1 (u p))
  change HasFDerivAt f (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y (u p))
    (cq (u p)) at hd
  have hi : Function.Injective (fderiv ℝ f (g a)) := by
    rw [hga, hd.fderiv]
    exact hY.2.1 (u p)
  have hcs : ContinuousAt cp.symm a := continuousAt_extChartAt_symm p
  have huc : ContinuousAt (u ∘ cp.symm) a := by
    simpa only [hcp] using (hu.continuousAt.comp hcs)
  have hg : ContinuousAt g a := by
    have hcq : ContinuousAt cq ((u ∘ cp.symm) a) := by
      simpa only [Function.comp_apply, hcp] using
        (continuousAt_extChartAt (I := nativeProductModel) (u p))
    exact hcq.comp huc
  have hnear : ∀ᶠ z in 𝓝 a, u (cp.symm z) ∈ cq.source := by
    apply huc.preimage_mem_nhds
    simpa only [Function.comp_apply, hcp] using
      (extChartAt_source_mem_nhds (I := nativeProductModel) (u p))
  have hfg : (f ∘ g) =ᶠ[𝓝 a] (X ∘ cp.symm) := by
    filter_upwards [hnear] with z hz
    change Y (cq.symm (cq (u (cp.symm z)))) = X (cp.symm z)
    rw [cq.left_inv hz]
    exact heq _
  have hXc : ContDiffAt ℝ ∞ (X ∘ cp.symm) a := by
    have h := contMDiffAt_iff_source.mp (hX p)
    rw [hr] at h
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Ambient) ∞ (X ∘ cp.symm) a := by
      simpa only [cp, a, contMDiffWithinAt_univ] using h
    exact h'.contDiffAt
  have hgSmooth : ContDiffAt ℝ ∞ g a :=
    classicalEmbedding_contDiffAt_factor (by simpa only [hga] using hf) hi hg
      (hXc.congr_of_eventuallyEq hfg)
  apply contMDiffAt_iff.mpr
  refine ⟨hu.continuousAt, ?_⟩
  rw [hr]
  exact hgSmooth.contDiffWithinAt

/-- The equal-image smooth reparameterization claim, with no external premise. -/
theorem classicalEmbeddedImageReparametrization_proved :
    ClassicalEmbeddedImageReparametrizationClaim := by
  intro X Y hX hY himage
  let ex := hX.2.2.toHomeomorph
  let ey := hY.2.2.toHomeomorph
  let e : NonrigidTorusSource ≃ₜ NonrigidTorusSource :=
    (ex.trans (Homeomorph.setCongr himage)).trans ey.symm
  have heq : ∀ p, Y (e p) = X p := by
    intro p
    change Y (ey.symm ((Homeomorph.setCongr himage) (ex p))) = X p
    have h := congrArg Subtype.val
      (ey.apply_symm_apply ((Homeomorph.setCongr himage) (ex p)))
    change Y (ey.symm ((Homeomorph.setCongr himage) (ex p))) = X p at h
    exact h
  have hsymm : ∀ p, X (e.symm p) = Y p := by
    intro p
    simpa only [e.apply_symm_apply] using (heq (e.symm p)).symm
  exact ⟨e, nativeEmbedding_contMDiff_factor hX.1 hY e.continuous heq,
    nativeEmbedding_contMDiff_factor hY.1 hX e.symm.continuous hsymm, heq⟩

end
end TightVer401


