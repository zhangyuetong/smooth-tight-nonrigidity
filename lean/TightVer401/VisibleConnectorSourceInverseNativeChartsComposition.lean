import TightVer401.VisibleConnectorSourceInverseNativeChartsOpen
import TightVer401.VisibleConnectorSourceInverseGlobal

/-! Native open/closed cylinder charts of the SAME actual source inverse.
The inverse and closed homeomorphism here are consumed intermediate outputs;
the ordinary raw-data application constructs them before calling this adapter. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
set_option backward.isDefEq.respectTransparency false

def visibleConnectorSourceInverseNativeRawSource (L : ℝ) (F : Coord → Coord)
    (q : Coord) : Coord := F (saddlePolarChart ![1 + q 1, 2 * Real.pi * q 0 / L])

def visibleConnectorSourceInverseNativeSource (L : ℝ) [Fact (0 < L)]
    (F : Coord → Coord) (p : AddCircle L × Icc (0 : ℝ) 1) : Coord :=
  F (visibleConnectorSourceInverseNativeRound L (p.1, (p.2 : ℝ)))

/-- Compose the actual standard native charts with the already constructed
actual open inverse and closed source homeomorphism. -/
theorem visibleConnectorSourceInverse_native_charts_of_actual_inverse
    (L : ℝ) [Fact (0 < L)] {F : Coord → Coord} {Ho Hi : ℂ ≃ₜ ℂ}
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hF : ContDiffOn ℝ ∞ F {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2})
    (e0 : OpenPartialHomeomorph Coord Coord)
    (he0S : e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2})
    (he0T : e0.target = annularCoordJordanInterior Ho Hi)
    (he0F : (e0 : Coord → Coord) = F)
    (hi0 : ContDiffOn ℝ ∞ e0.symm e0.target)
    (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
      annularCoordJordanClosure Ho Hi)
    (hH : ∀ z, (H z : Coord) = F z) :
    ∃ (P : OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) 1) Coord)
      (HN : (AddCircle L × Icc (0 : ℝ) 1) ≃ₜ
        ↥(closure (annularCoordJordanInterior Ho Hi))),
      Continuous (visibleConnectorSourceInverseNativeSource L F) ∧
      (∀ s (t : Icc (0 : ℝ) 1),
        visibleConnectorSourceInverseNativeSource L F (periodProjection L s, t) =
          visibleConnectorSourceInverseNativeRawSource L F ![s, (t : ℝ)]) ∧
      (∀ p, (HN p : Coord) = visibleConnectorSourceInverseNativeSource L F p) ∧
      P.source = univ ∧ P.target = annularCoordJordanInterior Ho Hi ∧
      (∀ p, P p = visibleConnectorSourceInverseNativeSource L F
        (p.1, ⟨(p.2 : ℝ), ⟨p.2.property.1.le, p.2.property.2.le⟩⟩)) ∧
      ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ P ∧
      ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ P.symm
        (annularCoordJordanInterior Ho Hi) := by
  let P0 := visibleConnectorSourceInverse_native_round_chart L
  let P := P0.trans e0
  let HN := ((visibleConnectorSourceInverse_native_round_closure L).trans H).trans
    (Homeomorph.setCongr (closure_annularCoordJordanInterior Ho Hi hNested).symm)
  have hP0S : P0.source = univ := visibleConnectorSourceInverse_native_round_chart_source L
  have hP0T : P0.target = e0.source :=
    (visibleConnectorSourceInverse_native_round_chart_target L).trans he0S.symm
  have hPS : P.source = univ := by
    ext p
    rw [OpenPartialHomeomorph.trans_source]
    simp only [mem_inter_iff, mem_preimage, hP0S, mem_univ, true_and]
    exact iff_true_intro (hP0T ▸ P0.map_source (hP0S.symm ▸ mem_univ p))
  have hPT : P.target = annularCoordJordanInterior Ho Hi := by
    ext y
    rw [OpenPartialHomeomorph.trans_target]
    constructor
    · intro hy
      exact he0T ▸ hy.1
    · intro hy
      have hy0 : y ∈ e0.target := he0T.symm ▸ hy
      exact ⟨hy0, hP0T.symm ▸ e0.map_target hy0⟩
  have hHActual : ∀ p, (HN p : Coord) = visibleConnectorSourceInverseNativeSource L F p := by
    intro p
    change (H (visibleConnectorSourceInverse_native_round_closure L p) : Coord) = _
    rw [hH, visibleConnectorSourceInverse_native_round_closure_apply]
    rfl
  have hCont : Continuous (visibleConnectorSourceInverseNativeSource L F) := by
    have heq : visibleConnectorSourceInverseNativeSource L F =
        fun p => (HN p : Coord) := funext (fun p => (hHActual p).symm)
    rw [heq]
    exact continuous_subtype_val.comp HN.continuous
  have hMap : MapsTo P0 univ {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} := by
    intro p hp
    rw [← visibleConnectorSourceInverse_native_round_chart_target L]
    exact P0.map_source (hP0S.symm ▸ hp)
  have hSmooth : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ P := by
    change ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ (e0 ∘ P0)
    rw [he0F]
    apply contMDiffOn_univ.mp
    exact hF.contMDiffOn.comp
      (visibleConnectorSourceInverse_native_round_chart_contMDiff L).contMDiffOn hMap
  have hInverse : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ P.symm
      (annularCoordJordanInterior Ho Hi) := by
    change ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ (P0.symm ∘ e0.symm) _
    apply (visibleConnectorSourceInverse_native_round_chart_symm_contMDiffOn L).comp
      (hi0.mono (by rw [he0T])).contMDiffOn
    intro y hy
    rw [← he0S]
    exact e0.map_target (he0T.symm ▸ hy)
  refine ⟨P, HN, hCont, ?_, hHActual, hPS, hPT, ?_, hSmooth, hInverse⟩
  · intro s t
    unfold visibleConnectorSourceInverseNativeSource
    rw [visibleConnectorSourceInverse_native_round_representative]
    rfl
  · intro p
    change e0 (P0 p) = _
    rw [he0F, visibleConnectorSourceInverse_native_round_chart_apply]
    rfl

end
end TightVer401
