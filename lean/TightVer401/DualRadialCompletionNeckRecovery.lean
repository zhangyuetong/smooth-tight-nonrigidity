import TightVer401.DualRadialCompletionLegendreGerms
import TightVer401.QuadraticRadialFillingBoundaryGerms

/-! Exact outer scalar recovery through the neck's actual inverse. The dual
overlap is an ordinary open subset of the same incoming gradient collar. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem dualRadialCompletionNeck_legendre_recovery
    {G F : Coord → ℝ} (eC eN : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G eC.source)
    (hi : ContDiffOn ℝ ∞ eC.symm eC.target)
    (hC : ∀ p ∈ eC.source, eC p = planarGradient G p)
    (hN : (eN : Coord → Coord) = planarGradient F)
    {W : Set Coord} (hW : IsOpen W) (hWC : W ⊆ eC.target)
    (hWN : W ⊆ eN.source) (hEq : EqOn F (planarLegendre G eC) W) :
    let V := eC.source ∩ (eC : Coord → Coord) ⁻¹' W
    IsOpen V ∧ V ⊆ eN.target ∧
      EqOn (planarLegendre F eN) G V ∧
      ∀ p ∈ V, planarLegendre F eN =ᶠ[𝓝 p] G := by
  let V := eC.source ∩ (eC : Coord → Coord) ⁻¹' W
  have hV : IsOpen V :=
    eC.continuousOn.isOpen_inter_preimage eC.open_source hW
  have hForward (p : Coord) (hp : p ∈ V) : eN (eC p) = p := by
    have hGerm : F =ᶠ[𝓝 (eC p)] planarLegendre G eC := by
      filter_upwards [hW.mem_nhds hp.2] with y hy
      exact hEq hy
    rw [hN, quadraticRadialFilling_gradient_eq_of_germ hGerm,
      planarLegendre_gradient eC hG hi hC (hWC hp.2)]
    exact eC.left_inv hp.1
  have hTarget : V ⊆ eN.target := by
    intro p hp
    rw [← hForward p hp]
    exact eN.map_source (hWN hp.2)
  have hRecovery : EqOn (planarLegendre F eN) G V := by
    intro p hp
    have hInverse : eN.symm p = eC p := by
      calc
        eN.symm p = eN.symm (eN (eC p)) :=
          congrArg eN.symm (hForward p hp).symm
        _ = eC p := eN.left_inv (hWN hp.2)
    change eN.symm p ⬝ᵥ p - F (eN.symm p) = G p
    rw [hInverse, hEq hp.2]
    exact dualRadialCompletionLegendre_involutive G eC hp.1
  refine ⟨hV, hTarget, hRecovery, ?_⟩
  intro p hp
  filter_upwards [hV.mem_nhds hp] with q hq
  exact hRecovery hq

end
end TightVer401
