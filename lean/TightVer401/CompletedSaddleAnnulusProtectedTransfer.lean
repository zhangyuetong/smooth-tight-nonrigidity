import TightVer401.CompletedSaddleAnnulusProtectedBand
import TightVer401.QuadraticRadialFillingBoundaryGerms

/-! Actual scalar germ locality and smooth protected-chart composition. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem completedSaddleAnnulusSupport_eq_of_germ {G H : Coord → ℝ} {p : Coord}
    (h : G =ᶠ[𝓝 p] H) : planarSupportMap G p = planarSupportMap H p := by
  have hv := h.eq_of_nhds
  have hg := quadraticRadialFilling_gradient_eq_of_germ h
  have h0 : coordPartial 0 G p = coordPartial 0 H p := congrFun hg 0
  have h1 : coordPartial 1 G p = coordPartial 1 H p := congrFun hg 1
  unfold planarSupportMap
  rw [hv,h0,h1]

/-- Construct the protected coordinate output by composing actual support
coordinates and deriving literal affine equality from actual scalar germs. -/
def completedSaddleAnnulusProtectedBand_of_support_coordinates
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (K : Set (AddCircle T × Ioo (0 : ℝ) w)) (a : ℝ)
    (G0 Gtilde : Coord → ℝ)
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (c1 : OpenPartialHomeomorph Coord (AddCircle (2 * Real.pi) × ℝ))
    (hK : K ⊆ (c0.trans c1).source)
    (hTarget : c1.target ⊆ univ ×ˢ Ioo (0 : ℝ) Real.pi)
    (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
    (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
    (hc1 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c1 c1.source)
    (hci1 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c1.symm c1.target)
    (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
    (hScalar : ∀ p ∈ (c0.trans c1).source, Gtilde =ᶠ[𝓝 (c0 p)] G0)
    (hCompleted : ∀ p ∈ c1.source,
      S (c1 p) = -planarSupportMap Gtilde p + a • revolutionAxis) :
    CompletedSaddleAnnulusProtectedBand d S K a where
  coordinates := c0.trans c1
  protected_source := hK
  interior_target := fun _ hx => hTarget hx.1
  coordinates_smooth := by
    change ContMDiffOn nativeProductModel nativeProductModel ∞ (c1 ∘ c0)
      (c0.source ∩ c0 ⁻¹' c1.source)
    exact hc1.comp (hc0.mono inter_subset_left) (fun _ hx => hx.2)
  inverse_smooth := by
    change ContMDiffOn nativeProductModel nativeProductModel ∞ (c0.symm ∘ c1.symm)
      (c1.target ∩ c1.symm ⁻¹' c0.target)
    exact hci0.comp (hci1.mono inter_subset_left) (fun _ hx => hx.2)
  affine_eq := by
    intro p hp
    change S (c1 (c0 p)) = -d.bandMap p + a • revolutionAxis
    rw [hCompleted (c0 p) hp.2,
      completedSaddleAnnulusSupport_eq_of_germ (hScalar p hp), hBand p hp.1]

end
end TightVer401
