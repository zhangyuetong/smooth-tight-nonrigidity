import TightVer401.SphereFrame
import OAI.Geometry.Borsuk.SphereGeometry.HemisphereChart

/-! OpenAI's normalized affine hemisphere chart, with actual two-dimensional
coordinate domain and a proved injective differential. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def sphereHemisphere (w : Ambient) (hw : w ≠ 0) : Coord → Ambient :=
  fun p => OAI.BorsukNine.hemisphereChart w (sphereTangentFrame w hw) (sphereCoordEquiv p)

def sphereHemisphereInverse (w : Ambient) (hw : w ≠ 0) : Ambient → Coord :=
  fun u => sphereCoordEquiv.symm
    (OAI.BorsukNine.hemisphereInverse w (sphereTangentFrame w hw) u)

theorem sphereHemisphere_contDiff (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) :
    ContDiff ℝ ∞ (sphereHemisphere w hw) :=
  (OAI.BorsukNine.hemisphereChart_contDiff w (sphereTangentFrame w hw) hunit
    (sphereTangentFrame_orthogonal w hw)).comp sphereCoordEquiv.contDiff

theorem sphereHemisphere_norm (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) (p : Coord) :
    ‖sphereHemisphere w hw p‖ = 1 :=
  OAI.BorsukNine.hemisphereChart_norm w (sphereTangentFrame w hw) hunit
    (sphereTangentFrame_orthogonal w hw) _

theorem sphereHemisphere_zero (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) :
    sphereHemisphere w hw 0 = w := by
  simp [sphereHemisphere, OAI.BorsukNine.hemisphereChart,
    OAI.BorsukNine.SimplicialChains.unitRadial, hunit]

theorem sphereHemisphere_inner_pos (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) (p : Coord) :
    0 < inner ℝ w (sphereHemisphere w hw p) :=
  OAI.BorsukNine.hemisphereChart_inner_pos w (sphereTangentFrame w hw) hunit
    (sphereTangentFrame_orthogonal w hw) _

theorem sphereHemisphere_left_inverse (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) (p : Coord) :
    sphereHemisphereInverse w hw (sphereHemisphere w hw p) = p := by
  change sphereCoordEquiv.symm (OAI.BorsukNine.hemisphereInverse w (sphereTangentFrame w hw)
    (OAI.BorsukNine.hemisphereChart w (sphereTangentFrame w hw) (sphereCoordEquiv p))) = p
  rw [OAI.BorsukNine.hemisphereInverse_chart w (sphereTangentFrame w hw) hunit
    (sphereTangentFrame_orthogonal w hw)]
  exact sphereCoordEquiv.symm_apply_apply p

theorem sphereHemisphere_right_inverse (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1)
    {u : Ambient} (hu : ‖u‖ = 1) (hwu : 0 < inner ℝ w u) :
    sphereHemisphere w hw (sphereHemisphereInverse w hw u) = u := by
  simp only [sphereHemisphere, sphereHemisphereInverse, sphereCoordEquiv.apply_symm_apply]
  exact OAI.BorsukNine.hemisphereChart_inverse w (sphereTangentFrame w hw) hunit
    (sphereTangentFrame_orthogonal w hw) (sphereTangentFrame_onto w hw) hu hwu

theorem sphereHemisphereInverse_contDiffAt (w : Ambient) (hw : w ≠ 0)
    {u : Ambient} (hwu : 0 < inner ℝ w u) :
    ContDiffAt ℝ ∞ (sphereHemisphereInverse w hw) u := by
  have hi : ContDiffAt ℝ ∞ (fun a : Ambient => (inner ℝ w a)⁻¹) u :=
    (contDiff_const.inner ℝ contDiff_id).contDiffAt.inv (ne_of_gt hwu)
  exact sphereCoordEquiv.symm.contDiff.contDiffAt.comp u
    (hi.smul (sphereTangentFrame w hw).toContinuousLinearMap.adjoint.contDiff.contDiffAt)

theorem sphereHemisphere_differential_injective (w : Ambient) (hw : w ≠ 0)
    (hunit : ‖w‖ = 1) (p : Coord) :
    Function.Injective (fderiv ℝ (sphereHemisphere w hw) p) := by
  have hQ := (sphereHemisphere_contDiff w hw hunit).differentiable (by simp)
  have hI := (sphereHemisphereInverse_contDiffAt w hw
    (sphereHemisphere_inner_pos w hw hunit p)).differentiableAt (by simp)
  have he : (fun q => sphereHemisphereInverse w hw (sphereHemisphere w hw q)) =
      (fun q : Coord => q) := funext (sphereHemisphere_left_inverse w hw hunit)
  have hd := fderiv_comp p hI (hQ p)
  change fderiv ℝ (fun q => sphereHemisphereInverse w hw (sphereHemisphere w hw q)) p =
    (fderiv ℝ (sphereHemisphereInverse w hw) (sphereHemisphere w hw p)).comp
      (fderiv ℝ (sphereHemisphere w hw) p) at hd
  have hid : fderiv ℝ (fun q : Coord => q) p = ContinuousLinearMap.id ℝ Coord :=
    (hasFDerivAt_id p).fderiv
  rw [he, hid] at hd
  intro v z hvz
  have hh := congrArg (fderiv ℝ (sphereHemisphereInverse w hw)
    (sphereHemisphere w hw p)) hvz
  change ((fderiv ℝ (sphereHemisphereInverse w hw) (sphereHemisphere w hw p)).comp
    (fderiv ℝ (sphereHemisphere w hw) p)) v =
    ((fderiv ℝ (sphereHemisphereInverse w hw) (sphereHemisphere w hw p)).comp
    (fderiv ℝ (sphereHemisphere w hw) p)) z at hh
  rw [← hd] at hh
  exact hh

theorem sphereHemisphere_metric (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) :
    SmoothPositiveOn (inducedMetric (sphereHemisphere w hw)) univ ∧
    IsometricOn (inducedMetric (sphereHemisphere w hw)) (sphereHemisphere w hw) univ := by
  have hQ : ContDiffOn ℝ ∞ (sphereHemisphere w hw) univ :=
    (sphereHemisphere_contDiff w hw hunit).contDiffOn
  exact ⟨inducedMetric_smoothPositiveOn hQ isOpen_univ
    (fun p _ => sphereHemisphere_differential_injective w hw hunit p),
    inducedMetric_isometricOn hQ⟩

end
end TightVer401
