import TightVer401.ProtectedTorusBendingExtension
import TightVer401.NativeProductPlaneForms

/-! The protected band field has actual zero strain after affine placement and
zero extension. This application uses the existing derivative chain rule. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Affine placement preserves the actual mixed differential pairing. -/
theorem protectedTorus_affine_pullback_zero_strain {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    {F Z : NonrigidTorusSource → Ambient} {q : NonrigidTorusSource}
    (hq : q ∈ e.target)
    (hF : F =ᶠ[𝓝 q] (fun z => A (X (e.symm z))))
    (hZ : Z =ᶠ[𝓝 q] (fun z => A.linearIsometryEquiv (Y (e.symm z)))) :
    ∀ v z : ℝ × ℝ, nativeProductLinearMetricForm F Z q v z = 0 := by
  let O := A.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hO (x : Ambient) : O x = A.linearIsometryEquiv x := rfl
  have hi := (he.contMDiffAt (e.open_target.mem_nhds hq)).mdifferentiableAt (by simp)
  have hx := ((hX (e.symm q)).mdifferentiableAt (by simp)).comp q hi
  have hy := ((hY.1 (e.symm q)).mdifferentiableAt (by simp)).comp q hi
  have hox := O.mdifferentiableAt.comp q hx
  have hoy := O.mdifferentiableAt.comp q hy
  have hfa : F =ᶠ[𝓝 q] (fun z => O (X (e.symm z)) + A 0) := by
    filter_upwards [hF] with z hz
    rw [hz]
    rw [hO]
    simpa only [vadd_eq_add, add_zero] using A.map_vadd (0 : Ambient) (X (e.symm z))
  have dx := mfderiv_comp q ((hX (e.symm q)).mdifferentiableAt (by simp)) hi
  have dy := mfderiv_comp q ((hY.1 (e.symm q)).mdifferentiableAt (by simp)) hi
  have dox := mfderiv_comp q O.mdifferentiableAt hx
  have doy := mfderiv_comp q O.mdifferentiableAt hy
  have dO : mfderiv 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) O (X (e.symm q)) = O := by
    rw [mfderiv_eq_fderiv]
    exact O.fderiv
  have dOY : mfderiv 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) O (Y (e.symm q)) = O := by
    rw [mfderiv_eq_fderiv]
    exact O.fderiv
  simp only [Function.comp_apply] at dox doy
  rw [dO, dx] at dox
  rw [dOY, dy] at doy
  have hza : Z =ᶠ[𝓝 q] (fun z => O (Y (e.symm z))) := by
    filter_upwards [hZ] with z hz
    rw [hz, hO]
  have dF : (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q :
      (ℝ × ℝ) →L[ℝ] Ambient) = O.comp
      ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) X (e.symm q)).comp
        (mfderiv nativeProductModel nativeProductModel e.symm q)) := by
    calc
      _ = (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (fun z => O (X (e.symm z)) + A 0) q : (ℝ × ℝ) →L[ℝ] Ambient) := hfa.mfderiv_eq
      _ = _ := by
        have hadd := mfderiv_add hox
          (mdifferentiableAt_const (I := nativeProductModel) (c := A 0) (x := q))
        have hder : (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
            (fun z => O (X (e.symm z)) + A 0) q : (ℝ × ℝ) →L[ℝ] Ambient) =
            mfderiv nativeProductModel 𝓘(ℝ, Ambient) (O ∘ X ∘ e.symm) q := by
          simp only [mfderiv_const, add_zero] at hadd
          convert! hadd using 1
        exact hder.trans dox
  have dZ : (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Z q :
      (ℝ × ℝ) →L[ℝ] Ambient) = O.comp
      ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y (e.symm q)).comp
        (mfderiv nativeProductModel nativeProductModel e.symm q)) := by
    calc
      _ = (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (fun z => O (Y (e.symm z))) q : (ℝ × ℝ) →L[ℝ] Ambient) := hza.mfderiv_eq
      _ = _ := doy
  intro v z
  unfold nativeProductLinearMetricForm
  rw [dF, dZ]
  change inner ℝ (A.linearIsometryEquiv
      (bandDifferential X (e.symm q) (mfderiv nativeProductModel nativeProductModel e.symm q v)))
    (A.linearIsometryEquiv
      (bandDifferential Y (e.symm q) (mfderiv nativeProductModel nativeProductModel e.symm q z))) +
    inner ℝ (A.linearIsometryEquiv
      (bandDifferential Y (e.symm q) (mfderiv nativeProductModel nativeProductModel e.symm q v)))
    (A.linearIsometryEquiv
      (bandDifferential X (e.symm q) (mfderiv nativeProductModel nativeProductModel e.symm q z))) = 0
  rw [A.linearIsometryEquiv.inner_map_map, A.linearIsometryEquiv.inner_map_map]
  exact hY.2 (e.symm q) _ _

end
end TightVer401
