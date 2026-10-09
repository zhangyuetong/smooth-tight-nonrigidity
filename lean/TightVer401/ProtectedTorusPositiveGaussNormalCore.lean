import TightVer401.ProtectedTorusPositiveGaussNormalFrame
import TightVer401.AmbientCross
import TightVer401.SphereCharts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Actual global normal of an arbitrary smooth native torus immersion.

The cross product uses the actual two constant native differential directions,
with height direction first. Injectivity proves its nonvanishing. Normalization
then produces a smooth unit normal orthogonal to every actual tangent vector.
The quotient-chart frame smoothness is proved in the imported helper.
-/
open scoped Manifold ContDiff Topology Matrix RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance protectedPositiveGaussNormalDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Cross product of the actual height and circle differential vectors. -/
def nativeTorusImmersionCross (F : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) : Ambient :=
  ambientCross (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (0, 1))
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (1, 0))

/-- Injectivity of the actual differential makes the cross product nonzero. -/
theorem nativeTorusImmersionCross_ne_zero {F : NonrigidTorusSource → Ambient}
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (p : NonrigidTorusSource) : nativeTorusImmersionCross F p ≠ 0 := by
  let D : (ℝ × ℝ) →L[ℝ] Ambient := mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p
  have hli : LinearIndependent ℝ ![(fun i : Fin 3 => D (0, 1) i),
      (fun i : Fin 3 => D (1, 0) i)] := by
    rw [linearIndependent_fin2]
    constructor
    · intro he
      have he' : (D (1, 0) : Ambient) = 0 := by ext i; exact congrFun he i
      have hv : ((1, 0) : ℝ × ℝ) = 0 := himm p (he'.trans D.map_zero.symm)
      exact one_ne_zero (congrArg Prod.fst hv)
    · intro a he
      have he' : (D (a, 0) : Ambient) = D (0, 1) := by
        have ha : ((a, 0) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) := by simp
        rw [ha, map_smul]
        ext i
        exact congrFun he i
      have hv := himm p he'
      exact zero_ne_one (congrArg Prod.snd hv)
  have hx := crossProduct_ne_zero_iff_linearIndependent.mpr hli
  intro hz
  apply hx
  ext i
  exact congrArg (fun v : Ambient => v i) hz

private theorem protectedPositiveGauss_cross_contDiff :
    ContDiff ℝ ∞ (fun p : Ambient × Ambient => ambientCross p.1 p.2) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have heval (i : Fin 3) : ContDiff ℝ ∞ (fun v : Ambient => v i) :=
    ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).contDiff
  have hc : ContDiff ℝ ∞ (fun p : Ambient × Ambient =>
      crossProduct (fun i => p.1 i) (fun i => p.2 i)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp only [cross_apply] <;>
      exact ((heval _).comp contDiff_fst |>.mul ((heval _).comp contDiff_snd)).sub
        ((heval _).comp contDiff_fst |>.mul ((heval _).comp contDiff_snd))
  exact e.symm.contDiff.comp hc

/-- Smoothness of the actual cross field, without a supplied frame hypothesis. -/
theorem nativeTorusImmersionCross_contMDiff {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (nativeTorusImmersionCross F) := by
  have hvProd : ContMDiff nativeProductModel
      (𝓘(ℝ, Ambient).prod 𝓘(ℝ, Ambient)) ∞
      (fun p => ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (0, 1) : Ambient),
        (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (1, 0) : Ambient))) :=
    (protectedTorusPositiveGauss_nativeFrame_contMDiff hF (0, 1)).prodMk
      (protectedTorusPositiveGauss_nativeFrame_contMDiff hF (1, 0))
  have hv : ContMDiff nativeProductModel 𝓘(ℝ, Ambient × Ambient) ∞
      (fun p => ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (0, 1) : Ambient),
        (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (1, 0) : Ambient))) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hvProd
    exact hvProd
  change ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
    ((fun p : Ambient × Ambient => ambientCross p.1 p.2) ∘
      (fun p => ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (0, 1) : Ambient),
        (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p (1, 0) : Ambient))))
  exact protectedPositiveGauss_cross_contDiff.comp_contMDiff hv

/-- Sphere-valued normalization of the actual cross product. -/
def nativeTorusImmersionNormal (F : NonrigidTorusSource → Ambient)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (p : NonrigidTorusSource) : RoundSphere :=
  ⟨NormedSpace.normalize (nativeTorusImmersionCross F p), by
    simpa using NormedSpace.norm_normalize (nativeTorusImmersionCross_ne_zero himm p)⟩

/-- The global normalized cross is actually smooth as a sphere-valued map. -/
theorem nativeTorusImmersionNormal_contMDiff {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p)) :
    ContMDiff nativeProductModel (𝓡 2) ∞ (nativeTorusImmersionNormal F himm) := by
  have hx := nativeTorusImmersionCross_contMDiff hF
  have hn : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p => ‖nativeTorusImmersionCross F p‖) := by
    intro p
    have hnorm : ContDiffAt ℝ ∞ (fun v : Ambient => ‖v‖)
        (nativeTorusImmersionCross F p) :=
      contDiffAt_norm ℝ (nativeTorusImmersionCross_ne_zero himm p)
    exact hnorm.contMDiffAt.comp p (hx p)
  have hs : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p => NormedSpace.normalize (nativeTorusImmersionCross F p)) :=
    (hn.inv₀ (fun p => norm_ne_zero_iff.mpr (nativeTorusImmersionCross_ne_zero himm p))).smul hx
  exact hs.codRestrict_sphere (fun p => by
    simpa using NormedSpace.norm_normalize (nativeTorusImmersionCross_ne_zero himm p))

/-- Actual normal orthogonality for every actual native tangent direction. -/
theorem nativeTorusImmersionNormal_orthogonal {F : NonrigidTorusSource → Ambient}
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (p : NonrigidTorusSource) (v : ℝ × ℝ) :
    inner ℝ (nativeTorusImmersionNormal F himm p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p v : Ambient) = 0 := by
  let D : (ℝ × ℝ) →L[ℝ] Ambient := mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p
  have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  have h1 := ambientCross_orthogonal_right (D (0, 1)) (D (1, 0))
  have h2 := ambientCross_orthogonal_left (D (0, 1)) (D (1, 0))
  change inner ℝ (‖nativeTorusImmersionCross F p‖⁻¹ • nativeTorusImmersionCross F p)
    (D v : Ambient) = 0
  rw [hv, map_add, map_smul, map_smul]
  simp only [real_inner_smul_left, inner_add_right, real_inner_smul_right]
  change inner ℝ (D (1, 0)) (nativeTorusImmersionCross F p) = 0 at h1
  change inner ℝ (D (0, 1)) (nativeTorusImmersionCross F p) = 0 at h2
  have hc1 : inner ℝ (nativeTorusImmersionCross F p) (D (1, 0)) = 0 :=
    (real_inner_comm _ _).trans h1
  have hc2 : inner ℝ (nativeTorusImmersionCross F p) (D (0, 1)) = 0 :=
    (real_inner_comm _ _).trans h2
  simp only [hc1, hc2, mul_zero, add_zero]

end
end TightVer401




