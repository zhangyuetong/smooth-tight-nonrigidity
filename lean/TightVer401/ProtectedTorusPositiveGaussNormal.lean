import TightVer401.ProtectedTorusPositiveGaussNormalCore
import TightVer401.ProtectedTorusPositiveGaussNormalCalculus
import TightVer401.ParabolicConvexClosureGaussSmoothNative

/-! The actual smooth normal of the literal protected torus assembly.

Its restriction to the convex half is exactly the outward native Gauss map of
that same input meridian. The orientation is established by a strictly positive
actual cross-product scale, using cosine height on (pi,2pi).
-/
open scoped Manifold ContDiff Topology Matrix RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance protectedPositiveGaussAssemblyPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual cross field of the literal assembled map. -/
def protectedTorusPositiveGaussCross {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) : NonrigidTorusSource → Ambient :=
  nativeTorusImmersionCross (protectedTorusMap d.saddle d.meridian h)

theorem protectedTorusPositiveGaussCross_ne_zero {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (p : NonrigidTorusSource) :
    protectedTorusPositiveGaussCross d p ≠ 0 :=
  nativeTorusImmersionCross_ne_zero (protectedTorusMap_contMDiff_and_immersion d).2 p

/-- Sphere-valued actual normalized native-frame cross of the literal assembly. -/
def protectedTorusPositiveGaussNormal {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) : NonrigidTorusSource → RoundSphere :=
  nativeTorusImmersionNormal (protectedTorusMap d.saddle d.meridian h)
    (protectedTorusMap_contMDiff_and_immersion d).2

theorem protectedTorusPositiveGaussNormal_contMDiff {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    ContMDiff nativeProductModel (𝓡 2) ∞ (protectedTorusPositiveGaussNormal d) :=
  nativeTorusImmersionNormal_contMDiff (protectedTorusMap_contMDiff_and_immersion d).1
    (protectedTorusMap_contMDiff_and_immersion d).2

theorem protectedTorusPositiveGaussNormal_orthogonal {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (p : NonrigidTorusSource) (v : ℝ × ℝ) :
    inner ℝ (protectedTorusPositiveGaussNormal d p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (protectedTorusMap d.saddle d.meridian h) p v : Ambient) = 0 :=
  nativeTorusImmersionNormal_orthogonal (protectedTorusMap_contMDiff_and_immersion d).2 p v

private theorem protectedPositiveGauss_rotation_cross (R k s θ : ℝ) :
    ambientCross ((k * s) • revolutionRadial θ + k • revolutionAxis)
      (R • revolutionAngular θ) =
    (-R * k) • revolutionRadial θ + (R * k * s) • revolutionAxis := by
  ext i
  fin_cases i <;>
    simp [ambientCross, cross_apply, revolutionRadial, revolutionAngular, revolutionAxis,
      PiLp.add_apply, PiLp.smul_apply]
  · ring
  · ring
  · linear_combination R * k * s * (Real.sin_sq_add_cos_sq θ)

/-- Strictly positive outward cross scale on the actual convex parameter interval. -/
theorem protectedTorusPositiveGauss_convex_crossScale_pos {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) {φ : ℝ}
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    0 < -d.meridian (-h * Real.cos φ) * h * Real.sin φ *
      revolutionWeight (deriv d.meridian (-h * Real.cos φ)) := by
  have hr : 0 < d.meridian (-h * Real.cos φ) := lt_trans d.radius_pos
    (d.meridian_exterior _ (protectedTorusPositiveGauss_convex_height_mem d.height_pos hφ))
  have hs : Real.sin φ < 0 := by
    have ht := Real.sin_neg_of_neg_of_neg_pi_lt
      (show φ - 2 * Real.pi < 0 by linarith [hφ.2])
      (show -Real.pi < φ - 2 * Real.pi by linarith [hφ.1])
    simpa only [Real.sin_sub_two_pi] using ht
  exact mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) d.height_pos) hs)
    (revolutionWeight_pos _)

/-- Exact actual native cross equals a positive scale of the SAME meridian's outward normal. -/
theorem protectedTorusPositiveGauss_convex_cross {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (θ φ : ℝ)
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    protectedTorusPositiveGaussCross d
      (periodProjection (2 * Real.pi) θ, periodProjection (2 * Real.pi) φ) =
      (-d.meridian (-h * Real.cos φ) * h * Real.sin φ *
        revolutionWeight (deriv d.meridian (-h * Real.cos φ))) •
      parabolicConvexClosureNativeOutwardNormal d.meridian
        (parabolicConvexClosureHeightDomain h)
        (periodProjection (2 * Real.pi) θ,
          ⟨-h * Real.cos φ, by
            change -h * Real.cos φ ∈ Ioo (-h) h
            exact protectedTorusPositiveGauss_convex_height_mem d.height_pos hφ⟩) := by
  unfold protectedTorusPositiveGaussCross nativeTorusImmersionCross
  rw [protectedTorusPositiveGauss_convex_mfderiv d θ φ hφ (0, 1),
    protectedTorusPositiveGauss_convex_mfderiv d θ φ hφ (1, 0)]
  simp only [Prod.fst, Prod.snd, zero_mul, one_mul, mul_zero, mul_one,
    smul_zero, zero_smul, add_zero, zero_add]
  rw [show deriv d.meridian (-h * Real.cos φ) * (h * Real.sin φ) =
      (h * Real.sin φ) * deriv d.meridian (-h * Real.cos φ) by ring,
    protectedPositiveGauss_rotation_cross]
  simp only [parabolicConvexClosureNativeOutwardNormal,
    parabolicConvexClosureHeightInclusion, revolutionEndCircleNormal,
    revolutionCircleRadial_representative, revolutionNormalHeight]
  have hw : revolutionWeight (deriv d.meridian (-h * Real.cos φ)) ≠ 0 :=
    (revolutionWeight_pos _).ne'
  ext i
  fin_cases i <;>
    simp [revolutionRadial, revolutionAxis, PiLp.add_apply, PiLp.smul_apply] <;>
    simp only [neg_mul] at hw ⊢ <;>
    field_simp [hw] <;> ring

/-- The global actual unit normal restricts to the SAME actual native outward Gauss map. -/
theorem protectedTorusPositiveGaussNormal_convex {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (q : AddCircle (2 * Real.pi)) (φ : ℝ)
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    protectedTorusPositiveGaussNormal d (q, periodProjection (2 * Real.pi) φ) =
      parabolicConvexClosureNativeOutwardGauss d.meridian
        (parabolicConvexClosureHeightDomain h)
        (q, ⟨-h * Real.cos φ, by
          change -h * Real.cos φ ∈ Ioo (-h) h
          exact protectedTorusPositiveGauss_convex_height_mem d.height_pos hφ⟩) := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective q
  have hq : periodProjection (2 * Real.pi) θ = q := hθ
  rw [← hq]
  apply Subtype.ext
  change NormedSpace.normalize (protectedTorusPositiveGaussCross d
    (periodProjection (2 * Real.pi) θ, periodProjection (2 * Real.pi) φ)) = _
  rw [protectedTorusPositiveGauss_convex_cross d θ φ hφ,
    NormedSpace.normalize_smul_of_pos (protectedTorusPositiveGauss_convex_crossScale_pos d hφ)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (parabolicConvexClosureNativeOutwardNormal_norm _ _ _)

end
end TightVer401

