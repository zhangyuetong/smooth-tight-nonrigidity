import TightVer401.ParabolicConvexClosureGaussSmooth
import TightVer401.ParabolicConvexClosureGeometryNative
import TightVer401.RevolutionEndAngleInverseSmooth
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Actual global outward Gauss coordinates of the native convex meridian.

Only interior smoothness, negative actual radius acceleration and literal
parabolic radius germs are inputs. The actual circle angle and constructed
height inverse give the global Gauss inverse. Its smoothness and left-inverse
identity prove injectivity of the actual ambient-normal mfderiv. The sphere
target is the genuine open belt with height in (-1,1); no global image,
injectivity, differential regularity or diffeomorphism package is assumed.
-/

open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance parabolicGaussSmoothPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance parabolicGaussSmoothDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

def parabolicConvexClosureHeightDomain (h : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-h) h, isOpen_Ioo⟩

def parabolicConvexClosureSphereBelt : TopologicalSpace.Opens RoundSphere :=
  ⟨{n | n.val 2 ∈ Ioo (-1 : ℝ) 1},
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      continuous_subtype_val).isOpen_preimage _ isOpen_Ioo⟩

/-- The actual belt is exactly the sphere with its two axis poles removed. -/
theorem parabolicConvexClosureSphereBelt_eq_poles_compl :
    (parabolicConvexClosureSphereBelt : Set RoundSphere) =
      {n | n.val ≠ revolutionAxis ∧ n.val ≠ -revolutionAxis} := by
  ext n
  change n.val 2 ∈ Ioo (-1 : ℝ) 1 ↔ _
  constructor
  · intro hn
    constructor
    · intro he
      have ht := hn.2
      rw [he] at ht
      change (1 : ℝ) < 1 at ht
      exact (lt_irrefl _ ht)
    · intro he
      have ht := hn.1
      rw [he] at ht
      change (-1 : ℝ) < -1 at ht
      exact (lt_irrefl _ ht)
  · rintro ⟨hnorth, hsouth⟩
    have hs := revolutionSphere_horizontal_sq n
    have hlo : -1 ≤ n.val 2 := by nlinarith [sq_nonneg (n.val 0), sq_nonneg (n.val 1)]
    have hup : n.val 2 ≤ 1 := by nlinarith [sq_nonneg (n.val 0), sq_nonneg (n.val 1)]
    have hplus : n.val 2 ≠ 1 := by
      intro h2
      rw [h2] at hs
      have h0 : n.val 0 = 0 := by nlinarith [sq_nonneg (n.val 1)]
      have h1 : n.val 1 = 0 := by nlinarith [sq_nonneg (n.val 0)]
      apply hnorth
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [revolutionAxis, h0, h1, h2]
    have hminus : n.val 2 ≠ -1 := by
      intro h2
      rw [h2] at hs
      have h0 : n.val 0 = 0 := by nlinarith [sq_nonneg (n.val 1)]
      have h1 : n.val 1 = 0 := by nlinarith [sq_nonneg (n.val 0)]
      apply hsouth
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [revolutionAxis, h0, h1, h2]
    exact ⟨lt_of_le_of_ne hlo hminus.symm, lt_of_le_of_ne hup hplus⟩

def parabolicConvexClosureHorizontalComplex (n : Ambient) : ℂ := ⟨n 0, n 1⟩

theorem parabolicConvexClosureHorizontalComplex_contDiff :
    ContDiff ℝ ∞ parabolicConvexClosureHorizontalComplex := by
  have he : parabolicConvexClosureHorizontalComplex = fun n => -revolutionGaussHorizontal n := by
    funext n
    apply Complex.ext <;> simp [parabolicConvexClosureHorizontalComplex, revolutionGaussHorizontal]
  rw [he]
  exact revolutionGaussHorizontal_contDiff.neg

def parabolicConvexClosureOutwardAngle (n : Ambient) : AddCircle (2 * Real.pi) :=
  periodProjection (2 * Real.pi) (parabolicConvexClosureHorizontalComplex n).arg

theorem parabolicConvexClosure_horizontal_ne_zero (n : RoundSphere)
    (hn : n.val 2 ∈ Ioo (-1 : ℝ) 1) : parabolicConvexClosureHorizontalComplex n.val ≠ 0 := by
  intro he
  have h0 := congrArg Complex.re he
  have h1 := congrArg Complex.im he
  change n.val 0 = 0 at h0
  change n.val 1 = 0 at h1
  have hs := revolutionSphere_horizontal_sq n
  rw [h0, h1] at hs
  nlinarith [hn.1, hn.2]

theorem parabolicConvexClosureOutwardAngle_contMDiffAt {n : Ambient}
    (hn : parabolicConvexClosureHorizontalComplex n ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞ parabolicConvexClosureOutwardAngle n :=
  (revolutionComplexAngle_contMDiffAt hn).comp n
    parabolicConvexClosureHorizontalComplex_contDiff.contMDiff.contMDiffAt

theorem parabolicConvexClosure_nativeOutwardNormal_height (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (p : AddCircle (2 * Real.pi) × U) :
    parabolicConvexClosureNativeOutwardNormal r U p 2 = parabolicConvexClosureGaussHeight r p.2 := by
  change -(revolutionEndCircleNormal r (p.1, (p.2 : ℝ)) 2) = _
  rw [revolutionEndCircleNormal_height]
  rfl

/-- Global injectivity is proved from the actual scalar height and positive horizontal coefficient. -/
theorem parabolicConvexClosure_nativeOutwardNormal_injective {h : ℝ} {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0) :
    Function.Injective (parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h)) := by
  intro p s he
  have hheight := congrArg (fun v : Ambient => v 2) he
  rw [parabolicConvexClosure_nativeOutwardNormal_height,
    parabolicConvexClosure_nativeOutwardNormal_height] at hheight
  have hz : (p.2 : ℝ) = (s.2 : ℝ) :=
    (parabolicConvexClosure_gaussHeight_strictMonoOn hr hneg).injOn p.2.property s.2.property hheight
  change -(revolutionEndCircleNormal r (p.1, (p.2 : ℝ))) =
    -(revolutionEndCircleNormal r (s.1, (s.2 : ℝ))) at he
  have hi := neg_injective he
  have hcos := congrArg (fun v : Ambient => v 0) hi
  have hsin := congrArg (fun v : Ambient => v 1) hi
  change (-1 / revolutionWeight (deriv r p.2)) * Real.Angle.cos p.1 +
    revolutionNormalHeight r p.2 * 0 =
    (-1 / revolutionWeight (deriv r s.2)) * Real.Angle.cos s.1 +
      revolutionNormalHeight r s.2 * 0 at hcos
  change (-1 / revolutionWeight (deriv r p.2)) * Real.Angle.sin p.1 +
    revolutionNormalHeight r p.2 * 0 =
    (-1 / revolutionWeight (deriv r s.2)) * Real.Angle.sin s.1 +
      revolutionNormalHeight r s.2 * 0 at hsin
  simp only [mul_zero, add_zero] at hcos hsin
  rw [← hz] at hcos hsin
  have hw : -1 / revolutionWeight (deriv r p.2) ≠ 0 :=
    div_ne_zero (by norm_num) (revolutionWeight_pos _).ne'
  exact Prod.ext (revolutionAngle_cos_sin_injective (mul_left_cancel₀ hw hcos)
    (mul_left_cancel₀ hw hsin)) (Subtype.ext hz)

/-- Sign-free reconstruction of the actual outward normal at its angle and height. -/
theorem parabolicConvexClosure_outwardNormal_angle (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (n : RoundSphere) (z : U)
    (hz : parabolicConvexClosureGaussHeight r z = n.val 2) :
    parabolicConvexClosureNativeOutwardNormal r U (parabolicConvexClosureOutwardAngle n.val, z) = n.val := by
  let v := parabolicConvexClosureHorizontalComplex n.val
  let w := revolutionWeight (deriv r z)
  have hw : 0 < w := revolutionWeight_pos _
  have hsq : ‖v‖^2 = 1 / w^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [v, parabolicConvexClosureHorizontalComplex, ← pow_two]
    change (n.val 0)^2 + (n.val 1)^2 = 1 / w^2
    have hn := revolutionSphere_horizontal_sq n
    have hh : n.val 2 = -(deriv r z / w) := hz.symm
    rw [hh] at hn
    have hws : w^2 = 1 + (deriv r z)^2 := revolutionWeight_sq _
    field_simp [hw.ne'] at hn ⊢
    nlinarith
  have hv : ‖v‖ = 1 / w := by
    have hp : 0 < 1 / w := one_div_pos.mpr hw
    have he : ‖v‖^2 = (1 / w)^2 := by simpa [div_pow] using hsq
    nlinarith [norm_nonneg v]
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; positivity)
  apply PiLp.ext
  intro i
  fin_cases i
  · change -((-1 / w) * Real.Angle.cos (v.arg : Real.Angle) +
      revolutionNormalHeight r z * 0) = n.val 0
    rw [Real.Angle.cos_coe, Complex.cos_arg hv0, hv]
    change -((-1 / w) * (n.val 0 / (1 / w)) + _ * 0) = _
    field_simp [hw.ne']
    <;> ring
  · change -((-1 / w) * Real.Angle.sin (v.arg : Real.Angle) +
      revolutionNormalHeight r z * 0) = n.val 1
    rw [Real.Angle.sin_coe, Complex.sin_arg, hv]
    change -((-1 / w) * (n.val 1 / (1 / w)) + _ * 0) = _
    field_simp [hw.ne']
    <;> ring
  · change parabolicConvexClosureNativeOutwardNormal r U
      (parabolicConvexClosureOutwardAngle n.val, z) 2 = n.val 2
    rw [parabolicConvexClosure_nativeOutwardNormal_height]
    exact hz

section ActualInverse
variable {RN mu h δ : ℝ} (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ)
  {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
  (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0)
  (hlower : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z)) (Icc (-h) (-h + δ)))
  (hupper : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h))

include hmu hh hδ hr hneg hlower hupper

def parabolicConvexClosureInverseHeight (y : ℝ) : parabolicConvexClosureHeightDomain h :=
  ⟨parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper y, by
    classical
    by_cases hy : y ∈ Ioo (-1 : ℝ) 1
    · exact (parabolicConvexClosureGaussHeightInverse_spec hmu hh hδ hr hneg hlower hupper hy).1
    · simp only [parabolicConvexClosureGaussHeightInverse, dif_neg hy]
      exact ⟨by linarith, hh⟩⟩

/-- The explicit inverse is defined on ambient space; it is smooth at actual normals. -/
def parabolicConvexClosureAmbientGaussInverse (n : Ambient) :
    AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h :=
  (parabolicConvexClosureOutwardAngle n,
    parabolicConvexClosureInverseHeight hmu hh hδ hr hneg hlower hupper (n 2))

theorem parabolicConvexClosureAmbientGaussInverse_contMDiffAt {n : Ambient}
    (hn : parabolicConvexClosureHorizontalComplex n ≠ 0) (hy : n 2 ∈ Ioo (-1 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, Ambient) nativeProductModel ∞
      (parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper) n := by
  have hs : ContMDiffAt 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun a : Ambient => parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper (a 2)) n :=
    ((parabolicConvexClosureGaussHeightInverse_contDiffOn hmu hh hδ hr hneg hlower hupper).contDiffAt
      (isOpen_Ioo.mem_nhds hy)).contMDiffAt.comp n
        (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.contMDiff.contMDiffAt
  have ht : ContMDiffAt 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun a : Ambient => parabolicConvexClosureInverseHeight hmu hh hδ hr hneg hlower hupper (a 2)) n :=
    (ContMDiffAt.subtypeVal_comp_iff (parabolicConvexClosureHeightDomain h) _ n).mp hs
  exact (parabolicConvexClosureOutwardAngle_contMDiffAt hn).prodMk ht

theorem parabolicConvexClosureAmbientGaussInverse_right (n : RoundSphere)
    (hn : n.val 2 ∈ Ioo (-1 : ℝ) 1) :
    parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h)
      (parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper n.val) = n.val := by
  apply parabolicConvexClosure_outwardNormal_angle
  exact (parabolicConvexClosureGaussHeightInverse_spec hmu hh hδ hr hneg hlower hupper hn).2

theorem parabolicConvexClosureAmbientGaussInverse_left
    (p : AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h) :
    parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper
      (parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h) p) = p := by
  apply parabolicConvexClosure_nativeOutwardNormal_injective hr hneg
  exact parabolicConvexClosureAmbientGaussInverse_right hmu hh hδ hr hneg hlower hupper
    (parabolicConvexClosureNativeOutwardGauss r (parabolicConvexClosureHeightDomain h) p)
    (by
      change parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h) p 2 ∈ Ioo (-1 : ℝ) 1
      rw [parabolicConvexClosure_nativeOutwardNormal_height]
      exact parabolicConvexClosure_gaussHeight_mem r p.2)

/-- Actual native normal differential regularity follows from the smooth explicit left inverse. -/
theorem parabolicConvexClosure_nativeOutwardNormal_mfderiv_injective
    (p : AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h)) p) := by
  let N := parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h)
  let G := parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper
  have hy : N p 2 ∈ Ioo (-1 : ℝ) 1 := by
    rw [parabolicConvexClosure_nativeOutwardNormal_height]
    exact parabolicConvexClosure_gaussHeight_mem r p.2
  have hn : parabolicConvexClosureHorizontalComplex (N p) ≠ 0 :=
    parabolicConvexClosure_horizontal_ne_zero
      (parabolicConvexClosureNativeOutwardGauss r (parabolicConvexClosureHeightDomain h) p) hy
  have hdG := (parabolicConvexClosureAmbientGaussInverse_contMDiffAt hmu hh hδ hr hneg hlower hupper hn hy).mdifferentiableAt (by simp)
  have hdN := (parabolicConvexClosure_nativeOutwardNormal_contMDiff (parabolicConvexClosureHeightDomain h) hr p).mdifferentiableAt (by simp)
  have hc := mfderiv_comp p hdG hdN
  change mfderiv nativeProductModel nativeProductModel (G ∘ N) p = _ at hc
  have hleft : G ∘ N = id := funext
    (parabolicConvexClosureAmbientGaussInverse_left hmu hh hδ hr hneg hlower hupper)
  rw [hleft, mfderiv_id] at hc
  intro v w he
  have he' := congrArg (fun a => mfderiv 𝓘(ℝ, Ambient) nativeProductModel G (N p) a) he
  change ((mfderiv 𝓘(ℝ, Ambient) nativeProductModel G (N p)).comp
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) N p)) v =
    ((mfderiv 𝓘(ℝ, Ambient) nativeProductModel G (N p)).comp
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) N p)) w at he'
  rw [← hc] at he'
  exact he'

/-- Actual whole Gauss range; its two excluded pole heights are derived. -/
theorem parabolicConvexClosure_nativeOutwardGauss_range :
    range (parabolicConvexClosureNativeOutwardGauss r (parabolicConvexClosureHeightDomain h)) =
      (parabolicConvexClosureSphereBelt : Set RoundSphere) := by
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    change parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h) p 2 ∈ Ioo (-1 : ℝ) 1
    rw [parabolicConvexClosure_nativeOutwardNormal_height]
    exact parabolicConvexClosure_gaussHeight_mem r p.2
  · intro hn
    refine ⟨parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper n.val, ?_⟩
    exact Subtype.ext (parabolicConvexClosureAmbientGaussInverse_right hmu hh hδ hr hneg hlower hupper n hn)

theorem parabolicConvexClosure_sphereGaussInverse_contMDiffOn :
    ContMDiffOn (𝓡 2) nativeProductModel ∞
      (fun n : RoundSphere => parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper n.val)
      parabolicConvexClosureSphereBelt := by
  intro n hn
  exact ((parabolicConvexClosureAmbientGaussInverse_contMDiffAt hmu hh hδ hr hneg hlower hupper
    (parabolicConvexClosure_horizontal_ne_zero n hn) hn).comp n (contMDiff_coe_sphere n)).contMDiffWithinAt

/-- The actual outward Gauss diffeomorphism onto the open twice-punctured sphere belt. -/
def parabolicConvexClosureNativeGaussDiffeomorph :
    Diffeomorph nativeProductModel (𝓡 2)
      (AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h)
      parabolicConvexClosureSphereBelt ∞ where
  toFun p := ⟨parabolicConvexClosureNativeOutwardGauss r (parabolicConvexClosureHeightDomain h) p, by
    change parabolicConvexClosureNativeOutwardNormal r (parabolicConvexClosureHeightDomain h) p 2 ∈ Ioo (-1 : ℝ) 1
    rw [parabolicConvexClosure_nativeOutwardNormal_height]
    exact parabolicConvexClosure_gaussHeight_mem r p.2⟩
  invFun n := parabolicConvexClosureAmbientGaussInverse hmu hh hδ hr hneg hlower hupper n.val.val
  left_inv := parabolicConvexClosureAmbientGaussInverse_left hmu hh hδ hr hneg hlower hupper
  right_inv n := Subtype.ext (Subtype.ext
    (parabolicConvexClosureAmbientGaussInverse_right hmu hh hδ hr hneg hlower hupper n.val n.property))
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff parabolicConvexClosureSphereBelt _).mp
    (parabolicConvexClosure_nativeOutwardGauss_contMDiff (parabolicConvexClosureHeightDomain h) hr)
  contMDiff_invFun := by
    intro n
    exact contMDiffAt_subtype_iff.mpr
      ((parabolicConvexClosure_sphereGaussInverse_contMDiffOn hmu hh hδ hr hneg hlower hupper).contMDiffAt
        (parabolicConvexClosureSphereBelt.isOpen.mem_nhds n.property))

end ActualInverse
end
end TightVer401
