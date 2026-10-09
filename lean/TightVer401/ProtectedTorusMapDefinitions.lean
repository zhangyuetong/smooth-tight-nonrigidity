import TightVer401.TorusSourceGeometry
import TightVer401.NativeProductPlaneAtlas
import TightVer401.RevolutionEndCircleSmooth
import TightVer401.CorrugatedSeedFrameHorizontal

/-! Actual torus map definitions and ordinary producer interfaces.
This definitions-only module contains no pending proofs, so producers can import
it without depending on the root assembly gates in ProtectedTorusMap. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The signed transverse normalization of the two parabolic collars. -/
def protectedTorusCollarScale (h μ : ℝ) : ℝ := 2 * Real.sqrt (h / μ)

def protectedTorusNorthCollar (RN μ h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  (RN + μ * p.2) • revolutionCircleRadial p.1 +
    (h - μ * p.2 ^ 2 / 2) • revolutionAxis

def protectedTorusSouthCollar (RN μ h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  (RN + μ * p.2) • revolutionCircleRadial p.1 +
    (-h + μ * p.2 ^ 2 / 2) • revolutionAxis

/-- The convex cylinder uses height -h cos(phi); signed collar coordinates
keep the actual differential regular at its boundary circles. -/
def protectedTorusConvexCylinder (r : ℝ → ℝ) (h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  revolutionEndCircleFull r (p.1, -h * Real.cos p.2)

/-- Literal map on the already constructed quotient-circle product source. -/
def protectedTorusMap (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (r : ℝ → ℝ) (h : ℝ) (p : NonrigidTorusSource) : Ambient :=
  let φ : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  if φ ≤ Real.pi then S (p.1, φ)
  else protectedTorusConvexCylinder r h (p.1, φ)

/-- Ordinary producer data about an actual saddle cylinder and meridian.
No torus, torus smoothness or torus embedding conclusion is supplied here.
The saddle and convex owners must construct these data with the same RN,mu,h. -/
structure ProtectedSaddleCylinderInput (RN μ h : ℝ) where
  radius_pos : 0 < RN
  coefficient_pos : 0 < μ
  height_pos : 0 < h
  saddle : AddCircle (2 * Real.pi) × ℝ → Ambient
  saddle_continuous : ContinuousOn saddle (univ ×ˢ Icc (0 : ℝ) Real.pi)
  saddle_smooth : ContMDiffOn nativeProductModel 𝓘(ℝ, Ambient) ∞ saddle
    (univ ×ˢ Ioo (0 : ℝ) Real.pi)
  saddle_immersion : ∀ p ∈ (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi,
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) saddle p)
  saddle_injective : InjOn saddle (univ ×ˢ Icc (0 : ℝ) Real.pi)
  saddle_radius : ∀ p ∈ (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi,
    ‖corrugatedAmbientHorizontalCLM (saddle p)‖ < RN
  south_germ : ∃ ε > 0, ε < Real.pi / 2 ∧
    ∀ q : AddCircle (2 * Real.pi), ∀ u ∈ Icc (0 : ℝ) ε,
      saddle (q, u) = protectedTorusSouthCollar RN μ h
        (q, -protectedTorusCollarScale h μ * Real.sin (u / 2))
  north_germ : ∃ ε > 0, ε < Real.pi / 2 ∧
    ∀ q : AddCircle (2 * Real.pi), ∀ u ∈ Icc (Real.pi - ε) Real.pi,
      saddle (q, u) = protectedTorusNorthCollar RN μ h
        (q, -protectedTorusCollarScale h μ * Real.cos (u / 2))

/-- Ordinary actual convex-meridian data; no torus conclusion. -/
structure ProtectedParabolicMeridianInput (RN μ h : ℝ) where
  meridian : ℝ → ℝ
  meridian_continuous : ContinuousOn meridian (Icc (-h) h)
  meridian_smooth : ContDiffOn ℝ ∞ meridian (Ioo (-h) h)
  meridian_exterior : ∀ z ∈ Ioo (-h) h, RN < meridian z
  meridian_north_germ : ∃ ε > 0, ∀ z ∈ Icc (h - ε) h,
    meridian z = RN + Real.sqrt (2 * μ * (h - z))
  meridian_south_germ : ∃ ε > 0, ∀ z ∈ Icc (-h) (-h + ε),
    meridian z = RN + Real.sqrt (2 * μ * (h + z))

/-- The two producer inputs share the exact geometric constants. -/
structure ProtectedTorusAssemblyInput (RN μ h : ℝ)
    extends ProtectedSaddleCylinderInput RN μ h,
      ProtectedParabolicMeridianInput RN μ h

end
end TightVer401
