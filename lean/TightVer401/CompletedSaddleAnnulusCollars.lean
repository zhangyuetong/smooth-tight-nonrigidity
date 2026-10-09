import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.CompletedSaddleAnnulusNormalization

/-! Actual smooth native south and north collars with the same normalized
height, using the committed root's literal signed collar definitions. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def completedSaddleAnnulusSouthCollar (RN μ h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  protectedTorusSouthCollar RN μ h
    (p.1, completedSaddleAnnulusSouthTransverse h μ p.2)

def completedSaddleAnnulusNorthCollar (RN μ h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  protectedTorusNorthCollar RN μ h
    (p.1, completedSaddleAnnulusNorthTransverse h μ p.2)

/-- Smoothness of the actual committed south base collar, without any
incoming collar smoothness package. -/
theorem completedSaddleAnnulusSouthCollar_base_contMDiff (RN μ h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (protectedTorusSouthCollar RN μ h) := by
  have ht : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => p.2) := contMDiff_snd
  have hr : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => RN + μ * p.2) :=
    contMDiff_const.add (contMDiff_const.mul ht)
  have hz : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => -h + μ * p.2 ^ 2 / 2) :=
    contMDiff_const.add ((contMDiff_const.mul (ht.pow 2)).div_const 2)
  exact (hr.smul (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
    (hz.smul contMDiff_const)

theorem completedSaddleAnnulusNorthCollar_base_contMDiff (RN μ h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (protectedTorusNorthCollar RN μ h) := by
  have ht : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => p.2) := contMDiff_snd
  have hr : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => RN + μ * p.2) :=
    contMDiff_const.add (contMDiff_const.mul ht)
  have hz : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => h - μ * p.2 ^ 2 / 2) :=
    contMDiff_const.sub ((contMDiff_const.mul (ht.pow 2)).div_const 2)
  exact (hr.smul (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
    (hz.smul contMDiff_const)

/-- Native smoothness of the actual normalized south collar on its full
quotient-circle product source. -/
theorem completedSaddleAnnulusSouthCollar_contMDiff (RN μ h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (completedSaddleAnnulusSouthCollar RN μ h) :=
  (completedSaddleAnnulusSouthCollar_base_contMDiff RN μ h).comp
    (contMDiff_fst.prodMk
      ((completedSaddleAnnulusSouthTransverse_contDiff h μ).contMDiff.comp contMDiff_snd))

theorem completedSaddleAnnulusNorthCollar_contMDiff (RN μ h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (completedSaddleAnnulusNorthCollar RN μ h) :=
  (completedSaddleAnnulusNorthCollar_base_contMDiff RN μ h).comp
    (contMDiff_fst.prodMk
      ((completedSaddleAnnulusNorthTransverse_contDiff h μ).contMDiff.comp contMDiff_snd))

/-- Exact agreement with the root's literal signed south collar formula. -/
theorem completedSaddleAnnulusSouthCollar_signed_formula (RN μ h : ℝ)
    (q : AddCircle (2 * Real.pi)) (u : ℝ) :
    completedSaddleAnnulusSouthCollar RN μ h (q, u) =
      protectedTorusSouthCollar RN μ h
        (q, -protectedTorusCollarScale h μ * Real.sin (u / 2)) := by
  have ht : completedSaddleAnnulusSouthTransverse h μ u =
      -protectedTorusCollarScale h μ * Real.sin (u / 2) := by
    unfold completedSaddleAnnulusSouthTransverse protectedTorusCollarScale
    ring
  change protectedTorusSouthCollar RN μ h (q, completedSaddleAnnulusSouthTransverse h μ u) = _
  rw [ht]

theorem completedSaddleAnnulusNorthCollar_signed_formula (RN μ h : ℝ)
    (q : AddCircle (2 * Real.pi)) (u : ℝ) :
    completedSaddleAnnulusNorthCollar RN μ h (q, u) =
      protectedTorusNorthCollar RN μ h
        (q, -protectedTorusCollarScale h μ * Real.cos (u / 2)) := by
  have ht : completedSaddleAnnulusNorthTransverse h μ u =
      -protectedTorusCollarScale h μ * Real.cos (u / 2) := by
    unfold completedSaddleAnnulusNorthTransverse protectedTorusCollarScale
    ring
  change protectedTorusNorthCollar RN μ h (q, completedSaddleAnnulusNorthTransverse h μ u) = _
  rw [ht]

theorem completedSaddleAnnulusSouthCollar_boundary (RN μ h : ℝ)
    (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusSouthCollar RN μ h (q, 0) =
      RN • revolutionCircleRadial q + (-h) • revolutionAxis := by
  simp [completedSaddleAnnulusSouthCollar, protectedTorusSouthCollar]

theorem completedSaddleAnnulusNorthCollar_boundary (RN μ h : ℝ)
    (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusNorthCollar RN μ h (q, Real.pi) =
      RN • revolutionCircleRadial q + h • revolutionAxis := by
  simp [completedSaddleAnnulusNorthCollar, protectedTorusNorthCollar]

/-- The actual south collar has the common normalized height as a literal
ambient vector formula, derived from the actual scalar normalization. -/
theorem completedSaddleAnnulusSouthCollar_normalized_formula
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (p : AddCircle (2 * Real.pi) × ℝ) :
    completedSaddleAnnulusSouthCollar RN μ h p =
      (RN + μ * completedSaddleAnnulusSouthTransverse h μ p.2) • revolutionCircleRadial p.1 +
        (-h * Real.cos p.2) • revolutionAxis := by
  change (RN + μ * completedSaddleAnnulusSouthTransverse h μ p.2) • revolutionCircleRadial p.1 +
    (-h + μ * (completedSaddleAnnulusSouthTransverse h μ p.2) ^ 2 / 2) • revolutionAxis = _
  rw [completedSaddleAnnulusSouthTransverse_height hh hμ]

theorem completedSaddleAnnulusNorthCollar_normalized_formula
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (p : AddCircle (2 * Real.pi) × ℝ) :
    completedSaddleAnnulusNorthCollar RN μ h p =
      (RN + μ * completedSaddleAnnulusNorthTransverse h μ p.2) • revolutionCircleRadial p.1 +
        (-h * Real.cos p.2) • revolutionAxis := by
  change (RN + μ * completedSaddleAnnulusNorthTransverse h μ p.2) • revolutionCircleRadial p.1 +
    (h - μ * (completedSaddleAnnulusNorthTransverse h μ p.2) ^ 2 / 2) • revolutionAxis = _
  rw [completedSaddleAnnulusNorthTransverse_height hh hμ]

/-- Evaluate the actual ambient height coordinate of the south collar. -/
theorem completedSaddleAnnulusSouthCollar_height
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (p : AddCircle (2 * Real.pi) × ℝ) :
    completedSaddleAnnulusSouthCollar RN μ h p 2 = -h * Real.cos p.2 := by
  rw [completedSaddleAnnulusSouthCollar_normalized_formula RN hh hμ]
  simp [revolutionCircleRadial, revolutionAxis]

theorem completedSaddleAnnulusNorthCollar_height
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (p : AddCircle (2 * Real.pi) × ℝ) :
    completedSaddleAnnulusNorthCollar RN μ h p 2 = -h * Real.cos p.2 := by
  rw [completedSaddleAnnulusNorthCollar_normalized_formula RN hh hμ]
  simp [revolutionCircleRadial, revolutionAxis]

end
end TightVer401
