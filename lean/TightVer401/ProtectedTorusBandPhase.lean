import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.PeriodCircleInstances

/-! The literal saddle phase chart connects completed cylinder coordinates to
 the already constructed native torus source. It uses the retained quotient
 atlas and supplies no completed-cylinder existence premise. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The retained centered phase chart restricted to the open saddle phase. -/
def protectedTorusPhaseChart :
    OpenPartialHomeomorph (AddCircle (2 * Real.pi) × ℝ) NonrigidTorusSource :=
  ((OpenPartialHomeomorph.refl (AddCircle (2 * Real.pi))).prod
    (periodChart (2 * Real.pi))).restr
      ((univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi)

theorem protectedTorusPhaseChart_source :
    protectedTorusPhaseChart.source =
      (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi := by
  change ((OpenPartialHomeomorph.refl (AddCircle (2 * Real.pi))).prod
    (periodChart (2 * Real.pi))).source ∩
      interior ((univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi) =
    (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi
  have hO : IsOpen ((univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi) :=
    isOpen_univ.prod isOpen_Ioo
  rw [hO.interior_eq]
  ext p
  constructor
  · exact fun hp => hp.2
  · intro hp
    refine ⟨?_, hp⟩
    change p.1 ∈ (univ : Set (AddCircle (2 * Real.pi))) ∧
      p.2 ∈ Ioo (-(2 * Real.pi) / 2) (-(2 * Real.pi) / 2 + 2 * Real.pi)
    exact ⟨mem_univ _, ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2]⟩⟩

theorem protectedTorusPhaseChart_apply (p : AddCircle (2 * Real.pi) × ℝ) :
    protectedTorusPhaseChart p = (p.1, periodProjection (2 * Real.pi) p.2) := rfl

/-- The inverse phase coordinate is the actual retained circle chart at zero. -/
private theorem protectedTorusPhaseChart_circle_inverse_smooth :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (periodChart (2 * Real.pi)).symm
      (periodChart (2 * Real.pi)).target := by
  have hchart : chartAt ℝ (0 : AddCircle (2 * Real.pi)) =
      OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) 0 := rfl
  have hc := contMDiffOn_extChartAt (I := 𝓘(ℝ, ℝ)) (n := ∞)
    (x := (0 : AddCircle (2 * Real.pi)))
  convert! hc using 1
  · funext q
    change (periodChart (2 * Real.pi)).symm q =
      (periodChart (2 * Real.pi)).symm (-0 + q)
    simp only [neg_zero, zero_add]
  · rw [hchart, OAI.RawQuotientLie.addLeftChart_source]
    ext q
    simp only [mem_preimage, neg_zero, zero_add]

theorem protectedTorusPhaseChart_inverse_smooth :
    ContMDiffOn nativeProductModel nativeProductModel ∞
      protectedTorusPhaseChart.symm protectedTorusPhaseChart.target := by
  have hid : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) univ :=
    contMDiff_id.contMDiffOn
  have hc := hid.prodMap protectedTorusPhaseChart_circle_inverse_smooth
  change ContMDiffOn nativeProductModel nativeProductModel ∞
    (Prod.map id (periodChart (2 * Real.pi)).symm) protectedTorusPhaseChart.target
  apply hc.mono
  intro p hp
  exact hp.1

/-- The quotient map is smooth in the same native product model. -/
theorem protectedTorusPhaseChart_forward_smooth :
    ContMDiff nativeProductModel nativeProductModel ∞ protectedTorusPhaseChart := by
  change ContMDiff nativeProductModel nativeProductModel ∞
    (Prod.map id (periodProjection (2 * Real.pi)))
  exact contMDiff_id.prodMap (periodProjection_contMDiff (2 * Real.pi))

/-- The literal torus map is exactly the supplied saddle on the chart source. -/
theorem protectedTorusPhaseChart_map_source
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ protectedTorusPhaseChart.source) :
    protectedTorusMap S r h (protectedTorusPhaseChart p) = S p := by
  rw [protectedTorusPhaseChart_source] at hp
  have hu : p.2 ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨hp.2.1.le, by linarith [hp.2.2, Real.pi_pos]⟩
  have hrep : AddCircle.equivIco (2 * Real.pi) 0
      (periodProjection (2 * Real.pi) p.2) = ⟨p.2, hu⟩ :=
    AddCircle.equivIco_coe_eq hu
  rw [protectedTorusPhaseChart_apply]
  simp only [protectedTorusMap, hrep, if_pos hp.2.2.le]

/-- The exact saddle equality on the actual open torus chart target. -/
theorem protectedTorusPhaseChart_map_target
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    {p : NonrigidTorusSource} (hp : p ∈ protectedTorusPhaseChart.target) :
    protectedTorusMap S r h p = S (protectedTorusPhaseChart.symm p) := by
  have hm := protectedTorusPhaseChart_map_source S r h
    (protectedTorusPhaseChart.map_target hp)
  rwa [protectedTorusPhaseChart.right_inv hp] at hm

/-- Exact connection interface for composing a protected cylinder coordinate
map with this literal torus phase chart. -/
theorem protectedTorusPhaseChart_properties :
    protectedTorusPhaseChart.source =
      (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi ∧
    (∀ p, protectedTorusPhaseChart p = (p.1, periodProjection (2 * Real.pi) p.2)) ∧
    ContMDiffOn nativeProductModel nativeProductModel ∞
      protectedTorusPhaseChart.symm protectedTorusPhaseChart.target ∧
    (∀ (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
      (p : NonrigidTorusSource), p ∈ protectedTorusPhaseChart.target →
      protectedTorusMap S r h p = S (protectedTorusPhaseChart.symm p)) :=
  ⟨protectedTorusPhaseChart_source, protectedTorusPhaseChart_apply,
    protectedTorusPhaseChart_inverse_smooth, fun S r h _ hp =>
      protectedTorusPhaseChart_map_target S r h hp⟩

end
end TightVer401
