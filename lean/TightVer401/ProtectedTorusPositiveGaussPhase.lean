import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.ParabolicConvexClosureGaussSmoothNative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! The actual open convex phase and its quotient chart.
This uses the literal phase interval (pi,2pi) and the registered quotient,
not a supplied placement or a different convex meridian. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussPhasePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def protectedTorusPositiveGaussPhaseSet : Set (AddCircle (2 * Real.pi)) :=
  periodProjection (2 * Real.pi) '' Ioo Real.pi (2 * Real.pi)

theorem protectedTorusPositiveGaussPhaseSet_iff (q : AddCircle (2 * Real.pi)) :
    q ∈ protectedTorusPositiveGaussPhaseSet ↔
      (AddCircle.equivIco (2 * Real.pi) 0 q).val ∈ Ioo Real.pi (2 * Real.pi) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have he := AddCircle.equivIco_coe_eq
      (show u ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) from
        ⟨by linarith [hu.1, Real.pi_pos], by simpa using hu.2⟩)
    have hev : (AddCircle.equivIco (2 * Real.pi) 0
        (periodProjection (2 * Real.pi) u)).val = u := congrArg Subtype.val he
    rw [hev]
    exact hu
  · intro hq
    exact ⟨_, hq, AddCircle.coe_equivIco⟩

theorem protectedTorusPositiveGaussPhaseSet_isOpen :
    IsOpen protectedTorusPositiveGaussPhaseSet :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

def protectedTorusPositiveGaussRegion : TopologicalSpace.Opens NonrigidTorusSource :=
  ⟨univ ×ˢ protectedTorusPositiveGaussPhaseSet,
    isOpen_univ.prod protectedTorusPositiveGaussPhaseSet_isOpen⟩

theorem protectedTorusPositiveGaussRegion_iff (p : NonrigidTorusSource) :
    p ∈ protectedTorusPositiveGaussRegion ↔
      (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi) := by
  change p.1 ∈ (univ : Set (AddCircle (2 * Real.pi))) ∧
    p.2 ∈ protectedTorusPositiveGaussPhaseSet ↔ _
  simp only [mem_univ, true_and, protectedTorusPositiveGaussPhaseSet_iff]

def protectedTorusPositiveGaussPhaseDomain : TopologicalSpace.Opens ℝ :=
  ⟨Ioo Real.pi (2 * Real.pi), isOpen_Ioo⟩

/-- A genuine restricted quotient partial homeomorphism, with explicit source. -/
def protectedTorusPositiveGaussPhaseChart :
    OpenPartialHomeomorph ℝ (AddCircle (2 * Real.pi)) :=
  (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) Real.pi).restrOpen
    (Ioo Real.pi (2 * Real.pi)) isOpen_Ioo

theorem protectedTorusPositiveGaussPhaseChart_source :
    protectedTorusPositiveGaussPhaseChart.source = Ioo Real.pi (2 * Real.pi) := by
  change Ioo Real.pi (Real.pi + 2 * Real.pi) ∩ Ioo Real.pi (2 * Real.pi) = _
  ext u
  constructor
  · exact fun hu => hu.2
  · intro hu
    exact ⟨⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩, hu⟩

theorem protectedTorusPositiveGaussPhaseChart_apply (u : ℝ) :
    protectedTorusPositiveGaussPhaseChart u = periodProjection (2 * Real.pi) u := rfl

theorem protectedTorusPositiveGaussPhaseChart_target :
    protectedTorusPositiveGaussPhaseChart.target = protectedTorusPositiveGaussPhaseSet := by
  rw [← protectedTorusPositiveGaussPhaseChart.image_source_eq_target,
    protectedTorusPositiveGaussPhaseChart_source]
  rfl

/-- Actual inverse quotient coordinates are smooth in the registered atlas. -/
theorem protectedTorusPositiveGaussPhaseChart_inverse_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      protectedTorusPositiveGaussPhaseChart.symm protectedTorusPositiveGaussPhaseSet := by
  intro q hq
  obtain ⟨φ, hφ, rfl⟩ := hq
  let q := periodProjection (2 * Real.pi) φ
  let σ : AddCircle (2 * Real.pi) → ℝ := fun y => φ + extChartAt 𝓘(ℝ, ℝ) q y
  have hz : extChartAt 𝓘(ℝ, ℝ) q q = (0 : ℝ) := by
    change (periodChart (2 * Real.pi)).symm (-q + q) = 0
    rw [neg_add_cancel]
    have h0 : periodChart (2 * Real.pi) (0 : ℝ) = 0 := rfl
    rw [← h0, (periodChart (2 * Real.pi)).left_inv (periodChart_zero_source _)]
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ q :=
    contMDiffAt_const.add (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ)))
  have hσ : σ q = φ := by simp only [σ, hz, add_zero]
  have ht : ∀ᶠ y in 𝓝 q, σ y ∈ Ioo Real.pi (2 * Real.pi) := by
    apply hs.continuousAt.eventually
    rw [hσ]
    exact isOpen_Ioo.mem_nhds hφ
  have he : protectedTorusPositiveGaussPhaseChart.symm =ᶠ[𝓝 q] σ := by
    filter_upwards [ht, (chartAt ℝ q).open_source.mem_nhds (mem_chart_source ℝ q)] with y hy hc
    have hquot : periodProjection (2 * Real.pi) (σ y) = y := by
      change periodProjection (2 * Real.pi)
        (φ + (periodChart (2 * Real.pi)).symm (-q + y)) = y
      rw [map_add]
      change q + (periodChart (2 * Real.pi))
        ((periodChart (2 * Real.pi)).symm (-q + y)) = y
      have hc' : y ∈ (OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) q).source := hc
      rw [OAI.RawQuotientLie.addLeftChart_source] at hc'
      rw [(periodChart (2 * Real.pi)).right_inv hc']
      rw [← add_assoc, add_neg_cancel, zero_add]
    calc
      protectedTorusPositiveGaussPhaseChart.symm y =
          protectedTorusPositiveGaussPhaseChart.symm
            (protectedTorusPositiveGaussPhaseChart (σ y)) :=
        congrArg protectedTorusPositiveGaussPhaseChart.symm hquot.symm
      _ = σ y := protectedTorusPositiveGaussPhaseChart.left_inv
        (by rw [protectedTorusPositiveGaussPhaseChart_source]; exact hy)
  exact (hs.congr_of_eventuallyEq he).contMDiffWithinAt

end
end TightVer401
