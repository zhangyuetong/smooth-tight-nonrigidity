import TightVer401.ParabolicConvexClosureBodyFrontier
import TightVer401.ParabolicConvexClosureGeometryNative

/-! The actual closed lateral annulus and its image in Ambient. Continuity uses
only the restriction of the radius to its closed interval. Positive radius
proves injectivity; compactness of circle times interval gives a genuine closed
embedding. Endpoint smoothness remains the separate parabolic-collar task. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology Pointwise
set_option backward.isDefEq.respectTransparency false

local instance bodyAnnulusCirclePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev ParabolicConvexClosureClosedAnnulus (h : ℝ) :=
  AddCircle (2 * Real.pi) × Icc (-h) h

/-- The actual closed annulus map, including both endpoint circles. -/
def parabolicConvexClosureClosedMap (r : ℝ → ℝ) (h : ℝ)
    (p : ParabolicConvexClosureClosedAnnulus h) : Ambient :=
  revolutionEndCircleFull r (p.1, (p.2 : ℝ))

/-- Actual closed lateral points, using the Euclidean horizontal radius. -/
def parabolicConvexClosureClosedLateralCarrier (r : ℝ → ℝ) (h : ℝ) : Set Ambient :=
  {p | p 2 ∈ Icc (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2)}

/-- Endpoint radius circle, as an actual subset of its Ambient height plane. -/
def parabolicConvexClosureEndpointCircle (RN z : ℝ) : Set Ambient :=
  {p | p 2 = z ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = RN}

@[simp] theorem parabolicConvexClosureClosedMap_zero (r : ℝ → ℝ) (h : ℝ)
    (p : ParabolicConvexClosureClosedAnnulus h) :
    parabolicConvexClosureClosedMap r h p 0 = r p.2.val * Real.Angle.cos p.1 := by
  simp [parabolicConvexClosureClosedMap, revolutionEndCircleFull, revolutionCircleRadial, revolutionAxis]

@[simp] theorem parabolicConvexClosureClosedMap_one (r : ℝ → ℝ) (h : ℝ)
    (p : ParabolicConvexClosureClosedAnnulus h) :
    parabolicConvexClosureClosedMap r h p 1 = r p.2.val * Real.Angle.sin p.1 := by
  simp [parabolicConvexClosureClosedMap, revolutionEndCircleFull, revolutionCircleRadial, revolutionAxis]

@[simp] theorem parabolicConvexClosureClosedMap_height (r : ℝ → ℝ) (h : ℝ)
    (p : ParabolicConvexClosureClosedAnnulus h) :
    parabolicConvexClosureClosedMap r h p 2 = p.2.val := by
  simp [parabolicConvexClosureClosedMap, revolutionEndCircleFull, revolutionCircleRadial, revolutionAxis]

/-- Closed continuity follows from actual closed-interval profile continuity. -/
theorem parabolicConvexClosureClosedMap_continuous {r : ℝ → ℝ} {h : ℝ}
    (hr : ContinuousOn r (Icc (-h) h)) : Continuous (parabolicConvexClosureClosedMap r h) := by
  have hrest : Continuous (fun z : Icc (-h) h => r z.val) := hr.domRestrict
  have hrad := hrest.comp (continuous_snd : Continuous (fun p : ParabolicConvexClosureClosedAnnulus h => p.2))
  exact (hrad.smul (revolutionCircleRadial_contMDiff.continuous.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_snd).smul continuous_const)

/-- Height and the retained circle angle injection prove actual map injectivity. -/
theorem parabolicConvexClosureClosedMap_injective {r : ℝ → ℝ} {h : ℝ}
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) : Function.Injective (parabolicConvexClosureClosedMap r h) := by
  intro p q he
  have hz : p.2.val = q.2.val := by
    simpa only [parabolicConvexClosureClosedMap_height] using congrArg (fun v : Ambient => v 2) he
  have hrne : r p.2.val ≠ 0 := (hrpos _ p.2.property).ne'
  have hc := congrArg (fun v : Ambient => v 0) he
  have hs := congrArg (fun v : Ambient => v 1) he
  simp only [parabolicConvexClosureClosedMap_zero, parabolicConvexClosureClosedMap_one] at hc hs
  rw [← hz] at hc hs
  exact Prod.ext
    (revolutionAngle_cos_sin_injective ((mul_left_cancel₀ hrne) hc) ((mul_left_cancel₀ hrne) hs))
    (Subtype.ext hz)

/-- Genuine closed embedding, obtained from actual continuity/injectivity and compact domain. -/
theorem parabolicConvexClosureClosedMap_isClosedEmbedding {r : ℝ → ℝ} {h : ℝ}
    (hr : ContinuousOn r (Icc (-h) h)) (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    Topology.IsClosedEmbedding (parabolicConvexClosureClosedMap r h) := by
  exact (parabolicConvexClosureClosedMap_continuous hr).isClosedEmbedding
    (parabolicConvexClosureClosedMap_injective hrpos)

 theorem parabolicConvexClosureClosedMap_horizontal_norm {r : ℝ → ℝ} {h : ℝ}
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) (p : ParabolicConvexClosureClosedAnnulus h) :
    ‖parabolicConvexClosureHorizontalCLM (parabolicConvexClosureClosedMap r h p)‖ = r p.2.val := by
  have htrig : (Real.Angle.cos p.1)^2 + (Real.Angle.sin p.1)^2 = 1 := by
    induction p.1 using Real.Angle.induction_on with
    | h θ => simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using Real.cos_sq_add_sin_sq θ
  have hsq : ‖parabolicConvexClosureHorizontalCLM (parabolicConvexClosureClosedMap r h p)‖^2 = (r p.2.val)^2 := by
    rw [parabolicConvexClosureHorizontal_norm_sq,
      parabolicConvexClosureClosedMap_zero, parabolicConvexClosureClosedMap_one]
    nlinarith [congrArg (fun s : ℝ => (r p.2.val)^2 * s) htrig]
  exact (sq_eq_sq₀ (norm_nonneg _) (hrpos _ p.2.property).le).mp hsq

/-- Every actual closed lateral point has a circle argument representative. -/
theorem parabolicConvexClosureClosedMap_range {r : ℝ → ℝ} {h : ℝ}
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    range (parabolicConvexClosureClosedMap r h) = parabolicConvexClosureClosedLateralCarrier r h := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change (parabolicConvexClosureClosedMap r h q) 2 ∈ Icc (-h) h ∧ _
    rw [parabolicConvexClosureClosedMap_height]
    exact ⟨q.2.property, parabolicConvexClosureClosedMap_horizontal_norm hrpos q⟩
  · rintro ⟨hz, hnorm⟩
    let v := parabolicConvexClosureHorizontalCLM p
    have hvnorm : ‖v‖ = r (p 2) := hnorm
    have hrp : 0 < r (p 2) := hrpos _ hz
    have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hvnorm]; exact hrp)
    let q : ParabolicConvexClosureClosedAnnulus h := ((v.arg : Real.Angle), ⟨p 2, hz⟩)
    refine ⟨q, ?_⟩
    ext i
    fin_cases i
    · change parabolicConvexClosureClosedMap r h q 0 = p 0
      rw [parabolicConvexClosureClosedMap_zero]
      change r (p 2) * Real.Angle.cos (v.arg : Real.Angle) = p 0
      rw [Real.Angle.cos_coe, Complex.cos_arg hv0, hvnorm]
      have hvre : v.re = p 0 := by
        change (parabolicConvexClosureHorizontalCLM p).re = p 0
        rw [parabolicConvexClosureHorizontalCLM_apply]
      rw [hvre]
      field_simp [hrp.ne']
    · change parabolicConvexClosureClosedMap r h q 1 = p 1
      rw [parabolicConvexClosureClosedMap_one]
      change r (p 2) * Real.Angle.sin (v.arg : Real.Angle) = p 1
      rw [Real.Angle.sin_coe, Complex.sin_arg, hvnorm]
      have hvim : v.im = p 1 := by
        change (parabolicConvexClosureHorizontalCLM p).im = p 1
        rw [parabolicConvexClosureHorizontalCLM_apply]
      rw [hvim]
      field_simp [hrp.ne']
    · simp [q]

/-- The actual closed image consists exactly of its two endpoint circles and open lateral points. -/
theorem parabolicConvexClosureClosedMap_range_decomposition {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hl : r (-h) = RN) (hu : r h = RN) :
    range (parabolicConvexClosureClosedMap r h) =
      parabolicConvexClosureEndpointCircle RN (-h) ∪ parabolicConvexClosureEndpointCircle RN h ∪
        parabolicConvexClosureLateralCarrier r h := by
  rw [parabolicConvexClosureClosedMap_range hrpos]
  ext p
  change (p 2 ∈ Icc (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2)) ↔
    ((p 2 = -h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = RN) ∨
      (p 2 = h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = RN)) ∨
      (p 2 ∈ Ioo (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2))
  constructor
  · rintro ⟨hz, hp⟩
    by_cases heL : p 2 = -h
    · exact Or.inl (Or.inl ⟨heL, by simpa only [heL, hl] using hp⟩)
    by_cases heU : p 2 = h
    · exact Or.inl (Or.inr ⟨heU, by simpa only [heU, hu] using hp⟩)
    exact Or.inr ⟨⟨lt_of_le_of_ne hz.1 (Ne.symm heL), lt_of_le_of_ne hz.2 heU⟩, hp⟩
  · rintro ((⟨hz, hp⟩ | ⟨hz, hp⟩) | ⟨hz, hp⟩)
    · refine ⟨?_, ?_⟩
      · rw [hz]; exact ⟨le_rfl, by linarith⟩
      · simpa only [hz, hl] using hp
    · refine ⟨?_, ?_⟩
      · rw [hz]; exact ⟨by linarith, le_rfl⟩
      · simpa only [hz, hu] using hp
    · exact ⟨Ioo_subset_Icc_self hz, hp⟩

/-- Ordinary meridian endpoint and interior positivity imply positivity on the closed interval. -/
theorem parabolicConvexClosure_radius_pos_closed {r : ℝ → ℝ} {h RN : ℝ}
    (hRN : 0 < RN) (hl : r (-h) = RN) (hu : r h = RN)
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z) : ∀ z ∈ Icc (-h) h, 0 < r z := by
  intro z hz
  by_cases heL : z = -h
  · simpa only [heL, hl] using hRN
  by_cases heU : z = h
  · simpa only [heU, hu] using hRN
  exact hRN.trans (hrpos z ⟨lt_of_le_of_ne hz.1 (Ne.symm heL), lt_of_le_of_ne hz.2 heU⟩)

/-- The existing actual native open lateral map is an embedding via its inclusion into the
constructed closed annulus. This is a topological claim, not endpoint height smoothness. -/
theorem parabolicConvexClosure_nativeMap_isEmbedding {r : ℝ → ℝ} {h : ℝ}
    (hr : ContinuousOn r (Icc (-h) h)) (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    Topology.IsEmbedding
      (parabolicConvexClosureNativeMap r (⟨Ioo (-h) h, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ)) := by
  change Topology.IsEmbedding (parabolicConvexClosureClosedMap r h ∘
    Prod.map id (Set.inclusion (Ioo_subset_Icc_self : Ioo (-h) h ⊆ Icc (-h) h)))
  exact (parabolicConvexClosureClosedMap_isClosedEmbedding hr hrpos).isEmbedding.comp
    (Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion Ioo_subset_Icc_self))

end
end TightVer401


