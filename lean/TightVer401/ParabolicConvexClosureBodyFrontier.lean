import TightVer401.ParabolicConvexClosureBody

/-! Exact interior and frontier of the actual convex carrier. The converse
interior implications are proved using actual small axial and horizontal
line movements, not supplied boundary characterization assumptions. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped Topology Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The endpoint disk in its literal Ambient plane. -/
def parabolicConvexClosureDisk (RN z : ℝ) : Set Ambient :=
  {p | p 2 = z ∧ ‖parabolicConvexClosureHorizontalCLM p‖ ≤ RN}

/-- Actual lateral points of interior height, characterized by radius equality. -/
def parabolicConvexClosureLateralCarrier (r : ℝ → ℝ) (h : ℝ) : Set Ambient :=
  {p | p 2 ∈ Ioo (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2)}

/-- The actual horizontal direction of an Ambient point, retaining zero height. -/
def parabolicConvexClosureHorizontalLift (p : Ambient) : Ambient :=
  WithLp.toLp 2 ![p 0, p 1, 0]

@[simp] theorem parabolicConvexClosureHorizontalLift_height (p : Ambient) :
    parabolicConvexClosureHorizontalLift p 2 = 0 := rfl

@[simp] theorem parabolicConvexClosureHorizontalLift_horizontal (p : Ambient) :
    parabolicConvexClosureHorizontalCLM (parabolicConvexClosureHorizontalLift p) =
      parabolicConvexClosureHorizontalCLM p := by
  rw [parabolicConvexClosureHorizontalCLM_apply, parabolicConvexClosureHorizontalCLM_apply]
  apply Complex.ext <;> rfl

private theorem parabolicConvexClosureBody_line_step {r : ℝ → ℝ} {h : ℝ} {p : Ambient}
    (hp : p ∈ interior (parabolicConvexClosureBodyCarrier r h)) (u : Ambient) :
    ∃ t : ℝ, t > 0 ∧ p + t • u ∈ parabolicConvexClosureBodyCarrier r h := by
  let f : ℝ → Ambient := fun t => p + t • u
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have ht : parabolicConvexClosureBodyCarrier r h ∈ 𝓝 (f 0) := by
    simpa [f] using (mem_interior_iff_mem_nhds.mp hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hf.continuousAt.eventually ht)
  refine ⟨δ / 2, half_pos hδ, hball ?_⟩
  change dist (δ / 2) 0 < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ

/-- An interior point has genuinely interior height; both endpoint planes are excluded. -/
theorem parabolicConvexClosureBody_interior_height {r : ℝ → ℝ} {h : ℝ} {p : Ambient}
    (hp : p ∈ interior (parabolicConvexClosureBodyCarrier r h)) : p 2 ∈ Ioo (-h) h := by
  have hbody := interior_subset hp
  constructor
  · by_contra hnot
    have he : p 2 = -h := le_antisymm (le_of_not_gt hnot) hbody.1.1
    obtain ⟨t, ht, hpt⟩ := parabolicConvexClosureBody_line_step hp
      (-parabolicConvexClosureRadialPoint 0 1)
    have hbound := hpt.1.1
    change -h ≤ p 2 + t * (-1) at hbound
    rw [he] at hbound
    linarith
  · by_contra hnot
    have he : p 2 = h := le_antisymm hbody.1.2 (le_of_not_gt hnot)
    obtain ⟨t, ht, hpt⟩ := parabolicConvexClosureBody_line_step hp
      (parabolicConvexClosureRadialPoint 0 1)
    have hbound := hpt.1.2
    change p 2 + t * 1 ≤ h at hbound
    rw [he, mul_one] at hbound
    linarith

/-- At positive radius, radial equality is excluded from the actual interior. -/
theorem parabolicConvexClosureBody_interior_radius {r : ℝ → ℝ} {h RN : ℝ}
    (hRN : 0 < RN) (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z) {p : Ambient}
    (hp : p ∈ interior (parabolicConvexClosureBodyCarrier r h)) :
    ‖parabolicConvexClosureHorizontalCLM p‖ < r (p 2) := by
  have hbody := interior_subset hp
  have hz := parabolicConvexClosureBody_interior_height hp
  have hrp : 0 < r (p 2) := hRN.trans (hrpos (p 2) hz)
  by_contra hnot
  have he : ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2) :=
    le_antisymm hbody.2 (le_of_not_gt hnot)
  obtain ⟨t, ht, hpt⟩ := parabolicConvexClosureBody_line_step hp
    (parabolicConvexClosureHorizontalLift p)
  have hheight : (p + t • parabolicConvexClosureHorizontalLift p) 2 = p 2 := by
    change p 2 + t * 0 = p 2
    ring
  have hhorizontal : parabolicConvexClosureHorizontalCLM
      (p + t • parabolicConvexClosureHorizontalLift p) =
      (1 + t) • parabolicConvexClosureHorizontalCLM p := by
    rw [map_add, map_smul, parabolicConvexClosureHorizontalLift_horizontal]
    rw [add_smul, one_smul]
  have hrad := hpt.2
  rw [hhorizontal, norm_smul, Real.norm_of_nonneg (by linarith), he, hheight] at hrad
  nlinarith [mul_pos ht hrp]

/-- Exact actual interior: strict height bounds and strict Euclidean horizontal radius. -/
theorem parabolicConvexClosureBody_mem_interior_iff {r : ℝ → ℝ} {h RN : ℝ}
    (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z) (p : Ambient) :
    p ∈ interior (parabolicConvexClosureBodyCarrier r h) ↔
      p 2 ∈ Ioo (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ < r (p 2) := by
  constructor
  · intro hp
    exact ⟨parabolicConvexClosureBody_interior_height hp,
      parabolicConvexClosureBody_interior_radius hRN hrpos hp⟩
  · rintro ⟨hz, hp⟩
    exact parabolicConvexClosureBody_mem_interior_of_lt hr hz hp

/-- Exact frontier disks and interior lateral points, from the actual closed carrier. -/
theorem parabolicConvexClosureBody_mem_frontier_iff {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hl : r (-h) = RN) (hu : r h = RN) (p : Ambient) :
    p ∈ frontier (parabolicConvexClosureBodyCarrier r h) ↔
      (p 2 = -h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ ≤ RN) ∨
      (p 2 = h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ ≤ RN) ∨
      (p 2 ∈ Ioo (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ = r (p 2)) := by
  rw [frontier, (parabolicConvexClosureBody_isClosed hr).closure_eq]
  constructor
  · rintro ⟨hbody, hnot⟩
    by_cases hzL : p 2 = -h
    · exact Or.inl ⟨hzL, by simpa only [hzL, hl] using hbody.2⟩
    by_cases hzU : p 2 = h
    · exact Or.inr (Or.inl ⟨hzU, by simpa only [hzU, hu] using hbody.2⟩)
    have hz : p 2 ∈ Ioo (-h) h :=
      ⟨lt_of_le_of_ne hbody.1.1 (Ne.symm hzL), lt_of_le_of_ne hbody.1.2 hzU⟩
    have hnotlt : ¬ ‖parabolicConvexClosureHorizontalCLM p‖ < r (p 2) := by
      intro hlt
      exact hnot ((parabolicConvexClosureBody_mem_interior_iff hRN hr hrpos p).mpr ⟨hz, hlt⟩)
    exact Or.inr (Or.inr ⟨hz, le_antisymm hbody.2 (le_of_not_gt hnotlt)⟩)
  · rintro (⟨hz, hp⟩ | ⟨hz, hp⟩ | ⟨hz, hp⟩)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hz]
        exact ⟨le_rfl, by linarith⟩
      · simpa only [hz, hl] using hp
      · intro hi
        have hheight := parabolicConvexClosureBody_interior_height hi
        rw [hz] at hheight
        exact (lt_irrefl (-h)) hheight.1
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hz]
        exact ⟨by linarith, le_rfl⟩
      · simpa only [hz, hu] using hp
      · intro hi
        have hheight := parabolicConvexClosureBody_interior_height hi
        rw [hz] at hheight
        exact (lt_irrefl h) hheight.2
    · refine ⟨⟨Ioo_subset_Icc_self hz, hp.le⟩, ?_⟩
      intro hi
      have hrad := parabolicConvexClosureBody_interior_radius hRN hrpos hi
      rw [hp] at hrad
      exact (lt_irrefl (r (p 2))) hrad

 theorem parabolicConvexClosureBody_frontier {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hl : r (-h) = RN) (hu : r h = RN) :
    frontier (parabolicConvexClosureBodyCarrier r h) =
      parabolicConvexClosureDisk RN (-h) ∪ parabolicConvexClosureDisk RN h ∪
        parabolicConvexClosureLateralCarrier r h := by
  ext p
  simpa only [mem_union, parabolicConvexClosureDisk, parabolicConvexClosureLateralCarrier,
    mem_setOf_eq, or_assoc] using parabolicConvexClosureBody_mem_frontier_iff hh hRN hr hrpos hl hu p

private theorem parabolicConvexClosure_radialPoint_body {r : ℝ → ℝ} {h z : ℝ}
    (hz : z ∈ Ioo (-h) h) (hrz : 0 ≤ r z) :
    parabolicConvexClosureRadialPoint (r z) z ∈ parabolicConvexClosureBodyCarrier r h := by
  refine ⟨Ioo_subset_Icc_self hz, ?_⟩
  simp [parabolicConvexClosureRadialPoint_horizontal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hrz]

/-- A genuine point witness to failure of central negation invariance. -/
theorem parabolicConvexClosureBody_exists_not_neg_mem {r : ℝ → ℝ} {h RN : ℝ}
    (hRN : 0 < RN) (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hasym : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) :
    ∃ p ∈ parabolicConvexClosureBodyCarrier r h, -p ∉ parabolicConvexClosureBodyCarrier r h := by
  obtain ⟨z, hz, he⟩ := hasym
  have hzI : z ∈ Ioo (-h) h := ⟨by linarith [hz.1, hz.2], hz.2⟩
  have hnzI : -z ∈ Ioo (-h) h := ⟨by linarith [hz.2], by linarith [hz.1, hz.2]⟩
  have hpos := hRN.trans (hrpos z hzI)
  have hnegpos := hRN.trans (hrpos (-z) hnzI)
  rcases lt_or_gt_of_ne he with hlt | hgt
  · refine ⟨parabolicConvexClosureRadialPoint (r z) z,
      parabolicConvexClosure_radialPoint_body hzI hpos.le, ?_⟩
    intro hp
    have hbound := hp.2
    have hheight : (-parabolicConvexClosureRadialPoint (r z) z) 2 = -z := rfl
    rw [map_neg, norm_neg, parabolicConvexClosureRadialPoint_horizontal, hheight] at hbound
    have hnorm : ‖(r z : ℂ)‖ = r z := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hnorm] at hbound
    exact (not_le_of_gt hlt) hbound
  · refine ⟨parabolicConvexClosureRadialPoint (r (-z)) (-z),
      parabolicConvexClosure_radialPoint_body hnzI hnegpos.le, ?_⟩
    intro hp
    have hbound := hp.2
    have hheight : (-parabolicConvexClosureRadialPoint (r (-z)) (-z)) 2 = z := by simp
    rw [map_neg, norm_neg, parabolicConvexClosureRadialPoint_horizontal, hheight] at hbound
    have hnorm : ‖(r (-z) : ℂ)‖ = r (-z) := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnegpos]
    rw [hnorm] at hbound
    exact (not_le_of_gt hgt) hbound

 theorem parabolicConvexClosureBody_not_neg_invariant {r : ℝ → ℝ} {h RN : ℝ}
    (hRN : 0 < RN) (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hasym : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) :
    Neg.neg '' parabolicConvexClosureBodyCarrier r h ≠ parabolicConvexClosureBodyCarrier r h := by
  obtain ⟨p, hp, hn⟩ := parabolicConvexClosureBody_exists_not_neg_mem hRN hrpos hasym
  intro he
  apply hn
  rw [← he]
  exact mem_image_of_mem Neg.neg hp

end
end TightVer401


