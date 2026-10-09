import TightVer401.ParabolicConvexClosureBoundaryCosineTopology
import TightVer401.ParabolicConvexClosureGeometry

/-! Actual smooth embedded closed lateral annulus in the coordinator's cosine
parameter, with its registered manifold-with-boundary model.

Inputs are ordinary radius regularity on the open height interval, actual
positive radius there, and literal closed parabolic endpoint germs. At each
endpoint the cosine map is genuinely equal to a smooth polynomial collar
composed with a transverse coordinate whose derivative is nonzero. Interior
points use a true smooth profile germ and nonzero cosine-height derivative.
The same local maps prove injectivity of the actual manifold differential.
The topological embedding and exact image are independent exports from the
retained closed-annulus map. No pending specification is imported.
-/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance boundaryCosinePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem circleCollar_upper_eq {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    (θ : AddCircle (2 * Real.pi)) {s : ℝ} (hs : 0 ≤ s) (hsmall : mu * s^2 / 2 ≤ δ) :
    parabolicConvexClosureCircleCollar 1 RN mu h (θ, s) =
      revolutionEndCircleFull r (θ, h - mu * s^2 / 2) := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective θ
  rw [← ha]
  change parabolicConvexClosureCircleCollar 1 RN mu h (periodProjection (2 * Real.pi) a, s) =
    revolutionEndCircleFull r (periodProjection (2 * Real.pi) a, h - mu * s^2 / 2)
  rw [parabolicConvexClosureCircleCollar_representative,
    revolutionEndCircleFull_representative]
  exact parabolicConvexClosureCollar_upper_eq hmu hg hs hsmall

private theorem circleCollar_lower_eq {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    (θ : AddCircle (2 * Real.pi)) {s : ℝ} (hs : 0 ≤ s) (hsmall : mu * s^2 / 2 ≤ δ) :
    parabolicConvexClosureCircleCollar (-1) RN mu h (θ, s) =
      revolutionEndCircleFull r (θ, -h + mu * s^2 / 2) := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective θ
  rw [← ha]
  change parabolicConvexClosureCircleCollar (-1) RN mu h (periodProjection (2 * Real.pi) a, s) =
    revolutionEndCircleFull r (periodProjection (2 * Real.pi) a, -h + mu * s^2 / 2)
  rw [parabolicConvexClosureCircleCollar_representative,
    revolutionEndCircleFull_representative]
  exact parabolicConvexClosureCollar_lower_eq hmu hg hs hsmall

private theorem upper_boundary_germ {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    {p : AddCircle (2 * Real.pi) × unitInterval} (hp : (p.2 : ℝ) = 0) :
    (parabolicConvexClosureCircleCollar 1 RN mu h ∘
      Prod.map id (parabolicConvexClosureCosineUpper mu h) ∘
      parabolicConvexClosureBoundaryInclusion) =ᶠ[𝓝 p]
        parabolicConvexClosureBoundaryCosineMap r h := by
  have hc : Continuous (fun x : AddCircle (2 * Real.pi) × unitInterval =>
      mu * (parabolicConvexClosureCosineUpper mu h x.2)^2 / 2) := by
    exact (continuous_const.mul
      (((parabolicConvexClosureCosineUpper_contDiff mu h).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).pow 2)).div_const 2
  have hn : {x : AddCircle (2 * Real.pi) × unitInterval |
      mu * (parabolicConvexClosureCosineUpper mu h x.2)^2 / 2 < δ} ∈ 𝓝 p :=
    (isOpen_lt hc continuous_const).mem_nhds (by
      simpa [hp, parabolicConvexClosureCosineUpper] using hδ)
  filter_upwards [hn] with x hx
  change parabolicConvexClosureCircleCollar 1 RN mu h
      (x.1, parabolicConvexClosureCosineUpper mu h x.2) = _
  rw [parabolicConvexClosureBoundaryCosineMap_eq,
    ← parabolicConvexClosureCosineUpper_height hmu hh]
  exact circleCollar_upper_eq hmu hg x.1
    (parabolicConvexClosureCosineUpper_nonneg hmu hh x.2) hx.le

private theorem lower_boundary_germ {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    {p : AddCircle (2 * Real.pi) × unitInterval} (hp : (p.2 : ℝ) = 1) :
    (parabolicConvexClosureCircleCollar (-1) RN mu h ∘
      Prod.map id (parabolicConvexClosureCosineLower mu h) ∘
      parabolicConvexClosureBoundaryInclusion) =ᶠ[𝓝 p]
        parabolicConvexClosureBoundaryCosineMap r h := by
  have hc : Continuous (fun x : AddCircle (2 * Real.pi) × unitInterval =>
      mu * (parabolicConvexClosureCosineLower mu h x.2)^2 / 2) := by
    exact (continuous_const.mul
      (((parabolicConvexClosureCosineLower_contDiff mu h).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).pow 2)).div_const 2
  have hn : {x : AddCircle (2 * Real.pi) × unitInterval |
      mu * (parabolicConvexClosureCosineLower mu h x.2)^2 / 2 < δ} ∈ 𝓝 p :=
    (isOpen_lt hc continuous_const).mem_nhds (by
      simpa [hp, parabolicConvexClosureCosineLower] using hδ)
  filter_upwards [hn] with x hx
  change parabolicConvexClosureCircleCollar (-1) RN mu h
      (x.1, parabolicConvexClosureCosineLower mu h x.2) = _
  rw [parabolicConvexClosureBoundaryCosineMap_eq,
    ← parabolicConvexClosureCosineLower_height hmu hh]
  exact circleCollar_lower_eq hmu hg x.1
    (parabolicConvexClosureCosineLower_nonneg hmu hh x.2) hx.le

set_option maxHeartbeats 800000 in
/-- A genuine smooth full-cylinder germ of the exact boundary map, with its
actual full-cylinder differential injective at the specified point. -/
theorem parabolicConvexClosureBoundaryCosineMap_regular_germ {RN mu h δ : ℝ}
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hlower : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    (hupper : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    (p : AddCircle (2 * Real.pi) × unitInterval) :
    ∃ F : AddCircle (2 * Real.pi) × ℝ → Ambient,
      ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F ∧
      (F ∘ parabolicConvexClosureBoundaryInclusion =ᶠ[𝓝 p]
        parabolicConvexClosureBoundaryCosineMap r h) ∧
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F
        (parabolicConvexClosureBoundaryInclusion p)) := by
  have hid : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) := contMDiff_id
  by_cases hp0 : (p.2 : ℝ) = 0
  · let s := parabolicConvexClosureCosineUpper mu h
    have hs : ContMDiff nativeProductModel nativeProductModel ∞ (Prod.map id s) :=
      hid.prodMap (parabolicConvexClosureCosineUpper_contDiff mu h).contMDiff
    refine ⟨parabolicConvexClosureCircleCollar 1 RN mu h ∘ Prod.map id s,
      (parabolicConvexClosureCircleCollar_contMDiff 1 RN mu h).comp hs,
      upper_boundary_germ hmu hh hδ hupper hp0, ?_⟩
    rw [mfderiv_comp _
      ((parabolicConvexClosureCircleCollar_contMDiff 1 RN mu h _).mdifferentiableAt (by simp))
      ((hs _).mdifferentiableAt (by simp))]
    have houter : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (parabolicConvexClosureCircleCollar 1 RN mu h)
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s
          (parabolicConvexClosureBoundaryInclusion p))) := by
      apply parabolicConvexClosureCircleCollar_mfderiv_injective
        (σ := 1) (RN := RN) (mu := mu) (h := h) hmu.ne'
        ((Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s)
          (parabolicConvexClosureBoundaryInclusion p))
      simpa [s, parabolicConvexClosureBoundaryInclusion, hp0,
        parabolicConvexClosureCosineUpper] using hRN.ne'
    have hinner : Function.Injective (mfderiv nativeProductModel nativeProductModel
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s)
        (parabolicConvexClosureBoundaryInclusion p)) := by
      have hds : HasDerivAt s (protectedTorusCollarScale h mu * (Real.pi / 2))
          (parabolicConvexClosureBoundaryInclusion p).2 := by
        simpa [s, parabolicConvexClosureBoundaryInclusion, hp0] using
          parabolicConvexClosureCosineUpper_hasDerivAt mu h (p.2 : ℝ)
      have hd : protectedTorusCollarScale h mu * (Real.pi / 2) ≠ 0 :=
        mul_ne_zero (ne_of_gt (parabolicConvexClosure_cosineScale_pos hmu hh))
        (div_ne_zero Real.pi_ne_zero (by norm_num))
      exact parabolicConvexClosure_scalarReparam_mfderiv_injective
        (s := s) (d := protectedTorusCollarScale h mu * (Real.pi / 2))
        (parabolicConvexClosureBoundaryInclusion p) hds hd
    intro v w he
    exact hinner (houter he)
  by_cases hp1 : (p.2 : ℝ) = 1
  · let s := parabolicConvexClosureCosineLower mu h
    have hs : ContMDiff nativeProductModel nativeProductModel ∞ (Prod.map id s) :=
      hid.prodMap (parabolicConvexClosureCosineLower_contDiff mu h).contMDiff
    refine ⟨parabolicConvexClosureCircleCollar (-1) RN mu h ∘ Prod.map id s,
      (parabolicConvexClosureCircleCollar_contMDiff (-1) RN mu h).comp hs,
      lower_boundary_germ hmu hh hδ hlower hp1, ?_⟩
    rw [mfderiv_comp _
      ((parabolicConvexClosureCircleCollar_contMDiff (-1) RN mu h _).mdifferentiableAt (by simp))
      ((hs _).mdifferentiableAt (by simp))]
    have houter : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (parabolicConvexClosureCircleCollar (-1) RN mu h)
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s
          (parabolicConvexClosureBoundaryInclusion p))) := by
      apply parabolicConvexClosureCircleCollar_mfderiv_injective
        (σ := -1) (RN := RN) (mu := mu) (h := h) hmu.ne'
        ((Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s)
          (parabolicConvexClosureBoundaryInclusion p))
      simpa [s, parabolicConvexClosureBoundaryInclusion, hp1,
        parabolicConvexClosureCosineLower] using hRN.ne'
    have hinner : Function.Injective (mfderiv nativeProductModel nativeProductModel
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) s)
        (parabolicConvexClosureBoundaryInclusion p)) := by
      have hds : HasDerivAt s (-protectedTorusCollarScale h mu * (Real.pi / 2))
          (parabolicConvexClosureBoundaryInclusion p).2 := by
        simpa [s, parabolicConvexClosureBoundaryInclusion, hp1] using
          parabolicConvexClosureCosineLower_hasDerivAt mu h (p.2 : ℝ)
      have hd : -protectedTorusCollarScale h mu * (Real.pi / 2) ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (parabolicConvexClosure_cosineScale_pos hmu hh)))
        (div_ne_zero Real.pi_ne_zero (by norm_num))
      exact parabolicConvexClosure_scalarReparam_mfderiv_injective
        (s := s) (d := -protectedTorusCollarScale h mu * (Real.pi / 2))
        (parabolicConvexClosureBoundaryInclusion p) hds hd
    intro v w he
    exact hinner (houter he)
  have hpt : (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne p.2.property.1 (Ne.symm hp0), lt_of_le_of_ne p.2.property.2 hp1⟩
  have hz := parabolicConvexClosureCosineHeight_mem_interior hh hpt
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension isOpen_Ioo hr hz
  let b := parabolicConvexClosureCosineHeight h
  have hb : ContMDiff nativeProductModel nativeProductModel ∞ (Prod.map id b) :=
    hid.prodMap (parabolicConvexClosureCosineHeight_contDiff h).contMDiff
  refine ⟨revolutionEndCircleFull q ∘ Prod.map id b,
    (revolutionEndCircleFull_contMDiff hq).comp hb, ?_, ?_⟩
  · have hge := hg.comp_tendsto
      (((parabolicConvexClosureCosineHeight_contDiff h).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).continuousAt)
    filter_upwards [hge] with x hx
    change q (b (x.2 : ℝ)) = r (b (x.2 : ℝ)) at hx
    rw [parabolicConvexClosureBoundaryCosineMap_eq]
    simp [revolutionEndCircleFull, hx, b, parabolicConvexClosureBoundaryInclusion]
  · rw [mfderiv_comp _
      ((revolutionEndCircleFull_contMDiff hq _).mdifferentiableAt (by simp))
      ((hb _).mdifferentiableAt (by simp))]
    have houter : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (revolutionEndCircleFull q)
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) b
          (parabolicConvexClosureBoundaryInclusion p))) := by
      apply revolutionEndCircleFull_mfderiv_injective hq
        ((Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) b)
          (parabolicConvexClosureBoundaryInclusion p))
      change q (b (p.2 : ℝ)) ≠ 0
      rw [hg.self_of_nhds]
      exact (hRN.trans (hrpos _ hz)).ne'
    have hinner : Function.Injective (mfderiv nativeProductModel nativeProductModel
        (Prod.map (id : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) b)
        (parabolicConvexClosureBoundaryInclusion p)) := by
      have hds : HasDerivAt b (-h * Real.pi * Real.sin (Real.pi * (p.2 : ℝ)))
          (parabolicConvexClosureBoundaryInclusion p).2 :=
        parabolicConvexClosureCosineHeight_hasDerivAt h (p.2 : ℝ)
      have hd : -h * Real.pi * Real.sin (Real.pi * (p.2 : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hh.ne') Real.pi_ne_zero)
        (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hpt.1)
          (by nlinarith [Real.pi_pos, hpt.2])).ne'
      exact parabolicConvexClosure_scalarReparam_mfderiv_injective
        (s := b) (d := -h * Real.pi * Real.sin (Real.pi * (p.2 : ℝ)))
        (parabolicConvexClosureBoundaryInclusion p) hds hd
    intro v w he
    exact hinner (houter he)

theorem parabolicConvexClosureBoundaryCosineMap_contMDiff {RN mu h δ : ℝ}
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hlower : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    (hupper : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h)) :
    ContMDiff parabolicConvexClosureBoundaryModel 𝓘(ℝ, Ambient) ∞
      (parabolicConvexClosureBoundaryCosineMap r h) := by
  intro p
  obtain ⟨F, hF, hg, _⟩ := parabolicConvexClosureBoundaryCosineMap_regular_germ
    hRN hmu hh hδ hr hrpos hlower hupper p
  exact ((hF.comp parabolicConvexClosureBoundaryInclusion_contMDiff) p).congr_of_eventuallyEq hg.symm

theorem parabolicConvexClosureBoundaryCosineMap_mfderiv_injective {RN mu h δ : ℝ}
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hlower : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    (hupper : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    (p : AddCircle (2 * Real.pi) × unitInterval) :
    Function.Injective (mfderiv parabolicConvexClosureBoundaryModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureBoundaryCosineMap r h) p) := by
  obtain ⟨F, hF, hg, hinj⟩ := parabolicConvexClosureBoundaryCosineMap_regular_germ
    hRN hmu hh hδ hr hrpos hlower hupper p
  rw [← hg.mfderiv_eq, mfderiv_comp _ ((hF _).mdifferentiableAt (by simp))
    ((parabolicConvexClosureBoundaryInclusion_contMDiff p).mdifferentiableAt (by simp))]
  exact hinj.comp (parabolicConvexClosureBoundaryInclusion_mfderiv_injective p)

end
end TightVer401
