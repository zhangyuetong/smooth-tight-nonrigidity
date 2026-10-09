import TightVer401.ParabolicConvexClosureGaussHeight

/-! The actual smooth scalar inverse of the outward Gauss height.

The inverse is the proved interval homeomorphism's inverse, extended by zero
outside its target interval. Nonzero actual derivative and the pinned smooth
local inverse theorem construct inverse germs. Actual interval monotonicity
identifies those germs with the constructed global inverse. No smooth inverse,
derivative regularity or surjectivity conclusion is an input.
-/

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual local smooth inverse from ordinary radius regularity and concavity. -/
theorem parabolicConvexClosure_gaussHeight_smooth_local_inverse {U : Set ℝ}
    (hU : IsOpen U) {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    {z : ℝ} (hz : z ∈ U) (hneg : deriv (deriv r) z < 0) :
    ∃ (g : ℝ → ℝ) (W : Set ℝ), IsOpen W ∧
      parabolicConvexClosureGaussHeight r z ∈ W ∧
      g (parabolicConvexClosureGaussHeight r z) = z ∧ ContDiffOn ℝ ∞ g W ∧
      ∀ y ∈ W, g y ∈ U ∧ parabolicConvexClosureGaussHeight r (g y) = y := by
  obtain ⟨q, hq, hgerm⟩ := parabolicConvexClosure_profile_extension hU hr hz
  let c := -deriv (deriv q) z / revolutionWeight (deriv q z)^3
  have hc : 0 < c := by
    dsimp only [c]
    rw [hgerm.deriv.deriv_eq, hgerm.deriv_eq]
    exact div_pos (neg_pos.mpr hneg) (pow_pos (revolutionWeight_pos _) 3)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft
    (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 c hc.ne')
  have he : HasFDerivAt (parabolicConvexClosureGaussHeight q)
      (e : ℝ →L[ℝ] ℝ) z := by
    convert! ((revolutionNormalHeight_hasDerivAt hq z).neg).hasFDerivAt using 1 <;> try rfl
    ext v
    simp [e, c, smul_eq_mul, neg_div]
  have hqheight : ContDiff ℝ ∞ (parabolicConvexClosureGaussHeight q) :=
    (revolutionNormalHeight_contDiff hq).neg
  obtain ⟨g, V, hV, hVz, hgz, hg, hright⟩ :=
    OAI.WeakMTWGlobalSupport.SmoothODE.exists_smooth_local_inverse hqheight he
  have hheight := parabolicConvexClosure_gaussHeight_germ hgerm
  have hpoint := hheight.self_of_nhds
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hheight.and (hU.mem_nhds hz))
  let W := V ∩ g ⁻¹' ball z ε
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV isOpen_ball
  have hWz : parabolicConvexClosureGaussHeight r z ∈ W := by
    rw [← hpoint]
    exact ⟨hVz, by simp [hgz, hε]⟩
  refine ⟨g, W, hW, hWz, ?_, hg.mono inter_subset_left, ?_⟩
  · rwa [← hpoint]
  · intro y hy
    have hb := hball hy.2
    exact ⟨hb.2, hb.1.symm.trans (hright y hy.1)⟩

section GlobalInverse
variable {RN mu h δ : ℝ} (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ)
  {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
  (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0)
  (hlower : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z))
    (Icc (-h) (-h + δ)))
  (hupper : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h))

/-- Explicit forward formula for the already constructed actual interval homeomorphism. -/
theorem parabolicConvexClosureGaussHeightHomeomorph_apply (z : Ioo (-h) h) :
    (parabolicConvexClosureGaussHeightHomeomorph hmu hh hδ hr hneg hlower hupper z : ℝ) =
      parabolicConvexClosureGaussHeight r z := rfl

/-- Actual interval inverse, with an irrelevant zero extension outside its target. -/
def parabolicConvexClosureGaussHeightInverse (y : ℝ) : ℝ := by
  classical
  exact if hy : y ∈ Ioo (-1 : ℝ) 1 then
    (parabolicConvexClosureGaussHeightHomeomorph hmu hh hδ hr hneg hlower hupper).symm ⟨y, hy⟩
  else 0

theorem parabolicConvexClosureGaussHeightInverse_spec {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper y ∈ Ioo (-h) h ∧
      parabolicConvexClosureGaussHeight r
        (parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper y) = y := by
  classical
  let E := parabolicConvexClosureGaussHeightHomeomorph hmu hh hδ hr hneg hlower hupper
  have hinv : parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper y =
      (E.symm ⟨y, hy⟩ : ℝ) := by
    simp only [parabolicConvexClosureGaussHeightInverse, dif_pos hy]
    rfl
  rw [hinv]
  refine ⟨(E.symm ⟨y, hy⟩).property, ?_⟩
  have he := congrArg Subtype.val (E.apply_symm_apply ⟨y, hy⟩)
  exact he

theorem parabolicConvexClosureGaussHeightInverse_left {z : ℝ} (hz : z ∈ Ioo (-h) h) :
    parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper
      (parabolicConvexClosureGaussHeight r z) = z := by
  have hs := parabolicConvexClosureGaussHeightInverse_spec hmu hh hδ hr hneg hlower hupper
    (parabolicConvexClosure_gaussHeight_mem r z)
  exact (parabolicConvexClosure_gaussHeight_strictMonoOn hr hneg).injOn hs.1 hz hs.2

/-- Smoothness of the actual inverse follows from constructed local inverse germs. -/
theorem parabolicConvexClosureGaussHeightInverse_contDiffOn :
    ContDiffOn ℝ ∞ (parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper)
      (Ioo (-1 : ℝ) 1) := by
  intro y hy
  let z := parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper y
  have hz := parabolicConvexClosureGaussHeightInverse_spec hmu hh hδ hr hneg hlower hupper hy
  obtain ⟨g, W, hW, hWy, hgy, hg, hright⟩ :=
    parabolicConvexClosure_gaussHeight_smooth_local_inverse isOpen_Ioo hr hz.1 (hneg z hz.1)
  rw [hz.2] at hWy hgy
  have heq : parabolicConvexClosureGaussHeightInverse hmu hh hδ hr hneg hlower hupper =ᶠ[𝓝 y] g := by
    filter_upwards [hW.mem_nhds hWy, isOpen_Ioo.mem_nhds hy] with t ht hty
    have hs := parabolicConvexClosureGaussHeightInverse_spec hmu hh hδ hr hneg hlower hupper hty
    have hg' := hright t ht
    exact (parabolicConvexClosure_gaussHeight_strictMonoOn hr hneg).injOn hs.1 hg'.1
      (hs.2.trans hg'.2.symm)
  exact ((hg y hWy).contDiffAt (hW.mem_nhds hWy)).congr_of_eventuallyEq heq |>.contDiffWithinAt

end GlobalInverse
end
end TightVer401
