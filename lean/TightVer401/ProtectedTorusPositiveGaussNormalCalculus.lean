import TightVer401.ProtectedTorusMap
import TightVer401.ProtectedTorusPositiveGaussNormalFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Exact actual differential on the literal convex branch of the assembled map.
The native quotient projection has derivative id in the registered translation
charts. The literal map agrees locally with its actual cosine-height rotation.
-/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry OAI.RawQuotientLie
set_option backward.isDefEq.respectTransparency false
local instance protectedPositiveGaussCalculusPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Exact derivative of the quotient projection in its registered charts. -/
theorem protectedTorusPositiveGauss_periodProjection_mfderiv (L : ℝ) [Fact (0 < L)]
    (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s =
      ContinuousLinearMap.id ℝ ℝ := by
  let a := periodProjection L s
  have hg : (extChartAt 𝓘(ℝ, ℝ) a ∘ periodProjection L) =ᶠ[𝓝 s]
      (fun t => t - s) := by
    have hs : ∀ᶠ t : ℝ in 𝓝 s, t - s ∈ (periodChart L).source := by
      have hz := (periodChart L).open_source.mem_nhds (periodChart_zero_source L)
      have hc : ContinuousAt (fun t : ℝ => t - s) s :=
        continuousAt_id.sub continuousAt_const
      change Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 (s - s)) at hc
      have hc0 : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 0) := by
        simpa only [sub_self] using hc
      exact hc0.eventually hz
    filter_upwards [hs] with t ht
    change (periodChart L).symm (-a + periodProjection L t) = t - s
    have he : -a + periodProjection L t = periodProjection L (t - s) := by
      simp [a, map_sub, sub_eq_add_neg, add_comm]
    rw [he]
    exact (periodChart L).left_inv ht
  have hd := mfderiv_comp s
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ℝ)) (mem_chart_source ℝ a))
    ((periodProjection_contMDiff L s).mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (extChartAt 𝓘(ℝ, ℝ) a ∘ periodProjection L) s : ℝ →L[ℝ] ℝ) =
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) a) a : ℝ →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s : ℝ →L[ℝ] ℝ) at hd
  rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
  rw [mfderiv_eq_fderiv, hg.fderiv_eq] at hd
  exact hd.symm.trans ((hasFDerivAt_id s).sub_const s).fderiv

/-- The literal product quotient projection. -/
def protectedTorusPositiveGaussProductProjection (p : ℝ × ℝ) : NonrigidTorusSource :=
  (periodProjection (2 * Real.pi) p.1, periodProjection (2 * Real.pi) p.2)

theorem protectedTorusPositiveGaussProductProjection_contMDiff :
    ContMDiff nativeProductModel nativeProductModel ∞
      protectedTorusPositiveGaussProductProjection :=
  ((periodProjection_contMDiff (2 * Real.pi)).comp contMDiff_fst).prodMk
    ((periodProjection_contMDiff (2 * Real.pi)).comp contMDiff_snd)

theorem protectedTorusPositiveGaussProductProjection_mfderiv (p : ℝ × ℝ) :
    mfderiv nativeProductModel nativeProductModel protectedTorusPositiveGaussProductProjection p =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  let Q := periodProjection (2 * Real.pi)
  have h1 := mfderiv_comp p
    ((periodProjection_contMDiff (2 * Real.pi) p.1).mdifferentiableAt (by simp))
    (mdifferentiableAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)))
  have h2 := mfderiv_comp p
    ((periodProjection_contMDiff (2 * Real.pi) p.2).mdifferentiableAt (by simp))
    (mdifferentiableAt_snd (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)))
  rw [protectedTorusPositiveGauss_periodProjection_mfderiv, mfderiv_fst] at h1
  rw [protectedTorusPositiveGauss_periodProjection_mfderiv, mfderiv_snd] at h2
  change (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (Q ∘ Prod.fst) p : (ℝ × ℝ) →L[ℝ] ℝ) =
    (ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) at h1
  change (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (Q ∘ Prod.snd) p : (ℝ × ℝ) →L[ℝ] ℝ) =
    (ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) at h2
  rw [ContinuousLinearMap.id_comp] at h1 h2
  have hp := mfderiv_prodMk
    (((periodProjection_contMDiff (2 * Real.pi)).comp contMDiff_fst p).mdifferentiableAt (by simp))
    (((periodProjection_contMDiff (2 * Real.pi)).comp contMDiff_snd p).mdifferentiableAt (by simp))
  change (mfderiv nativeProductModel nativeProductModel
      protectedTorusPositiveGaussProductProjection p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
    (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (Q ∘ Prod.fst) p : (ℝ × ℝ) →L[ℝ] ℝ).prod
      (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (Q ∘ Prod.snd) p : (ℝ × ℝ) →L[ℝ] ℝ) at hp
  rw [h1, h2] at hp
  change (mfderiv nativeProductModel nativeProductModel
    protectedTorusPositiveGaussProductProjection p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = _
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => D v) hp
  exact hv

/-- Cosine height lies in the actual meridian interior on the convex half. -/
theorem protectedTorusPositiveGauss_convex_height_mem {h φ : ℝ}
    (hh : 0 < h) (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    -h * Real.cos φ ∈ Ioo (-h) h := by
  have hs : Real.sin φ < 0 := by
    have ht := Real.sin_neg_of_neg_of_neg_pi_lt
      (show φ - 2 * Real.pi < 0 by linarith [hφ.2])
      (show -Real.pi < φ - 2 * Real.pi by linarith [hφ.1])
    simpa only [Real.sin_sub_two_pi] using ht
  have hl : -1 < Real.cos φ := by
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_ne_zero hs.ne]
  have hu : Real.cos φ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_ne_zero hs.ne]
  constructor <;> nlinarith

private def protectedPositiveGaussRotation (r : ℝ → ℝ) (h : ℝ)
    (p : ℝ × ℝ) : Ambient :=
  r (-h * Real.cos p.2) • revolutionRadial p.1 +
    (-h * Real.cos p.2) • revolutionAxis

private theorem protectedPositiveGaussRotation_fderiv {r : ℝ → ℝ} {h θ φ : ℝ}
    (hr : DifferentiableAt ℝ r (-h * Real.cos φ)) (v : ℝ × ℝ) :
    fderiv ℝ (protectedPositiveGaussRotation r h) (θ, φ) v =
      (v.2 * (deriv r (-h * Real.cos φ) * (h * Real.sin φ))) • revolutionRadial θ +
      (r (-h * Real.cos φ) * v.1) • revolutionAngular θ +
      (v.2 * (h * Real.sin φ)) • revolutionAxis := by
  let B : ℝ → ℝ := fun u => -h * Real.cos u
  have hB : HasDerivAt B (h * Real.sin φ) φ := by
    convert! (Real.hasDerivAt_cos φ).const_mul (-h) using 1 <;> simp [B] <;> ring
  have hA := hr.hasDerivAt.comp φ hB
  have hAr := hA.hasFDerivAt.comp (θ, φ)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (θ, φ)))
  have hBr := hB.hasFDerivAt.comp (θ, φ)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (θ, φ)))
  have hEr := (revolutionRadial_hasDerivAt θ).hasFDerivAt.comp (θ, φ)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (θ, φ)))
  have hd := (hAr.smul hEr).add
    (hBr.smul (hasFDerivAt_const (c := revolutionAxis) (θ, φ)))
  have hv := congrArg (fun D => D v) hd.fderiv
  change fderiv ℝ (protectedPositiveGaussRotation r h) (θ, φ) v = _ at hv
  simpa [ContinuousLinearMap.comp_apply, smul_smul, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc, B] using hv

/-- Actual native differential on the literal convex branch, for every tangent vector. -/
theorem protectedTorusPositiveGauss_convex_mfderiv {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (θ φ : ℝ)
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) (v : ℝ × ℝ) :
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (protectedTorusMap d.saddle d.meridian h)
      (periodProjection (2 * Real.pi) θ, periodProjection (2 * Real.pi) φ) v : Ambient) =
      (v.2 * (deriv d.meridian (-h * Real.cos φ) * (h * Real.sin φ))) • revolutionRadial θ +
      (d.meridian (-h * Real.cos φ) * v.1) • revolutionAngular θ +
      (v.2 * (h * Real.sin φ)) • revolutionAxis := by
  let F := protectedTorusMap d.saddle d.meridian h
  let P := protectedTorusPositiveGaussProductProjection
  have hg : F ∘ P =ᶠ[𝓝 (θ, φ)] protectedPositiveGaussRotation d.meridian h := by
    filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hφ] with p hp
    have he : (AddCircle.equivIco (2 * Real.pi) 0
        (periodProjection (2 * Real.pi) p.2)).val = p.2 :=
      congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show p.2 ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) from
          ⟨by linarith [hp.1, Real.pi_pos], by simpa using hp.2⟩))
    change protectedTorusMap d.saddle d.meridian h
      (periodProjection (2 * Real.pi) p.1, periodProjection (2 * Real.pi) p.2) =
      protectedPositiveGaussRotation d.meridian h p
    simp only [protectedTorusMap, he, if_neg (not_le.mpr hp.1),
      protectedTorusConvexCylinder, revolutionEndCircleFull,
      revolutionCircleRadial_representative, protectedPositiveGaussRotation]
  have hd := mfderiv_comp (θ, φ)
    (((protectedTorusMap_contMDiff_and_immersion d).1 (P (θ, φ))).mdifferentiableAt (by simp))
    ((protectedTorusPositiveGaussProductProjection_contMDiff (θ, φ)).mdifferentiableAt (by simp))
  rw [protectedTorusPositiveGaussProductProjection_mfderiv] at hd
  change (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F ∘ P) (θ, φ) :
      (ℝ × ℝ) →L[ℝ] Ambient) =
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (P (θ, φ)) :
      (ℝ × ℝ) →L[ℝ] Ambient).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ)) at hd
  rw [ContinuousLinearMap.comp_id] at hd
  have hraw : (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F ∘ P) (θ, φ) :
      (ℝ × ℝ) →L[ℝ] Ambient) = fderiv ℝ (F ∘ P) (θ, φ) := by
    unfold nativeProductModel
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact mfderiv_eq_fderiv
  have hv := congrArg (fun D : (ℝ × ℝ) →L[ℝ] Ambient => D v) hd
  have hvraw := congrArg (fun D : (ℝ × ℝ) →L[ℝ] Ambient => D v) hraw
  have hvgerm := congrArg (fun D : (ℝ × ℝ) →L[ℝ] Ambient => D v) hg.fderiv_eq
  change (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (P (θ, φ)) :
    (ℝ × ℝ) →L[ℝ] Ambient) v = _
  exact hv.symm.trans (hvraw.trans (hvgerm.trans (protectedPositiveGaussRotation_fderiv
    ((d.meridian_smooth.contDiffAt (isOpen_Ioo.mem_nhds
      (protectedTorusPositiveGauss_convex_height_mem d.height_pos hφ))).differentiableAt (by simp)) v)))

end
end TightVer401

