import TightVer401.GaussTightnessNativeCharts
import TightVer401.GaussTightnessNativeSign
import TightVer401.GaussTightnessMaximumTrace
import TightVer401.ClassicalPositiveGaussConnected

/-! Uniqueness of actual native torus height maxima in regular normal
directions. The supplied Gauss chart covers the ENTIRE positive region;
its source, its given normal, and the native second form are unchanged.
Final consumer: `classicalPositiveGaussTightness_proved`. -/

open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- A regular actual native height maximum lies in the entire positive
region, and its actual native trace records its normal sign. -/
theorem gaussTightness_native_regular_localMax_positive_and_trace_sign
    (X : NonrigidTorusSource → Ambient) (hX : NativeTorusSmoothEmbedding X)
    (N : NonrigidTorusSource → RoundSphere)
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N)
    (horth : ∀ p (v : ℝ × ℝ), inner ℝ (N p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0)
    (w : Ambient) (hw : inner ℝ w w = 1)
    (hreg : ∀ p, (N p : Ambient) = w ∨ (N p : Ambient) = -w →
      Function.Injective (fderiv ℝ (gaussTightnessNativeNormalCoordinates N p) 0))
    (p : NonrigidTorusSource)
    (hmax : IsLocalMax (fun z => inner ℝ (X z) w) p) :
    p ∈ nativeTorusPositiveRegion X ∧
      (0 < (nativeTorusSecondFundamental X N p).trace ↔ w = -(N p : Ambient)) ∧
      ((nativeTorusSecondFundamental X N p).trace < 0 ↔ w = (N p : Ambient)) := by
  let F := nativeProductCoordinateMap X p
  let Q := gaussTightnessNativeNormalCoordinates N p
  have hF : ContDiffOn ℝ ∞ F univ := (nativeProductTorusCoordinateMap_contDiff hX.1 p).contDiffOn
  have hQ : ContDiffOn ℝ ∞ Q univ := (gaussTightness_native_normal_contDiff hN p).contDiffOn
  have hg := gaussTightness_native_inducedMetric_smoothPositiveOn hX p
  have hIsom : IsometricOn (inducedMetric F) F univ := inducedMetric_isometricOn hF
  have hn : ∀ q ∈ (univ : Set Coord), IsUnitNormalAt F (Q q) q :=
    fun q _ => gaussTightness_native_coordinates_unitNormal hX.1 N horth p q
  have hm : IsLocalMax (height F w) 0 := gaussTightness_native_localMax_height w hmax
  have hiF : Function.Injective (fderiv ℝ F 0) :=
    nativeProductTorusCoordinateMap_fderiv_injective hX.1 hX.2.1 p 0
  have hdF : DifferentiableAt ℝ F 0 :=
    ((nativeProductTorusCoordinateMap_contDiff hX.1 p).contDiffAt).differentiableAt (by simp)
  have hsign := gaussTightness_localMax_height_normal_eq_or_neg_of_injective
    hdF hiF (Q 0) w (hn 0 (mem_univ 0)) hw hm
  have hnormalSign : (N p : Ambient) = w ∨ (N p : Ambient) = -w := by
    have hs : w = (N p : Ambient) ∨ w = -(N p : Ambient) := by
      simpa only [Q, gaussTightness_native_normal_zero] using hsign
    rcases hs with hsame | hopp
    · exact Or.inl hsame.symm
    · right
      rw [hopp]
      simp
  have hiQ : Function.Injective (fderiv ℝ Q 0) := hreg p hnormalSign
  have hK := gaussTightness_localMax_curvature_pos_of_normal_injective
    hg hIsom hQ isOpen_univ hn (mem_univ 0) w hw hm hiQ
  have ht := gaussTightness_localMax_normal_trace_sign_of_normal_injective
    hg hIsom hQ isOpen_univ hn (mem_univ 0) w hw hm hiQ
  refine ⟨?_, ?_⟩
  · change 0 < nativeTorusChartCurvature X p
    rw [gaussTightness_native_curvature_zero]
    exact hK
  · simpa only [nativeTorusSecondFundamental, F, Q, gaussTightness_native_normal_zero] using ht

/-- A one-sheeted actual Gauss chart on the entire positive region forces
all local height maxima in a regular unit direction to be the same point.
The proof determines the common normal sign by continuity of the actual
native trace, without an outward-normal convention. -/
theorem gaussTightness_native_localMax_unique_of_regular_direction
    (X : NonrigidTorusSource → Ambient) (hX : NativeTorusSmoothEmbedding X)
    (N : NonrigidTorusSource → RoundSphere)
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N)
    (horth : ∀ p (v : ℝ × ℝ), inner ℝ (N p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0)
    (E : Set RoundSphere) (hE : E.Finite)
    (e : OpenPartialHomeomorph NonrigidTorusSource RoundSphere)
    (hsource : e.source = nativeTorusPositiveRegion X) (htarget : e.target = univ \ E)
    (he : EqOn e N e.source) (w : Ambient) (hw : inner ℝ w w = 1)
    (hreg : ∀ p, (N p : Ambient) = w ∨ (N p : Ambient) = -w →
      Function.Injective (fderiv ℝ (gaussTightnessNativeNormalCoordinates N p) 0)) :
    ∀ p q, IsLocalMax (fun z => inner ℝ (X z) w) p →
      IsLocalMax (fun z => inner ℝ (X z) w) q → p = q := by
  intro p q hmaxp hmaxq
  obtain ⟨hp, hposp, hnegp⟩ := gaussTightness_native_regular_localMax_positive_and_trace_sign
    X hX N hN horth w hw hreg p hmaxp
  obtain ⟨hq, hposq, hnegq⟩ := gaussTightness_native_regular_localMax_positive_and_trace_sign
    X hX N hN horth w hw hreg q hmaxq
  have hconn := nativeTorusPositiveRegion_isPreconnected_of_gauss_chart X E hE e hsource htarget
  have hsymm (z : NonrigidTorusSource) : (nativeTorusSecondFundamental X N z).IsSymm :=
    gaussTightness_secondFundamental_isSymm
      (nativeProductTorusCoordinateMap_contDiff hX.1 z).contDiffOn
      isOpen_univ (mem_univ 0) (N z : Ambient)
  have hdet (z : NonrigidTorusSource) (hz : z ∈ nativeTorusPositiveRegion X) :
      0 < (nativeTorusSecondFundamental X N z).det := by
    have hg := gaussTightness_native_inducedMetric_smoothPositiveOn hX z
    have hF : ContDiffOn ℝ ∞ (nativeProductCoordinateMap X z) univ :=
      (nativeProductTorusCoordinateMap_contDiff hX.1 z).contDiffOn
    have hn : IsUnitNormalAt (nativeProductCoordinateMap X z) (N z : Ambient) 0 := by
      simpa only [gaussTightness_native_normal_zero] using
        gaussTightness_native_coordinates_unitNormal hX.1 N horth z 0
    change 0 < nativeTorusChartCurvature X z at hz
    rw [gaussTightness_native_curvature_zero] at hz
    rw [nativeTorusSecondFundamental,
      det_secondFundamental_eq_gaussianCurvature_mul_det hg
        (inducedMetric_isometricOn hF) isOpen_univ (mem_univ 0) hn]
    exact mul_pos hz (hg.2 0 (mem_univ 0)).det_pos
  have htraceiff := real_two_matrix_trace_pos_iff_on_preconnected hconn
    (nativeTorusSecondFundamental X N)
    (nativeTorusSecondFundamental_continuous hX.1 hN.continuous).continuousOn
    (fun z _ => hsymm z) hdet hp hq
  have hne (z : NonrigidTorusSource) (hz : z ∈ nativeTorusPositiveRegion X) :
      (nativeTorusSecondFundamental X N z).trace ≠ 0 :=
    real_two_matrix_trace_ne_zero_of_det_pos _ (hsymm z) (hdet z hz)
  have hnormalEq : (N p : Ambient) = (N q : Ambient) := by
    by_cases hpos : 0 < (nativeTorusSecondFundamental X N p).trace
    · have hwp := hposp.mp hpos
      have hwq := hposq.mp (htraceiff.mp hpos)
      exact neg_injective (hwp.symm.trans hwq)
    · have hneg : (nativeTorusSecondFundamental X N p).trace < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) (hne p hp)
      have hnotq : ¬ 0 < (nativeTorusSecondFundamental X N q).trace :=
        fun hh => hpos (htraceiff.mpr hh)
      have hnegq' : (nativeTorusSecondFundamental X N q).trace < 0 :=
        lt_of_le_of_ne (le_of_not_gt hnotq) (hne q hq)
      exact (hnegp.mp hneg).symm.trans (hnegq.mp hnegq')
  have hps : p ∈ e.source := by rwa [hsource]
  have hqs : q ∈ e.source := by rwa [hsource]
  apply e.injOn hps hqs
  rw [he hps, he hqs]
  exact Subtype.ext hnormalEq

end
end TightVer401
