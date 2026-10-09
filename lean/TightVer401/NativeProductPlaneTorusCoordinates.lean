import TightVer401.ProtectedTorusPositiveGaussCurvatureCharts
import TightVer401.ProtectedTorusPositiveGaussNormalCalculus

/-! Actual global coordinate representatives of smooth native torus immersions.
The preferred inverse chart is the literal globally smooth quotient cover.
The cover's actual derivative is the explicit finTwoArrow linear equivalence,
so chain rule and actual native immersion prove rank at every physical Coord.
No global model/metric compatibility or smooth-rank conclusion is supplied. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance nativeProductTorusCoordinatesPeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Actual translated quotient product cover of the native torus. -/
def nativeProductTorusCoordinateCover (s u : ℝ) (q : Coord) : NonrigidTorusSource :=
  (periodProjection (2 * Real.pi) (s + q 0),
    periodProjection (2 * Real.pi) (u + q 1))

/-- The actual quotient cover is globally smooth. -/
theorem nativeProductTorusCoordinateCover_contMDiff (s u : ℝ) :
    ContMDiff 𝓘(ℝ, Coord) nativeProductModel ∞ (nativeProductTorusCoordinateCover s u) := by
  have h0 : ContDiff ℝ ∞ (fun q : Coord => s + q 0) :=
    contDiff_const.add (_root_.contDiff_apply ℝ ℝ (0 : Fin 2))
  have h1 : ContDiff ℝ ∞ (fun q : Coord => u + q 1) :=
    contDiff_const.add (_root_.contDiff_apply ℝ ℝ (1 : Fin 2))
  exact ((periodProjection_contMDiff (2 * Real.pi)).comp h0.contMDiff).prodMk
    ((periodProjection_contMDiff (2 * Real.pi)).comp h1.contMDiff)

/-- Actual cover derivative is the explicit coordinate/product equivalence. -/
theorem nativeProductTorusCoordinateCover_mfderiv (s u : ℝ) (q : Coord) :
    mfderiv 𝓘(ℝ, Coord) nativeProductModel (nativeProductTorusCoordinateCover s u) q =
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap := by
  have hQ (t : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (periodProjection (2 * Real.pi)) t (ContinuousLinearMap.id ℝ ℝ) := by
    have hd := ((periodProjection_contMDiff (2 * Real.pi) t).mdifferentiableAt
      (by simp)).hasMFDerivAt
    rw [protectedTorusPositiveGauss_periodProjection_mfderiv] at hd
    exact hd
  have h0 : HasFDerivAt (fun x : Coord => s + x 0)
      (ContinuousLinearMap.proj (R := ℝ) 0) q :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) q).const_add s
  have h1 : HasFDerivAt (fun x : Coord => u + x 1)
      (ContinuousLinearMap.proj (R := ℝ) 1) q :=
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q).const_add u
  have hd := ((hQ (s + q 0)).comp q h0.hasMFDerivAt).prodMk
    ((hQ (u + q 1)).comp q h1.hasMFDerivAt)
  change HasMFDerivAt 𝓘(ℝ, Coord) nativeProductModel
    (nativeProductTorusCoordinateCover s u) q _ at hd
  have he := hd.mfderiv
  change (mfderiv 𝓘(ℝ, Coord) nativeProductModel
      (nativeProductTorusCoordinateCover s u) q : Coord →L[ℝ] (ℝ × ℝ)) =
    ((ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj (R := ℝ) 0)).prod
      ((ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj (R := ℝ) 1)) at he
  change (mfderiv 𝓘(ℝ, Coord) nativeProductModel
    (nativeProductTorusCoordinateCover s u) q : Coord →L[ℝ] (ℝ × ℝ)) = _
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun D : Coord →L[ℝ] (ℝ × ℝ) => D v) he

/-- The native preferred representative is literally F composed with the actual cover. -/
theorem nativeProductTorusCoordinateMap_eq_cover (F : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) :
    nativeProductCoordinateMap F p = F ∘ nativeProductTorusCoordinateCover s u :=
  protectedTorusPositiveGauss_chart_lift F p s u hs hu

/-- Every actual preferred coordinate representative is globally smooth. -/
theorem nativeProductTorusCoordinateMap_contDiff {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F) (p : NonrigidTorusSource) :
    ContDiff ℝ ∞ (nativeProductCoordinateMap F p) := by
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨u,hu⟩ := QuotientAddGroup.mk_surjective p.2
  rw [nativeProductTorusCoordinateMap_eq_cover F p s u hs hu]
  exact (hF.comp (nativeProductTorusCoordinateCover_contMDiff s u)).contDiff

/-- Exact actual fderiv of the global coordinate representative at every point. -/
theorem nativeProductTorusCoordinateMap_fderiv {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) (q : Coord) :
    fderiv ℝ (nativeProductCoordinateMap F p) q =
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F
        (nativeProductTorusCoordinateCover s u q)).comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap := by
  rw [nativeProductTorusCoordinateMap_eq_cover F p s u hs hu]
  have hd := mfderiv_comp q
    ((hF (nativeProductTorusCoordinateCover s u q)).mdifferentiableAt (by simp))
    ((nativeProductTorusCoordinateCover_contMDiff s u q).mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient)
      (F ∘ nativeProductTorusCoordinateCover s u) q : Coord →L[ℝ] Ambient) =
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F
      (nativeProductTorusCoordinateCover s u q) : (ℝ × ℝ) →L[ℝ] Ambient).comp
      (mfderiv 𝓘(ℝ, Coord) nativeProductModel
        (nativeProductTorusCoordinateCover s u) q : Coord →L[ℝ] (ℝ × ℝ)) at hd
  have hc : (mfderiv 𝓘(ℝ, Coord) nativeProductModel
      (nativeProductTorusCoordinateCover s u) q : Coord →L[ℝ] (ℝ × ℝ)) =
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap :=
      nativeProductTorusCoordinateCover_mfderiv s u q
  rw [mfderiv_eq_fderiv, hc] at hd
  exact hd

/-- Actual native immersion gives actual coordinate derivative rank globally. -/
theorem nativeProductTorusCoordinateMap_fderiv_injective {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (p : NonrigidTorusSource) (q : Coord) :
    Function.Injective (fderiv ℝ (nativeProductCoordinateMap F p) q) := by
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨u,hu⟩ := QuotientAddGroup.mk_surjective p.2
  rw [nativeProductTorusCoordinateMap_fderiv hF p s u hs hu q]
  exact (himm _).comp (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective

end
end TightVer401
