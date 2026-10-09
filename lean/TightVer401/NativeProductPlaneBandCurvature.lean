import TightVer401.NativeProductPlaneCurvature
import TightVer401.PeriodicRuledFrame

/-! Direct preferred-chart intrinsic curvature for the actual native ruled band. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

section
variable {L b : ℝ} [Fact (0 < L)]
local instance nativeProductPlaneBandCurvatureChartedSpace : ChartedSpace OAI.ClosedSurfaceR4.Plane (AddCircle L × Ioo (0 : ℝ) b) :=
  nativeProductPlaneChartedSpace _

/-- Identify the actual preferred-chart center with the physical band coordinates. -/
theorem nativeProductPlane_band_chart_center
    (p : AddCircle L × Ioo (0 : ℝ) b) :
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p) =
      (![0, (p.2 : ℝ)] : Coord) := by
  apply (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective
  change (chartAt (ModelProd ℝ ℝ) p p : ℝ × ℝ) = (0, (p.2 : ℝ))
  apply Prod.ext
  · change (periodChart L).symm (-p.1 + p.1) = 0
    rw [neg_add_cancel]
    have h0 : periodChart L (0 : ℝ) = (0 : AddCircle L) := rfl
    simpa only [h0] using (periodChart L).left_inv (periodChart_zero_source L)
  · rfl

/-- The native preferred band chart is the translated physical ruled map near its center. -/
theorem nativeProductPlane_band_chart_germ (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) (s : ℝ) (hs : periodProjection L s = p.1) :
    nativeProductCoordinateMap d.bandMap p =ᶠ[𝓝 (![0, (p.2 : ℝ)] : Coord)]
      ruledMap (fun t => d.γ (s + t)) (fun t => d.E (s + t)) := by
  have hu : (fun t : ℝ => ((chartAt ℝ p.2).symm t : ℝ)) =ᶠ[𝓝 (p.2 : ℝ)] id := by
    simpa [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, Function.comp_def] using
      ((bandOpen b).chartAt_subtype_val_symm_eventuallyEq (H := ℝ) (x := p.2)).symm
  have hu' := hu.comp_tendsto ((continuous_apply 1).tendsto (![0, (p.2 : ℝ)] : Coord))
  filter_upwards [hu'] with q hq
  change ((chartAt ℝ p.2).symm (q 1) : ℝ) = q 1 at hq
  have hc : (chartAt ℝ p.1).symm (q 0) = p.1 + periodProjection L (q 0) := by
    change (OAI.RawQuotientLie.addLeftChart (periodChart L) p.1).symm (q 0) = _
    simpa [periodChart, periodProjection] using
      OAI.RawQuotientLie.addLeftChart_symm_apply (periodChart L) p.1 (q 0)
  change d.period_γ.lift ((chartAt ℝ p.1).symm (q 0)) +
      ((chartAt ℝ p.2).symm (q 1) : ℝ) •
        d.period_E.lift ((chartAt ℝ p.1).symm (q 0)) = _
  rw [hc, ← hs, ← map_add, periodicLift_coe, periodicLift_coe, hq]
  rfl

/-- The actual transported band has the retained exact intrinsic curvature
in its genuine preferred chart at every band point. -/
theorem nativeProductPlane_band_curvature (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) (s : ℝ) (hs : periodProjection L s = p.1) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap d.bandMap p))
      (![0, (p.2 : ℝ)] : Coord) =
        -(d.τ s)^2 / (ruledEnergy (d.k s) (d.τ s) (p.2 : ℝ))^2 := by
  have hγ : ∀ t, HasDerivAt (fun t => d.γ (s + t)) (d.T (s + t)) t := by
    intro t
    have ht : HasDerivAt (fun r : ℝ => s + r) 1 t := by
      simpa using (hasDerivAt_id t).const_add s
    simpa [Function.comp_def] using (d.deriv_γ (s + t)).scomp t ht
  have hE : ∀ t, HasDerivAt (fun t => d.E (s + t))
      (-d.k (s + t) • d.T (s + t) + d.τ (s + t) • d.n (s + t)) t := by
    intro t
    have ht : HasDerivAt (fun r : ℝ => s + r) 1 t := by
      simpa using (hasDerivAt_id t).const_add s
    simpa [Function.comp_def] using (d.deriv_E (s + t)).scomp t ht
  have hγs : ContDiff ℝ ∞ (fun t => d.γ (s + t)) :=
    d.smooth_γ.comp (contDiff_const.add contDiff_id)
  have hEs : ContDiff ℝ ∞ (fun t => d.E (s + t)) :=
    d.smooth_E.comp (contDiff_const.add contDiff_id)
  have hX : ContDiff ℝ ∞ (ruledMap (fun t => d.γ (s + t)) (fun t => d.E (s + t))) :=
    (hγs.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (hEs.comp (contDiff_apply ℝ ℝ 0)))
  rw [nativeProductPlane_curvature_of_chart_germ (nativeProductPlane_band_chart_germ d p s hs)]
  simpa using ruled_gaussianCurvature hγ hE hX.contDiffOn isOpen_univ
    (fun q _ => d.orthonormal (s + q 0)) (fun q _ => d.torsion_ne_zero (s + q 0))
    (p := (![0, (p.2 : ℝ)] : Coord)) (mem_univ _)

/-- Strict negative intrinsic curvature of the actual transported native band. -/
theorem nativeProductPlane_band_curvature_neg (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap d.bandMap p))
      (![0, (p.2 : ℝ)] : Coord) < 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  rw [nativeProductPlane_band_curvature d p s hs]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (d.torsion_ne_zero s)))
    (sq_pos_of_pos (ruledEnergy_pos (d.torsion_ne_zero s)))

end
end
end TightVer401





