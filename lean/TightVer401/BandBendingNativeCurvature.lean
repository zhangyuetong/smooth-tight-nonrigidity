import TightVer401.BandBendingRuledCurvature
import TightVer401.BandBendingMetricTranslation
import TightVer401.NativeProductPlaneBandCurvature

/-! The proved small-amplitude physical-coordinate curvature bound in the actual
preferred native and transported OpenAI band charts. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

section
variable {L b : ℝ} [Fact (0 < L)]
local instance nativeBandBendingCurvatureChartedSpace :
    ChartedSpace OAI.ClosedSurfaceR4.Plane (AddCircle L × Ioo (0 : ℝ) b) :=
  nativeProductPlaneChartedSpace _

/-- The genuine quotient chart represents any native band map by its translated lift. -/
theorem bandBending_native_chart_lift_germ
    (F : AddCircle L × Ioo (0 : ℝ) b → Ambient)
    (p : AddCircle L × Ioo (0 : ℝ) b) (s : ℝ) (hs : periodProjection L s = p.1) :
    nativeProductCoordinateMap F p =ᶠ[𝓝 (![0, (p.2 : ℝ)] : Coord)]
      (fun q => bandCoordinateLift F (smoothingSeamShift s q)) := by
  have hu : (fun t : ℝ => ((chartAt ℝ p.2).symm t : ℝ)) =ᶠ[𝓝 (p.2 : ℝ)] id := by
    simpa [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, Function.comp_def] using
      ((bandOpen b).chartAt_subtype_val_symm_eventuallyEq (H := ℝ) (x := p.2)).symm
  have hu' := hu.comp_tendsto ((continuous_apply 1).tendsto (![0, (p.2 : ℝ)] : Coord))
  filter_upwards [hu'] with q hq
  change ((chartAt ℝ p.2).symm (q 1) : ℝ) = q 1 at hq
  have hbq : q 1 ∈ Ioo (0 : ℝ) b := by
    rw [← hq]
    exact ((chartAt ℝ p.2).symm (q 1)).property
  have hc : (chartAt ℝ p.1).symm (q 0) = periodProjection L (q 0 + s) := by
    change (OAI.RawQuotientLie.addLeftChart (periodChart L) p.1).symm (q 0) = _
    rw [OAI.RawQuotientLie.addLeftChart_symm_apply, ← hs]
    change periodProjection L s + periodProjection L (q 0) = periodProjection L (q 0 + s)
    rw [← map_add, add_comm s (q 0)]
  have hh : (chartAt ℝ p.2).symm (q 1) = (⟨q 1, hbq⟩ : Ioo (0 : ℝ) b) :=
    Subtype.ext hq
  change F ((chartAt ℝ p.1).symm (q 0), (chartAt ℝ p.2).symm (q 1)) = _
  rw [hc, hh]
  simp only [bandCoordinateLift, smoothingSeamShift, Matrix.cons_val_zero,
    Matrix.cons_val_one, dif_pos hbq]

/-- The perturbed native chart is the actual translated physical perturbation. -/
theorem bandBending_native_branch_chart_germ (d : PeriodicRuledFrame L)
    (Y : AddCircle L × Ioo (0 : ℝ) b → Ambient) (a : ℝ)
    (p : AddCircle L × Ioo (0 : ℝ) b) (s : ℝ) (hs : periodProjection L s = p.1) :
    nativeProductCoordinateMap (d.bandMap + a • Y) p =ᶠ[𝓝 (![0, (p.2 : ℝ)] : Coord)]
      (fun q => ruledMap d.γ d.E (smoothingSeamShift s q) +
        a • bandCoordinateLift Y (smoothingSeamShift s q)) := by
  have h := bandBending_native_chart_lift_germ (d.bandMap + a • Y) p s hs
  have hheight : ∀ᶠ q : Coord in 𝓝 (![0, (p.2 : ℝ)] : Coord), q 1 ∈ Ioo 0 b :=
    (isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds p.2.property
  filter_upwards [h, hheight] with q hq hbq
  rw [hq]
  simp only [bandCoordinateLift, smoothingSeamShift, Matrix.cons_val_zero,
    Matrix.cons_val_one, dif_pos hbq, Pi.add_apply, Pi.smul_apply,
    PeriodicRuledFrame.bandMap, periodicLift_coe, ruledMap]

/-- The uniform bound preserves curvature in the actual preferred native band charts. -/
theorem periodicRuledFrame_native_compact_bending_curvature_threshold
    (d : PeriodicRuledFrame L) (hb : 0 < b)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hcompact : HasCompactSupport Y) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p : AddCircle L × Ioo (0 : ℝ) b,
      gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap (d.bandMap + a • Y) p))
        (![0, (p.2 : ℝ)] : Coord) < 0 := by
  obtain ⟨δ, hδ, hbound⟩ := periodicRuledFrame_compact_bending_curvature_threshold d hb hY hcompact
  refine ⟨δ, hδ, fun a ha p => ?_⟩
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  rw [nativeProductPlane_curvature_of_chart_germ (bandBending_native_branch_chart_germ d Y a p s hs)]
  rw [bandBending_actual_curvature_translation (fun q => ruledMap d.γ d.E q + a • bandCoordinateLift Y q) s]
  exact hbound a ha _

end
end
end TightVer401
