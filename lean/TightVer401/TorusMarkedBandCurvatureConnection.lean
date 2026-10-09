import TightVer401.TorusBandCurvatureConnection
import TightVer401.ProtectedTorusLinearFieldConnection

/-! A fresh small-amplitude curvature threshold for the literal contragredient
marked branches. Only applications of the retained physical-coordinate threshold,
periodicity, and actual native chart/placement comparisons are used. The actual
marked smoothness, zero strain, rank and baseline sign are ordinary producer data.
No unmarked amplitude bound or perturbed curvature conclusion is an input. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

variable {T w : ℝ} [Fact (0 < T)]
local instance markedBandCurvatureChartedSpace :
    ChartedSpace OAI.ClosedSurfaceR4.Plane (AddCircle T × Ioo (0 : ℝ) w) :=
  nativeProductPlaneChartedSpace _

/-- The actual physical band source has strictly positive height below w. -/
def markedRuledBandCoordinateDomain (w : ℝ) : Set Coord :=
  {q | q 1 ∈ Ioo (0 : ℝ) w}
/-- The marked baseline is B after the actual affine-isometry placement A. -/
def markedRuledBandCoordinateBase (d : PeriodicRuledFrame T)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (B : Ambient →L[ℝ] Ambient) : Coord → Ambient :=
  fun q => B (A (ruledMap d.γ d.E q))

/-- The marked bending is C after the linear part of the SAME placement A. -/
def markedRuledBandCoordinateField
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (C : Ambient →L[ℝ] Ambient) : Coord → Ambient :=
  fun q => C (A.linearIsometryEquiv (bandCoordinateLift Y q))

/-- Literal native-band branches corresponding to the two physical maps above. -/
def markedRuledBandNativeBranch (d : PeriodicRuledFrame T)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (B C : Ambient →L[ℝ] Ambient)
    (a : ℝ) : AddCircle T × Ioo (0 : ℝ) w → Ambient :=
  fun p => B (A ((d.bandMap (b := w)) p)) + a • C (A.linearIsometryEquiv (Y p))

/-- Only a local germ is identified: the native-band lift vanishes outside
its height domain, whereas the globally defined marked ruled baseline does not. -/
theorem markedRuledBand_native_branch_chart_germ (d : PeriodicRuledFrame T)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (B C : Ambient →L[ℝ] Ambient) (a : ℝ)
    (p : AddCircle T × Ioo (0 : ℝ) w) (s : ℝ)
    (hs : periodProjection T s = p.1) :
    nativeProductCoordinateMap (markedRuledBandNativeBranch d Y A B C a) p
      =ᶠ[𝓝 (![0, (p.2 : ℝ)] : Coord)]
      (fun q => markedRuledBandCoordinateBase d A B (smoothingSeamShift s q) +
        a • markedRuledBandCoordinateField Y A C (smoothingSeamShift s q)) := by
  have h := bandBending_native_chart_lift_germ
    (markedRuledBandNativeBranch d Y A B C a) p s hs
  have hheight : ∀ᶠ q : Coord in 𝓝 (![0, (p.2 : ℝ)] : Coord), q 1 ∈ Ioo 0 w :=
    (isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds p.2.property
  filter_upwards [h, hheight] with q hq hbq
  rw [hq]
  simp only [bandCoordinateLift, smoothingSeamShift, Matrix.cons_val_zero,
    Matrix.cons_val_one, dif_pos hbq, markedRuledBandNativeBranch,
    markedRuledBandCoordinateBase, markedRuledBandCoordinateField,
    PeriodicRuledFrame.bandMap, periodicLift_coe, ruledMap]

/-- A compact fundamental rectangle gives a NEW marked curvature bound on
all points of the original band's actual compact bending support. -/
theorem markedRuledBand_native_compact_curvature_threshold
    (d : PeriodicRuledFrame T) (hw : 0 < w)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (B C : Ambient →L[ℝ] Ambient)
    (hcompact : HasCompactSupport Y)
    (hX : ContDiff ℝ ∞ (markedRuledBandCoordinateBase d A B))
    (hY : IsInfinitesimalBendingOn (markedRuledBandCoordinateBase d A B)
      (markedRuledBandCoordinateField Y A C) (markedRuledBandCoordinateDomain w))
    (himm : ∀ q ∈ markedRuledBandCoordinateDomain w, Function.Injective
      (fderiv ℝ (markedRuledBandCoordinateBase d A B) q))
    (hneg : ∀ q ∈ markedRuledBandCoordinateDomain w, gaussianCurvature
      (inducedMetric (markedRuledBandCoordinateBase d A B)) q < 0) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p ∈ tsupport Y,
      gaussianCurvature
        (inducedMetric (nativeProductPlaneCoordinateMap
          (markedRuledBandNativeBranch d Y A B C a) p))
        (![0, (p.2 : ℝ)] : Coord) < 0 := by
  obtain ⟨lower, upper, hlo, _, hhi, hs⟩ := compact_band_support_uniform_bounds hw hcompact
  let X := markedRuledBandCoordinateBase d A B
  let V := markedRuledBandCoordinateField Y A C
  let K : Set Coord := (fun z : ℝ × ℝ => (![z.1, z.2] : Coord)) ''
    (Icc (0 : ℝ) T ×ˢ Icc lower upper)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous)
  have hU : IsOpen (markedRuledBandCoordinateDomain w) :=
    isOpen_Ioo.preimage (continuous_apply 1)
  have hKU : K ⊆ markedRuledBandCoordinateDomain w := by
    rintro q ⟨⟨s,u⟩, ⟨hs, hu⟩, rfl⟩
    change 0 < u ∧ u < w
    exact ⟨lt_of_lt_of_le hlo hu.1, lt_of_le_of_lt hu.2 hhi⟩
  obtain ⟨δ, hδ, hbound⟩ := bandBending_compact_actual_curvature_threshold
    hX.contDiffOn hY hU himm hK hKU (fun q hq => hneg q (hKU hq))
  refine ⟨δ, hδ, ?_⟩
  intro a ha p hp

  have hAp (q : Coord) :
      X (smoothingSeamShift T q) + a • V (smoothingSeamShift T q) = X q + a • V q := by
    have hYp := bandCoordinateLift_periodic Y (q 1) (q 0)
    change bandCoordinateLift Y (![q 0 + T, q 1] : Coord) =
      bandCoordinateLift Y (![q 0, q 1] : Coord) at hYp
    have hq : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
    change B (A (ruledMap d.γ d.E (smoothingSeamShift T q))) +
      a • C (A.linearIsometryEquiv (bandCoordinateLift Y (smoothingSeamShift T q))) = _
    simp only [smoothingSeamShift, ruledMap, Matrix.cons_val_zero, Matrix.cons_val_one,
      d.period_γ (q 0), d.period_E (q 0)]
    rw [hYp, hq]
    rfl
  have hperiod : Function.Periodic
      (fun s : ℝ => gaussianCurvature (inducedMetric (fun q => X q + a • V q))
        (![s, (p.2 : ℝ)] : Coord)) T := by
    intro s
    have hshift : (fun q => X (smoothingSeamShift T q) + a • V (smoothingSeamShift T q)) =
        (fun q => X q + a • V q) := funext hAp
    have hcurv := bandBending_actual_curvature_translation
      (fun q => X q + a • V q) T (![s, (p.2 : ℝ)] : Coord)
    rw [hshift] at hcurv
    simpa only [smoothingSeamShift, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hcurv.symm
  obtain ⟨s, hsp⟩ := QuotientAddGroup.mk_surjective p.1
  have heq := seam_periodic_eq_representative (Fact.out : 0 < T) hperiod s
  have hrepr : (![toIcoMod (Fact.out : 0 < T) 0 s, (p.2 : ℝ)] : Coord) ∈ K := by
    refine ⟨(toIcoMod (Fact.out : 0 < T) 0 s, (p.2 : ℝ)), ⟨?_, hs p hp⟩, rfl⟩
    exact Ico_subset_Icc_self (toIcoMod_mem_Ico' (Fact.out : 0 < T) s)
  have hphysical : gaussianCurvature (inducedMetric (fun q => X q + a • V q))
      (![s, (p.2 : ℝ)] : Coord) < 0 := by
    rw [heq]
    exact hbound a ha _ hrepr
  rw [nativeProductPlane_curvature_of_chart_germ
    (markedRuledBand_native_branch_chart_germ d Y A B C a p s hsp)]
  rw [bandBending_actual_curvature_translation (fun q => X q + a • V q) s]
  simpa only [smoothingSeamShift, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
    using hphysical

/-- Fresh marked stability on the SAME protected image, for both actual
branches B F ± a C Z. The native bending input is an ordinary actual zero-strain
statement; transport supplies it from dual pairing, rather than a curvature grant. -/
theorem protectedTorus_marked_bending_curvature_threshold
    (d : PeriodicRuledFrame T) (hw : 0 < w)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hcompact : HasCompactSupport Y)
    (F : NonrigidTorusSource → Ambient)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e e.source)
    (hi : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (B C : Ambient →L[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A ((d.bandMap (b := w)) p))
    (hX : ContDiff ℝ ∞ (markedRuledBandCoordinateBase d A B))
    (hY : IsInfinitesimalBendingOn (markedRuledBandCoordinateBase d A B)
      (markedRuledBandCoordinateField Y A C) (markedRuledBandCoordinateDomain w))
    (himm : ∀ q ∈ markedRuledBandCoordinateDomain w, Function.Injective
      (fderiv ℝ (markedRuledBandCoordinateBase d A B) q))
    (hneg : ∀ q ∈ markedRuledBandCoordinateDomain w, gaussianCurvature
      (inducedMetric (markedRuledBandCoordinateBase d A B)) q < 0)
    (hG : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (fun q => B (F q)))
    (hGi : ∀ q, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fun r => B (F r)) q))
    (hW : nativeProductIsBending (fun q => B (F q))
      (fun q => C (protectedTorusBendingField e A Y q))) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ q ∈ e '' tsupport Y,
      nativeTorusChartCurvature (fun r => B (F r)) q < 0 ∧
      nativeTorusChartCurvature
        (fun r => B (F r) + a • C (protectedTorusBendingField e A Y r)) q < 0 ∧
      nativeTorusChartCurvature
        (fun r => B (F r) - a • C (protectedTorusBendingField e A Y r)) q < 0 := by
  let G : NonrigidTorusSource → Ambient := fun q => B (F q)
  let W : NonrigidTorusSource → Ambient := fun q => C (protectedTorusBendingField e A Y q)
  obtain ⟨δ, hδ, hbound⟩ := markedRuledBand_native_compact_curvature_threshold
    d hw Y A B C hcompact hX hY himm hneg
  have hbranch (a : ℝ) {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
      (G + a • W) (e p) = markedRuledBandNativeBranch d Y A B C a p := by
    change B (F (e p)) + a • C (protectedTorusBendingField e A Y (e p)) = _
    rw [hplacement p hp, protectedTorusBendingField_source e A Y hp]
    rfl
  have hcompare (a : ℝ) {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
      nativeTorusChartCurvature (G + a • W) (e p) =
        gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
          (markedRuledBandNativeBranch d Y A B C a) p)) (![0, (p.2 : ℝ)] : Coord) := by
    exact nativeTorusChartCurvature_of_band_placement_at_height
      (markedRuledBandNativeBranch d Y A B C a) (G + a • W)
      (hG.add (nativeProduct_bending_const_smul hG hW a).1)
      (nativeProduct_bending_branch_immersion hG hW a hGi)
      e he hi (AffineIsometryEquiv.refl ℝ Ambient) (fun p hp => hbranch a hp) hp
  refine ⟨δ, hδ, ?_⟩
  intro a ha q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hps := hsupport hp
  have hzero : nativeTorusChartCurvature G (e p) < 0 := by
    have hz := (hcompare 0 hps).symm ▸ hbound 0 (by simpa using hδ) p hp
    simpa only [zero_smul, add_zero] using hz
  have hplus : nativeTorusChartCurvature (G + a • W) (e p) < 0 :=
    (hcompare a hps).symm ▸ hbound a ha p hp
  have hminus : nativeTorusChartCurvature (G + (-a) • W) (e p) < 0 :=
    (hcompare (-a) hps).symm ▸ hbound (-a) (by simpa only [abs_neg] using ha) p hp
  refine ⟨hzero, hplus, ?_⟩
  have hminus_eq : (G + (-a) • W) =
      (fun r => B (F r) - a • C (protectedTorusBendingField e A Y r)) := by
    funext r
    change B (F r) + (-a) • C (protectedTorusBendingField e A Y r) =
      B (F r) - a • C (protectedTorusBendingField e A Y r)
    rw [neg_smul, sub_eq_add_neg]
  rw [hminus_eq] at hminus
  exact hminus

end
end TightVer401

