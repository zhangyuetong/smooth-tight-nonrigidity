import TightVer401.VisibleConnectorSourceInverseNativeChartsComposition
import TightVer401.VisibleConnectorSourceInverseApplication

/-! Ordinary raw data construct the actual source inverse first, then the
native open/closed charts. Literal positive phases retain the physical period. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
set_option backward.isDefEq.respectTransparency false

theorem visibleConnectorSourceInverseNativeRawSource_actual
    (L : ℝ) [hL : Fact (0 < L)] {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (q : Coord) (hq : 0 < 1 + q 1) :
    visibleConnectorSourceInverseNativeRawSource L (visibleConnectorCartesianSource L p w h) q =
      p (q 0) + (q 1 * h (q 0)) • w (q 0) := by
  have hClock : visibleConnectorPhysicalParameter L (2 * Real.pi * q 0 / L) = q 0 := by
    unfold visibleConnectorPhysicalParameter
    field_simp [hL.out.ne', Real.two_pi_pos.ne']
  unfold visibleConnectorSourceInverseNativeRawSource
  rw [visibleConnectorCartesianSource_polar hpL hwL hhL hq]
  simp only [visibleConnectorPolarSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    hClock, add_sub_cancel_left]

/-- All native source chart fields are outputs of ordinary raw data. The
previous source inverse is constructed internally, rather than assumed. -/
theorem visibleConnectorSourceInverse_native_charts_of_raw
    (L : ℝ) [hL : Fact (0 < L)] {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (hpos : ∀ s, 0 < h s) (gamma : ℝ → Coord)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) →
      0 < visibleConnectorDelta p gamma w q)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (p (L * t) + h (L * t) • w (L * t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm (p (L * t))))
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    ∃ (P : OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) 1) Coord)
      (HN : (AddCircle L × Icc (0 : ℝ) 1) ≃ₜ
        ↥(closure (annularCoordJordanInterior Ho Hi))),
      Continuous (visibleConnectorSourceInverseNativeSource L (visibleConnectorCartesianSource L p w h)) ∧
      (∀ s (t : Icc (0 : ℝ) 1),
        visibleConnectorSourceInverseNativeSource L (visibleConnectorCartesianSource L p w h)
          (periodProjection L s, t) = p s + ((t : ℝ) * h s) • w s) ∧
      (∀ z, (HN z : Coord) =
        visibleConnectorSourceInverseNativeSource L (visibleConnectorCartesianSource L p w h) z) ∧
      P.source = univ ∧ P.target = annularCoordJordanInterior Ho Hi ∧
      (∀ z, P z = visibleConnectorSourceInverseNativeSource L (visibleConnectorCartesianSource L p w h)
        (z.1, ⟨(z.2 : ℝ), ⟨z.2.property.1.le, z.2.property.2.le⟩⟩)) ∧
      ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ P ∧
      ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ P.symm
        (annularCoordJordanInterior Ho Hi) := by
  obtain ⟨e0, E, H, he0S, he0T, he0F, hi0, hH, _hImage, _hKSource,
    _hSourcePositive, _hSourceSmooth, _hJac, _hE, _hi, _hBandTarget, _hAgree⟩ :=
    visibleConnectorSourceInverseApplication_global hL.out hp hw hh hpL hwL hhL hpos gamma
      hDelta hOuter hInner hNested
  have hSmooth := visibleConnectorSourceInverse_cartesian_smooth hp hw hh hpL hwL hhL
  have hRoundSmooth : ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h)
      {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} :=
    hSmooth.mono (fun _ hz => lt_trans zero_lt_one hz.1)
  obtain ⟨P, HN, hCont, hRepresentative, hHN, hPS, hPT, hPActual, hP, hPI⟩ :=
    visibleConnectorSourceInverse_native_charts_of_actual_inverse L hNested hRoundSmooth
      e0 he0S he0T he0F hi0 H hH
  refine ⟨P, HN, hCont, ?_, hHN, hPS, hPT, hPActual, hP, hPI⟩
  intro s t
  rw [hRepresentative, visibleConnectorSourceInverseNativeRawSource_actual L hpL hwL hhL
    ![s, (t : ℝ)] (by change 0 < 1 + (t : ℝ); linarith [t.property.1])]
  rfl

end
end TightVer401
