import TightVer401.IdentityBandPlanarSupportSaddle
import TightVer401.IdentityBandPlanarSupportImage
import TightVer401.IdentityBandPlanarSupportCoordinates

/-! Whole-image negative Hessian determinant for the actual reconstructed
protected-band potential, using genuine nonlinear derivative correspondence. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Every representative on the actual open Gauss-coordinate image has a
negative Cartesian Hessian determinant. No intrinsic curvature transport or
Hessian/sign/rank/inverse package is supplied. -/
theorem identityBandPlanarSupport_hessian_det_neg_on_image {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hUr : U = range (identityBandPlanarSource (d.bandSphereGauss (b := w))))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hrec : ∀ p : AddCircle T × Ioo (0 : ℝ) w,
      planarSupportMap G (identityBandPlanarSource d.bandSphereGauss p) = d.bandMap p) :
    ∀ q ∈ U, (planarHessian G q).det < 0 := by
  let V : Set Coord := {q | q 1 ∈ Ioo (0 : ℝ) w}
  let P : Coord → Coord := fun q => gnomonicInverse (d.rawGaussMap q)
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply 1)
  have hpdata (q : Coord) (hq : q ∈ V) :
      ∃ p : AddCircle T × Ioo (0 : ℝ) w,
        identityBandPlanarSource d.bandSphereGauss p = P q ∧
        d.bandMap p = ruledMap d.γ d.E q ∧ d.bandGaussMap p = d.rawGaussMap q := by
    let p : AddCircle T × Ioo (0 : ℝ) w := (periodProjection T (q 0), ⟨q 1, hq⟩)
    refine ⟨p, ?_, ?_, ?_⟩ <;>
      simp only [p, P, identityBandPlanarSource, PeriodicRuledFrame.bandSphereGauss,
        PeriodicRuledFrame.bandGaussMap, PeriodicRuledFrame.bandMap,
        PeriodicRuledFrame.fullBandMap, PeriodicRuledFrame.fullGaussMap,
        PeriodicRuledFrame.rawGaussMap, ruledMap, periodicLift_coe]
  have hnraw (q : Coord) (hq : q ∈ V) : 0 < d.rawGaussMap q 2 := by
    obtain ⟨p, _, _, hnp⟩ := hpdata q hq
    rw [← hnp]
    exact hnorth p
  have hP : ContDiffOn ℝ ∞ P V := by
    apply contDiffOn_pi.mpr
    intro i
    have hd (j : Fin 3) : ContDiff ℝ ∞ (fun q => d.rawGaussMap q j) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
        (periodicRuledFrame_rawGaussMap_contDiff d)
    have hcdiv := (hd (Fin.castSucc i)).contDiffOn.div (hd 2).contDiffOn
      (fun q hq => (hnraw q hq).ne')
    fin_cases i <;> exact hcdiv
  have hPU : MapsTo P V U := by
    intro q hq
    obtain ⟨p, hp, _, _⟩ := hpdata q hq
    rw [hUr, ← hp]
    exact mem_range_self p
  have hrawrec : EqOn (planarSupportMap G ∘ P) (ruledMap d.γ d.E) V := by
    intro q hq
    obtain ⟨p, hp, hxp, _⟩ := hpdata q hq
    change planarSupportMap G (P q) = ruledMap d.γ d.E q
    rw [← hp, hrec p, hxp]
  have hnorm : EqOn (planarUnitNormal ∘ P) d.rawGaussMap V := by
    intro q hq
    obtain ⟨p, _, _, hnp⟩ := hpdata q hq
    change planarUnitNormal (gnomonicInverse (d.rawGaussMap q)) = d.rawGaussMap q
    apply identityBand_gnomonic_unitNormal
    · rw [← hnp]
      exact periodicRuledFrame_fullGaussMap_unit d (p.1, (p.2 : ℝ))
    · exact hnraw q hq
  intro q hq
  rw [hUr] at hq
  obtain ⟨p, hp⟩ := hq
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let r : Coord := ![s, (p.2 : ℝ)]
  have hr : r ∈ V := p.2.property
  have hpr : P r = q := by
    rw [← hp]
    change gnomonicInverse (d.rawGaussMap r) =
      gnomonicInverse (d.fullGaussMap (p.1, (p.2 : ℝ)))
    rw [← hs]
    simp only [r, PeriodicRuledFrame.rawGaussMap, PeriodicRuledFrame.fullGaussMap,
      Function.Periodic.lift_coe, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsign := identityBandPlanarSupport_saddle_of_raw_reconstruction d hG hU hV hP hPU hrawrec hnorm hr
  simpa only [hpr] using hsign

end
end TightVer401