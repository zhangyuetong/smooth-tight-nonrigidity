import TightVer401.SmoothingPeriodicChartExistence
import TightVer401.SmoothingTubeBounds
import TightVer401.SmoothingTubeGerms
import TightVer401.SeamNormalRegularTube

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Complete smoothing on the actual planar normal tube: actual C∞, actual
saddle Hessians, exact physical side germs, and arbitrary uniform physical C¹
error on the compact inner tube. -/
theorem smoothing_periodic_planar_tube_exists {L : ℝ} [hLpos : Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ} (hr : 0 < r)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {F G : Coord → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hPF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hPG : ∀ p, G (smoothingSeamShift L p)=G p)
    (hzero : ∀ s, (F-G) (![s,0])=0)
    (hfirst : ∀ s, coordPartial 1 (F-G) (![s,0])=0)
    (hnegF : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) F p).det < 0)
    (hnegG : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) G p).det < 0)
    {w η : ℝ} (hw : 0 < w) (hη : 0 < η) :
    ∃ H : Coord → ℝ, ∃ hPH : ∀ p, H (smoothingSeamShift L p)=H p,
      ContDiff ℝ ∞ H ∧
      ContDiffOn ℝ ∞ (seamNormalTubePotential γ hL r H hPH) (seamNormalOpenTube γ hL r) ∧
      (∀ x ∈ seamNormalOpenTube γ hL r, (planarHessian (seamNormalTubePotential γ hL r H hPH) x).det < 0) ∧
      (∀ p : Coord, |p 1| < r → p 1 ≤ -w →
        seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)]
          seamNormalTubePotential γ hL r G hPG) ∧
      (∀ p : Coord, |p 1| < r → w ≤ p 1 →
        seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)]
          seamNormalTubePotential γ hL r F hPF) ∧
      (∀ s t : ℝ, |t| ≤ r/2 →
        |seamNormalTubePotential γ hL r H hPH (seamNormalCoordinates γ (![s,t]))-
          seamNormalTubePotential γ hL r (smoothingFlatOriginal F G) (smoothingFlatOriginal_periodic L hPF hPG)
            (seamNormalCoordinates γ (![s,t]))| < η ∧
        ‖planarGradient (seamNormalTubePotential γ hL r H hPH) (seamNormalCoordinates γ (![s,t]))-
          planarGradient (seamNormalTubePotential γ hL r (smoothingFlatOriginal F G)
            (smoothingFlatOriginal_periodic L hPF hPG)) (seamNormalCoordinates γ (![s,t]))‖ < η) := by
  let K := Icc (0 : ℝ) L
  let S : Set Coord := seamCoordProd.symm '' (K ×ˢ Icc (-r/2) (r/2))
  let U : Set Coord := {p | p 0 ∈ K ∧ |p 1| < r}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image seamCoordProd.symm.continuous
  have hSbounds (p : Coord) (hp : p ∈ S) : p 0 ∈ K ∧ |p 1| ≤ r/2 := by
    rcases hp with ⟨⟨s,t⟩,hst,rfl⟩
    refine ⟨hst.1,?_⟩
    change |t| ≤ r/2
    apply abs_le.mpr
    simpa only [mem_Icc,neg_div] using hst.2
  have hSr (p : Coord) (hp : p ∈ S) : |p 1| < r := (hSbounds p hp).2.trans_lt (half_lt_self hr)
  obtain ⟨M,hM,hTransport⟩ := smoothing_tube_compact_gradient_error hγ hL hi hJ hS hSr
  let α := η/(2*M+1)
  have hden : 0 < 2*M+1 := by linarith
  have hα : 0 < α := div_pos hη hden
  have hαeq : α*(2*M+1)=η := by dsimp [α]; exact div_mul_cancel₀ η (ne_of_gt hden)
  have hαη : α < η := by nlinarith
  have hErr : 2*M*α < η := by nlinarith
  obtain ⟨H,hH,hPH,hSaddle,hOld,hNew,hClose⟩ := smoothing_periodic_chart_exists
    (seamNormalCoordinates_contDiff hγ) hF hG hzero hfirst L hPF hPG
    (isCompact_Icc : IsCompact K) hS
    (U := U) (fun p hp => hp.1) (fun s hs => ⟨hs,by simpa using hr⟩)
    (fun s _ => hJ s 0 (by simpa using hr.le))
    (fun p hp => hnegG p hp.2) (fun p hp => hnegF p hp.2) hw hα
  have hAllNeg (s t : ℝ) (ht : |t| < r) :
      (seamCorrectedHessian (seamNormalCoordinates γ) H (![s,t])).det < 0 := by
    have hp : Function.Periodic (fun u : ℝ =>
        (seamCorrectedHessian (seamNormalCoordinates γ) H (![u,t])).det) L := by
      intro u
      exact congrArg Matrix.det (seamCorrectedHessian_periodic (seamNormalCoordinates_contDiff hγ) hH L
        (seamNormalCoordinates_periodic hL) hPH (![u,t]))
    rw [seam_periodic_eq_representative hLpos.out hp s]
    exact hSaddle _ ⟨Ico_subset_Icc_self (toIcoMod_mem_Ico' hLpos.out s),ht⟩
  refine ⟨H,hPH,hH,seamNormalTubePotential_contDiffOn hγ hL hi hJ hH hPH,
    seamNormalTubePotential_saddle hγ hL hi hJ hH hPH hAllNeg,?_,?_,?_⟩
  · intro p hp hwp
    exact seamNormalTubePotential_germ hγ hL hi hJ H G hPH hPG hp (hOld p hwp)
  · intro p hp hwp
    exact seamNormalTubePotential_germ hγ hL hi hJ H F hPH hPF hp (hNew p hwp)
  · intro s t ht
    let u := toIcoMod hLpos.out 0 s
    let p : Coord := (![u,t])
    have hu : u ∈ K := Ico_subset_Icc_self (toIcoMod_mem_Ico' hLpos.out s)
    have hp : p ∈ S := ⟨(u,t),⟨hu,by simpa only [mem_Icc,neg_div] using abs_le.mp ht⟩,rfl⟩
    have hΦPeriod : Function.Periodic (fun v : ℝ => seamNormalCoordinates γ (![v,t])) L :=
      fun v => seamNormalCoordinates_periodic hL (![v,t])
    have hΦEq := seam_periodic_eq_representative hLpos.out hΦPeriod s
    rw [hΦEq]
    have hc := hClose p hp
    have hgrad := hTransport H (smoothingFlatOriginal F G) hPH
      (smoothingFlatOriginal_periodic L hPF hPG) (hH.of_le (by simp))
      (smoothingFlatOriginal_contDiff_one hF hG hzero hfirst) α hα.le
      (fun q hq => (hClose q hq).2.le) p hp
    refine ⟨?_,hgrad.trans_lt hErr⟩
    rw [seamNormalTubePotential_coe hL H hPH hi u t (ht.trans (by linarith)),
      seamNormalTubePotential_coe hL (smoothingFlatOriginal F G) (smoothingFlatOriginal_periodic L hPF hPG)
        hi u t (ht.trans (by linarith))]
    exact hc.1.trans hαη

end
end TightVer401
