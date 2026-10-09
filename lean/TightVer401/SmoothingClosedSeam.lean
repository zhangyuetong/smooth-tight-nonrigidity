import TightVer401.SmoothingPlanarTubeExistence
import TightVer401.SmoothingTubeBoundaryGerms
import TightVer401.SmoothingOuterPatch

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Actual closed-seam smoothing with exact outer germs and arbitrary uniform
physical C¹ approximation. Tubular regularity and boundary gluing are explicit
derived mathematics, not a smoothing package assumed in the hypotheses. -/
theorem smoothing_closed_seam_exists {L : ℝ} [hLpos : Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ} (hr : 0 < r)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {V N : Set Coord} (hV : IsOpen V) (hN : IsOpen N)
    (hBigV : seamNormalOpenTube γ hL r ⊆ V) (hSeamN : seamNormalSeam γ hL ⊆ N)
    {F G O : Coord → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hPF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hPG : ∀ p, G (smoothingSeamShift L p)=G p)
    (hzero : ∀ s, (F-G) (![s,0])=0)
    (hfirst : ∀ s, coordPartial 1 (F-G) (![s,0])=0)
    (hnegF : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) F p).det < 0)
    (hnegG : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) G p).det < 0)
    (hO : ContDiffOn ℝ ∞ O (V \ seamNormalSeam γ hL))
    (hnegO : ∀ x ∈ V \ seamNormalSeam γ hL, (planarHessian O x).det < 0)
    (hMatch : ∀ x ∈ seamNormalOpenTube γ hL r,
      O x=seamNormalTubePotential γ hL r (smoothingFlatOriginal F G) (smoothingFlatOriginal_periodic L hPF hPG) x)
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] O) ∧
      ∀ x ∈ V, |H x-O x| < η ∧ ‖planarGradient H x-planarGradient O x‖ < η := by
  obtain ⟨ρ₀,hρ₀,hNarrowN⟩ := seamNormalTube_exists_subset_open hγ hL hN hSeamN
  let ρ := min (r/4) ρ₀
  have hρ : 0 < ρ := lt_min (by positivity) hρ₀
  have hρr : ρ < r := (min_le_left _ _).trans_lt (by linarith)
  have hρHalf : ρ ≤ r/2 := (min_le_left _ _).trans (by linarith)
  let T := seamNormalOpenTube γ hL ρ
  have hTBig : T ⊆ seamNormalOpenTube γ hL r := by
    apply image_mono
    apply Set.prod_mono Subset.rfl
    exact Ioo_subset_Ioo (by linarith) hρr.le
  have hTN : T ⊆ N := by
    apply Subset.trans _ hNarrowN
    apply image_mono
    apply Set.prod_mono Subset.rfl
    exact Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hT : IsOpen T := seamNormalOpenTube_isOpen hγ hL
    (fun s t ht => hJ s t (ht.trans hρr.le))
  let w := ρ/2
  have hw : 0 < w := half_pos hρ
  have hwρ : w < ρ := half_lt_self hρ
  obtain ⟨Hraw,hPH,hHraw,hP,hSaddle,hOld,hNew,hClose⟩ := smoothing_periodic_planar_tube_exists
    hγ hL hr hi hJ hF hG hPF hPG hzero hfirst hnegF hnegG hw hη
  let P := seamNormalTubePotential γ hL r Hraw hPH
  let Oraw := seamNormalTubePotential γ hL r (smoothingFlatOriginal F G) (smoothingFlatOriginal_periodic L hPF hPG)
  have hBigOpen := seamNormalOpenTube_isOpen hγ hL hJ
  have hOriginal (x : Coord) (hx : x ∈ seamNormalOpenTube γ hL r) : Oraw =ᶠ[𝓝 x] O := by
    filter_upwards [hBigOpen.mem_nhds hx] with y hy
    exact (hMatch y hy).symm
  have hBoundary (x : Coord) (hx : x ∈ V ∩ frontier T) : P =ᶠ[𝓝 x] O := by
    have hg := smoothing_tube_boundary_germ hγ hL hρ hρr hwρ hi hJ hT Hraw F G hPH hPF hPG hOld hNew hx.2
    obtain ⟨s,t,ht,hxEq⟩ := seamNormalOpenTube_frontier_representative hγ hL hT hx.2
    have hxBig : x ∈ seamNormalOpenTube γ hL r := by
      rw [hxEq]
      apply seamNormalCoordinates_mem_openTube hL
      change |t| < r
      rw [ht]
      exact hρr
    exact hg.trans (hOriginal x hxBig)
  have hClosePhysical (x : Coord) (hx : x ∈ V ∩ T) : |P x-O x| < η ∧
      ‖planarGradient P x-planarGradient O x‖ < η := by
    have hg := hOriginal x (hTBig hx.2)
    rw [← hg.eq_of_nhds,← smoothing_planarGradient_germ hg]
    rcases hx.2 with ⟨⟨q,t⟩,hq,rfl⟩
    obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
    change |P (seamNormalNative γ hL (periodProjection L s,t))-
      Oraw (seamNormalNative γ hL (periodProjection L s,t))| < η ∧
      ‖planarGradient P (seamNormalNative γ hL (periodProjection L s,t))-
        planarGradient Oraw (seamNormalNative γ hL (periodProjection L s,t))‖ < η
    rw [seamNormalNative_coe]
    exact hClose s t ((abs_lt.mpr hq.2).le.trans hρHalf)
  obtain ⟨hSmooth,hNegative,hGerms,hError⟩ := smoothingOpenPatch_properties hV hT
    (seamNormalSeam_isClosed hγ hL) (seamNormalSeam_subset_openTube hL hρ)
    (hP.mono hTBig) hO hBoundary (fun x hx => hSaddle x (hTBig hx.2)) hnegO hη hClosePhysical
  refine ⟨smoothingOpenPatch T P O,hSmooth,hNegative,?_,hError⟩
  intro x hx
  exact hGerms x ⟨hx.1,fun ht => hx.2 (hTN ht)⟩

end
end TightVer401
