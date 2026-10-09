import TightVer401.SmoothingClosedSeam
import TightVer401.SmoothingNormalExtension

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The closed-seam result needs smooth branch data only on the actual collar. -/
theorem smoothing_closed_seam_local_exists {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ} (hr : 0 < r)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {V N : Set Coord} (hV : IsOpen V) (hN : IsOpen N)
    (hBigV : seamNormalOpenTube γ hL r ⊆ V) (hSeamN : seamNormalSeam γ hL ⊆ N)
    {F G O : Coord → ℝ}
    (hF : ContDiffOn ℝ ∞ F {p : Coord | |p 1| < r})
    (hG : ContDiffOn ℝ ∞ G {p : Coord | |p 1| < r})
    (hPF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hPG : ∀ p, G (smoothingSeamShift L p)=G p)
    (hzero : ∀ s, (F-G) (![s,0])=0)
    (hfirst : ∀ s, coordPartial 1 (F-G) (![s,0])=0)
    (hnegF : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) F p).det < 0)
    (hnegG : ∀ p : Coord, |p 1| < r → (seamCorrectedHessian (seamNormalCoordinates γ) G p).det < 0)
    (hO : ContDiffOn ℝ ∞ O (V \ seamNormalSeam γ hL))
    (hnegO : ∀ x ∈ V \ seamNormalSeam γ hL, (planarHessian O x).det < 0)
    (hMatch : ∀ s t : ℝ, |t| < r → O (seamNormalCoordinates γ (![s,t]))=smoothingFlatOriginal F G (![s,t]))
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] O) ∧
      ∀ x ∈ V, |H x-O x| < η ∧ ‖planarGradient H x-planarGradient O x‖ < η := by
  let F' := smoothingNormalExtension r hr F
  let G' := smoothingNormalExtension r hr G
  let r' := r/8
  have hr' : 0 < r' := by dsimp [r']; positivity
  have hrr : r' < r := by dsimp [r']; linarith
  have hrQuarter : r' < r/4 := by dsimp [r']; linarith
  have hF' : ContDiff ℝ ∞ F' := smoothingNormalExtension_contDiff r hr hF
  have hG' : ContDiff ℝ ∞ G' := smoothingNormalExtension_contDiff r hr hG
  have hgF (p : Coord) (hp : |p 1| < r/4) : F' =ᶠ[𝓝 p] F := smoothingNormalExtension_germ r hr F hp
  have hgG (p : Coord) (hp : |p 1| < r/4) : G' =ᶠ[𝓝 p] G := smoothingNormalExtension_germ r hr G hp
  have hgD (s : ℝ) : F'-G' =ᶠ[𝓝 (![s,0] : Coord)] F-G := by
    have ht : |(![s,0] : Coord) 1| < r/4 := by simp; positivity
    filter_upwards [hgF _ ht,hgG _ ht] with p hpF hpG
    change F' p-G' p=F p-G p
    rw [hpF,hpG]
  have hz' (s : ℝ) : (F'-G') (![s,0])=0 := by rw [(hgD s).eq_of_nhds]; exact hzero s
  have hf' (s : ℝ) : coordPartial 1 (F'-G') (![s,0])=0 := by
    unfold coordPartial
    rw [(hgD s).fderiv_eq]
    exact hfirst s
  have hnF' (p : Coord) (hp : |p 1| < r') : (seamCorrectedHessian (seamNormalCoordinates γ) F' p).det < 0 := by
    rw [smoothing_correctedHessian_germ (seamNormalCoordinates γ) (hgF p (hp.trans hrQuarter))]
    exact hnegF p (hp.trans hrr)
  have hnG' (p : Coord) (hp : |p 1| < r') : (seamCorrectedHessian (seamNormalCoordinates γ) G' p).det < 0 := by
    rw [smoothing_correctedHessian_germ (seamNormalCoordinates γ) (hgG p (hp.trans hrQuarter))]
    exact hnegG p (hp.trans hrr)
  have hi' : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r') r') := by
    apply hi.mono
    exact Set.prod_mono Subset.rfl (Icc_subset_Icc (neg_le_neg hrr.le) hrr.le)
  have hBig' : seamNormalOpenTube γ hL r' ⊆ V := by
    apply Subset.trans _ hBigV
    exact image_mono (Set.prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hrr.le) hrr.le))
  have hMatch' (x : Coord) (hx : x ∈ seamNormalOpenTube γ hL r') :
      O x=seamNormalTubePotential γ hL r' (smoothingFlatOriginal F' G')
        (smoothingFlatOriginal_periodic L (smoothingNormalExtension_periodic r hr L hPF)
          (smoothingNormalExtension_periodic r hr L hPG)) x := by
    rcases hx with ⟨⟨q,t⟩,hq,rfl⟩
    obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
    change O (seamNormalNative γ hL (periodProjection L s,t))=
      seamNormalTubePotential γ hL r' (smoothingFlatOriginal F' G') _
        (seamNormalNative γ hL (periodProjection L s,t))
    simp only [seamNormalNative_coe]
    rw [seamNormalTubePotential_coe hL _ _ hi' s t (abs_lt.mpr hq.2).le]
    rw [hMatch s t ((abs_lt.mpr hq.2).trans hrr)]
    have hp : |(![s,t] : Coord) 1| < r/4 := by simpa using (abs_lt.mpr hq.2).trans hrQuarter
    exact (smoothingFlatOriginal_germ (hgF _ hp) (hgG _ hp)).eq_of_nhds.symm
  exact smoothing_closed_seam_exists hγ hL hr' hi'
    (fun s t ht => hJ s t (ht.trans hrr.le)) hV hN hBig' hSeamN hF' hG'
    (smoothingNormalExtension_periodic r hr L hPF) (smoothingNormalExtension_periodic r hr L hPG)
    hz' hf' hnF' hnG' hO hnegO hMatch' hη

end
end TightVer401
