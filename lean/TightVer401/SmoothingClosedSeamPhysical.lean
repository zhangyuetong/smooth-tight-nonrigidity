import TightVer401.SmoothingClosedSeamLocal
import TightVer401.SmoothingBranchPullback

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Closed-seam smoothing from actual physical branch data. The actual normal
tube, its Jacobian, the coordinate jets, corrected Hessians, smooth extensions,
periodic descent, and outer boundary matching are all derived. -/
theorem smoothing_closed_seam_physical_exists {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {V U N : Set Coord} (hV : IsOpen V) (hU : IsOpen U) (hN : IsOpen N)
    (hSeamV : seamNormalSeam γ hL ⊆ V) (hSeamU : seamNormalSeam γ hL ⊆ U)
    (hSeamN : seamNormalSeam γ hL ⊆ N) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {f g O : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hValue : ∀ s, f (seamComplexCoord (γ s))=g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s))=planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ U, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ U, (planarHessian g x).det < 0)
    (hO : ContDiffOn ℝ ∞ O (V \ seamNormalSeam γ hL))
    (hnegO : ∀ x ∈ V \ seamNormalSeam γ hL, (planarHessian O x).det < 0)
    (hOriginal : ∀ s t : ℝ, |t| < r₀ → seamNormalCoordinates γ (![s,t]) ∈ U →
      O (seamNormalCoordinates γ (![s,t]))=
        if t ≤ 0 then g (seamNormalCoordinates γ (![s,t])) else f (seamNormalCoordinates γ (![s,t])))
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] O) ∧
      ∀ x ∈ V, |H x-O x| < η ∧ ‖planarGradient H x-planarGradient O x‖ < η := by
  obtain ⟨r₁,hr₁,hi₁,_,hJ₁⟩ := seamNormalNative_exists_regular_embedded_strip hγ hL hreg hEmbed
  obtain ⟨r₂,hr₂,hTube₂⟩ := seamNormalTube_exists_subset_open hγ hL (hU.inter hV)
    (fun x hx => ⟨hSeamU hx,hSeamV hx⟩)
  let r := min r₁ (min r₂ r₀)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₀)
  have hr₁le : r ≤ r₁ := min_le_left _ _
  have hr₂le : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₀le : r ≤ r₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r) := hi₁.mono
    (Set.prod_mono Subset.rfl (Icc_subset_Icc (neg_le_neg hr₁le) hr₁le))
  have hJ (s t : ℝ) (ht : |t| ≤ r) :
      (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0 := hJ₁ s t (ht.trans hr₁le)
  have hTube : seamNormalOpenTube γ hL r ⊆ U ∩ V :=
    (image_mono (Set.prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hr₂le) hr₂le))).trans hTube₂
  have hMap (p : Coord) (hp : |p 1| < r) : seamNormalCoordinates γ p ∈ U :=
    (hTube (seamNormalCoordinates_mem_openTube hL hp)).1
  have hAxis (s : ℝ) : seamNormalCoordinates γ (![s,0]) ∈ U := hMap _ (by simpa using hr)
  let F : Coord → ℝ := fun p => f (seamNormalCoordinates γ p)
  let G : Coord → ℝ := fun p => g (seamNormalCoordinates γ p)
  have hΦ := seamNormalCoordinates_contDiff hγ
  have hF : ContDiffOn ℝ ∞ F {p : Coord | |p 1| < r} := smoothing_branch_pullback_contDiffOn hΦ hf hMap
  have hG : ContDiffOn ℝ ∞ G {p : Coord | |p 1| < r} := smoothing_branch_pullback_contDiffOn hΦ hg hMap
  have hPF (p : Coord) : F (smoothingSeamShift L p)=F p := congrArg f (seamNormalCoordinates_periodic hL p)
  have hPG (p : Coord) : G (smoothingSeamShift L p)=G p := congrArg g (seamNormalCoordinates_periodic hL p)
  have hdf (s : ℝ) : DifferentiableAt ℝ f (seamNormalCoordinates γ (![s,0])) :=
    (hf.contDiffAt (hU.mem_nhds (hAxis s))).differentiableAt (by simp)
  have hdg (s : ℝ) : DifferentiableAt ℝ g (seamNormalCoordinates γ (![s,0])) :=
    (hg.contDiffAt (hU.mem_nhds (hAxis s))).differentiableAt (by simp)
  have hValue' (s : ℝ) : f (seamNormalCoordinates γ (![s,0]))=g (seamNormalCoordinates γ (![s,0])) := by
    rw [seamNormalCoordinates_central]
    exact hValue s
  have hGradient' (s : ℝ) : planarGradient f (seamNormalCoordinates γ (![s,0]))=
      planarGradient g (seamNormalCoordinates γ (![s,0])) := by
    rw [seamNormalCoordinates_central]
    exact hGradient s
  obtain ⟨hz,hfirst⟩ := smoothing_branch_pullback_matching hΦ hdf hdg hValue' hGradient'
  have hjp (p : Coord) (hp : |p 1| < r) : (seamCoordinateJacobian (seamNormalCoordinates γ) p).det ≠ 0 := by
    have hpv : (![p 0,p 1] : Coord)=p := by ext i; fin_cases i <;> rfl
    have he := hJ (p 0) (p 1) hp.le
    simpa only [hpv] using he
  have hnF (p : Coord) (hp : |p 1| < r) : (seamCorrectedHessian (seamNormalCoordinates γ) F p).det < 0 :=
    smoothing_branch_pullback_saddle hΦ hU hf (hMap p hp) (hjp p hp) (hnegf _ (hMap p hp))
  have hnG (p : Coord) (hp : |p 1| < r) : (seamCorrectedHessian (seamNormalCoordinates γ) G p).det < 0 :=
    smoothing_branch_pullback_saddle hΦ hU hg (hMap p hp) (hjp p hp) (hnegg _ (hMap p hp))
  have hMatch (s t : ℝ) (ht : |t| < r) : O (seamNormalCoordinates γ (![s,t]))=smoothingFlatOriginal F G (![s,t]) := by
    change O (seamNormalCoordinates γ (![s,t]))=
      if t ≤ 0 then g (seamNormalCoordinates γ (![s,t])) else f (seamNormalCoordinates γ (![s,t]))
    exact hOriginal s t (ht.trans_le hr₀le) (hMap _ (by simpa using ht))
  exact smoothing_closed_seam_local_exists hγ hL hr hi hJ hV hN
    (fun x hx => (hTube hx).2) hSeamN hF hG hPF hPG hz hfirst hnF hnG hO hnegO hMatch hη

end
end TightVer401
