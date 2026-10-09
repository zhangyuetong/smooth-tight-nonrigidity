import TightVer401.RelativeSaddlePiecewise
import TightVer401.RelativeSaddleJets
import TightVer401.RelativeSaddleErrorControl
import TightVer401.RelativeSaddleCollar
import TightVer401.RelativeSaddleExteriorDomains

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Relative saddle smoothing from ordinary geometric two-sided data. The
piecewise exterior, its smoothness and saddle sign, the regular embedded tube,
the periodic pullbacks and the corrected Hessians are all constructed or
derived. The analytic construction is the retained normal-profile proof chain.
No smoothing result is a hypothesis. -/
theorem exists_relative_saddle_smoothing_of_matching_jets
    {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {V N P : Set Coord} (hV : IsOpen V) (hN : IsOpen N)
    (hSeamV : seamNormalSeam γ hL ⊆ V)
    (hSeamN : seamNormalSeam γ hL ⊆ N)
    (hBoundary : V ∩ frontier P ⊆ seamNormalSeam γ hL)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hSide : ∀ s t : ℝ, |t| < r₀ → t ≠ 0 →
      seamNormalCoordinates γ (![s,t]) ∈ V →
      (seamNormalCoordinates γ (![s,t]) ∈ P ↔ 0 < t))
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    (hValue : ∀ s, f (seamComplexCoord (γ s)) = g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ V, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ V, (planarHessian g x).det < 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] relativeSaddlePiecewise P f g) ∧
      ∀ x ∈ V, |H x - relativeSaddlePiecewise P f g x| < η ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise P f g) x‖ < η := by
  classical
  obtain ⟨hO,hnegO⟩ := relativeSaddlePiecewise_exterior hV hBoundary hf hg hnegf hnegg
  have hOriginal (s t : ℝ) (ht : |t| < r₀)
      (hx : seamNormalCoordinates γ (![s,t]) ∈ V) :
      relativeSaddlePiecewise P f g (seamNormalCoordinates γ (![s,t])) =
        if t ≤ 0 then g (seamNormalCoordinates γ (![s,t]))
          else f (seamNormalCoordinates γ (![s,t])) := by
    by_cases hz : t = 0
    · subst t
      rw [seamNormalCoordinates_central]
      simp only [relativeSaddlePiecewise, le_refl, ite_true]
      split_ifs with hp
      · exact hValue s
      · rfl
    · have hs := hSide s t ht hz hx
      simp only [relativeSaddlePiecewise, hs]
      by_cases hp : 0 < t
      · simp [hp, not_le.mpr hp]
      · simp [hp, le_of_not_gt hp]
  exact smoothing_closed_seam_physical_exists hγ hL hreg hEmbed hV hV hN
    hSeamV hSeamV hSeamN hr₀ hf hg hValue hGradient hnegf hnegg hO hnegO
    hOriginal hη

/-- The ver500 positive-seam interface. Positivity is the manuscript's sufficient
condition; the retained construction proves the stronger matching-jet result
above, because the determinant is affine in the only varying normal entry. -/
theorem exists_relative_saddle_smoothing
    {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {V N P : Set Coord} (hV : IsOpen V) (hN : IsOpen N)
    (hSeamV : seamNormalSeam γ hL ⊆ V)
    (hSeamN : seamNormalSeam γ hL ⊆ N)
    (hBoundary : V ∩ frontier P ⊆ seamNormalSeam γ hL)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hSide : ∀ s t : ℝ, |t| < r₀ → t ≠ 0 →
      seamNormalCoordinates γ (![s,t]) ∈ V →
      (seamNormalCoordinates γ (![s,t]) ∈ P ↔ 0 < t))
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    (hValue : ∀ s, f (seamComplexCoord (γ s)) = g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ V, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ V, (planarHessian g x).det < 0)
    (_hTangential : ∀ s, 0 < seamFramedHessian f (seamComplexCoord (γ s))
      (seamComplexCoord (deriv γ s)) (seamComplexCoord (Complex.I * deriv γ s)) 0 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] relativeSaddlePiecewise P f g) ∧
      ∀ x ∈ V, |H x - relativeSaddlePiecewise P f g x| < η ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise P f g) x‖ < η := by
  exact exists_relative_saddle_smoothing_of_matching_jets hγ hL hreg hEmbed hV hN
    hSeamV hSeamN hBoundary hr₀ hSide hf hg hValue hGradient hnegf hnegg hη

/-- Global two-sided smoothing without requiring either old branch to extend
smoothly across the whole exterior domain. Only their actual open domains and
which branch is used on each side are supplied; the common seam neighborhood
and the piecewise exterior regularity are derived. -/
theorem exists_relative_saddle_smoothing_on_sides
    {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {V N P Uf Ug : Set Coord}
    (hV : IsOpen V) (hN : IsOpen N) (hUf : IsOpen Uf) (hUg : IsOpen Ug)
    (hSeamV : seamNormalSeam γ hL ⊆ V)
    (hSeamN : seamNormalSeam γ hL ⊆ N)
    (hSeamUf : seamNormalSeam γ hL ⊆ Uf)
    (hSeamUg : seamNormalSeam γ hL ⊆ Ug)
    (hBoundary : V ∩ frontier P ⊆ seamNormalSeam γ hL)
    (hPositiveDomain : V ∩ interior P ⊆ Uf)
    (hNegativeDomain : V ∩ interior Pᶜ ⊆ Ug)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hSide : ∀ s t : ℝ, |t| < r₀ → t ≠ 0 →
      seamNormalCoordinates γ (![s,t]) ∈ V →
      (seamNormalCoordinates γ (![s,t]) ∈ P ↔ 0 < t))
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f Uf) (hg : ContDiffOn ℝ ∞ g Ug)
    (hValue : ∀ s, f (seamComplexCoord (γ s)) = g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ Uf, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ Ug, (planarHessian g x).det < 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H V ∧
      (∀ x ∈ V, (planarHessian H x).det < 0) ∧
      (∀ x ∈ V \ N, H =ᶠ[𝓝 x] relativeSaddlePiecewise P f g) ∧
      (∀ x ∈ (V \ N) ∩ interior P, H =ᶠ[𝓝 x] f) ∧
      (∀ x ∈ (V \ N) ∩ interior Pᶜ, H =ᶠ[𝓝 x] g) ∧
      ∀ x ∈ V, |H x - relativeSaddlePiecewise P f g x| < η ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise P f g) x‖ < η := by
  classical
  let U := (Uf ∩ Ug) ∩ V
  have hU : IsOpen U := (hUf.inter hUg).inter hV
  have hSeamU : seamNormalSeam γ hL ⊆ U := fun x hx =>
    ⟨⟨hSeamUf hx,hSeamUg hx⟩,hSeamV hx⟩
  obtain ⟨hO,hnegO⟩ := relativeSaddlePiecewise_exterior_domains hV hBoundary hUf hUg
    hPositiveDomain hNegativeDomain hf hg hnegf hnegg
  have hOriginal (s t : ℝ) (ht : |t| < r₀)
      (hx : seamNormalCoordinates γ (![s,t]) ∈ U) :
      relativeSaddlePiecewise P f g (seamNormalCoordinates γ (![s,t])) =
        if t ≤ 0 then g (seamNormalCoordinates γ (![s,t]))
          else f (seamNormalCoordinates γ (![s,t])) := by
    by_cases hz : t = 0
    · subst t
      rw [seamNormalCoordinates_central]
      simp only [relativeSaddlePiecewise, le_refl, ite_true]
      split_ifs with hp
      · exact hValue s
      · rfl
    · have hs := hSide s t ht hz hx.2
      simp only [relativeSaddlePiecewise, hs]
      by_cases hp : 0 < t
      · simp [hp, not_le.mpr hp]
      · simp [hp, le_of_not_gt hp]
  obtain ⟨H,hH,hNeg,hOld,hClose⟩ := smoothing_closed_seam_physical_exists
    hγ hL hreg hEmbed hV hU hN hSeamV hSeamU hSeamN hr₀
    (hf.mono (fun x hx => hx.1.1)) (hg.mono (fun x hx => hx.1.2)) hValue hGradient
    (fun x hx => hnegf x hx.1.1) (fun x hx => hnegg x hx.1.2) hO hnegO hOriginal hη
  refine ⟨H,hH,hNeg,hOld,?_,?_,hClose⟩
  · intro x hx
    exact (hOld x hx.1).trans (relativeSaddlePiecewise_germ_interior hx.2)
  · intro x hx
    exact (hOld x hx.1).trans (relativeSaddlePiecewise_germ_interior_compl hx.2)

/-- Seam-only geometric input also suffices: construct the actual open collar
and its two sides, derive a uniform saddle neighborhood by continuity, and
smooth in any prescribed smaller seam neighborhood. No partition, tube,
Jacobian, exterior potential or exterior smoothness premise is supplied. -/
theorem exists_relative_saddle_smoothing_in_collar
    {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {U N : Set Coord} (hU : IsOpen U) (hN : IsOpen N)
    (hSeamU : seamNormalSeam γ hL ⊆ U)
    (hSeamN : seamNormalSeam γ hL ⊆ N)
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hValue : ∀ s, f (seamComplexCoord (γ s)) = g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ seamNormalSeam γ hL, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ seamNormalSeam γ hL, (planarHessian g x).det < 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, IsOpen (seamNormalOpenTube γ hL r) ∧
      seamNormalOpenTube γ hL r ⊆ U ∧
      ∃ H : Coord → ℝ,
        ContDiffOn ℝ ∞ H (seamNormalOpenTube γ hL r) ∧
        (∀ x ∈ seamNormalOpenTube γ hL r, (planarHessian H x).det < 0) ∧
        (∀ x ∈ seamNormalOpenTube γ hL r \ N,
          H =ᶠ[𝓝 x] relativeSaddlePiecewise (relativeSaddleTubeSide γ hL r) f g) ∧
        ∀ x ∈ seamNormalOpenTube γ hL r,
          |H x - relativeSaddlePiecewise (relativeSaddleTubeSide γ hL r) f g x| < η ∧
          ‖planarGradient H x -
            planarGradient (relativeSaddlePiecewise (relativeSaddleTubeSide γ hL r) f g) x‖ < η := by
  let Uf : Set Coord := U ∩ (fun x => (planarHessian f x).det) ⁻¹' Iio 0
  let Ug : Set Coord := U ∩ (fun x => (planarHessian g x).det) ⁻¹' Iio 0
  let W := Uf ∩ Ug
  have hUf : IsOpen Uf :=
    (planarHessian_det_contDiffOn hf hU).continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hUg : IsOpen Ug :=
    (planarHessian_det_contDiffOn hg hU).continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hW : IsOpen W := hUf.inter hUg
  have hWU : W ⊆ U := fun x hx => hx.1.1
  have hSeamW : seamNormalSeam γ hL ⊆ W := fun x hx =>
    ⟨⟨hSeamU hx,hnegf x hx⟩,⟨hSeamU hx,hnegg x hx⟩⟩
  obtain ⟨r,hr,hi,hJ,hV,hVW⟩ := relativeSaddleSeam_exists_collar hγ hL hreg hEmbed hW hSeamW
  let V := seamNormalOpenTube γ hL r
  let P := relativeSaddleTubeSide γ hL r
  have hVU : V ⊆ U := hVW.trans hWU
  have hSide (s t : ℝ) (ht : |t| < r) (_hz : t ≠ 0)
      (_hx : seamNormalCoordinates γ (![s,t]) ∈ V) :
      seamNormalCoordinates γ (![s,t]) ∈ P ↔ 0 < t := by
    change 0 < relativeSaddleNormalParameter γ hL r (seamNormalCoordinates γ (![s,t])) ↔ 0 < t
    rw [relativeSaddleNormalParameter_coe hL hi s t ht.le]
  obtain ⟨H,hH,hNeg,hOld,hClose⟩ := exists_relative_saddle_smoothing_of_matching_jets
    hγ hL hreg hEmbed hV hN (seamNormalSeam_subset_openTube hL hr) hSeamN
    (relativeSaddleTubeSide_boundary hγ hL hi hJ) hr hSide (hf.mono hVU) (hg.mono hVU)
    hValue hGradient (fun x hx => (hVW hx).1.2) (fun x hx => (hVW hx).2.2) hη
  exact ⟨r,hr,hV,hVU,H,hH,hNeg,hOld,hClose⟩

end
end TightVer401
