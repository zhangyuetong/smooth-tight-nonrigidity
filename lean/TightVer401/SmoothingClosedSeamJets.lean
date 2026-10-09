import TightVer401.SmoothingClosedSeamPhysical

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Closed-seam smoothing from actual physical branch data. The actual normal
tube, its Jacobian, the coordinate jets, corrected Hessians, smooth extensions,
periodic descent, and outer boundary matching are all derived. -/
theorem smoothing_closed_seam_matching_jets {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {V U N : Set Coord} (hV : IsOpen V) (hU : IsOpen U) (hN : IsOpen N)
    (hSeamV : seamNormalSeam γ hL ⊆ V) (hSeamU : seamNormalSeam γ hL ⊆ U)
    (hSeamN : seamNormalSeam γ hL ⊆ N) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {f g O : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hValue : ∀ s, f (seamComplexCoord (γ s))=g (seamComplexCoord (γ s)))
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s))=planarGradient g (seamComplexCoord (γ s)))
    (hnegf : ∀ x ∈ seamNormalSeam γ hL, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ seamNormalSeam γ hL, (planarHessian g x).det < 0)
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
  let Uf : Set Coord := U ∩ (fun x => (planarHessian f x).det) ⁻¹' Iio 0
  let Ug : Set Coord := U ∩ (fun x => (planarHessian g x).det) ⁻¹' Iio 0
  let W := Uf ∩ Ug
  have hUf : IsOpen Uf := (planarHessian_det_contDiffOn hf hU).continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hUg : IsOpen Ug := (planarHessian_det_contDiffOn hg hU).continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hW : IsOpen W := hUf.inter hUg
  have hWU : W ⊆ U := fun x hx => hx.1.1
  have hSeamW : seamNormalSeam γ hL ⊆ W := fun x hx =>
    ⟨⟨hSeamU hx,hnegf x hx⟩,⟨hSeamU hx,hnegg x hx⟩⟩
  exact smoothing_closed_seam_physical_exists hγ hL hreg hEmbed hV hW hN hSeamV hSeamW hSeamN hr₀
    (hf.mono hWU) (hg.mono hWU) hValue hGradient
    (fun x hx => hx.1.2) (fun x hx => hx.2.2) hO hnegO
    (fun s t ht hx => hOriginal s t ht (hWU hx)) hη

end
end TightVer401
