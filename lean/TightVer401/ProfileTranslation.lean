import TightVer401.RuledBandClassification

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem translated_profile_support {F : ℝ → ℝ} {cb a : ℝ}
    (hF : tsupport F ⊆ Ioi (cb + a)) :
    tsupport (fun c => F (c + a)) ⊆ Ioi cb := by
  intro c hc
  have hca : c + a ∈ tsupport F :=
    tsupport_comp_subset_preimage F (continuous_id.add continuous_const) hc
  have := hF hca
  change cb + a < c + a at this
  exact (add_lt_add_iff_right a).mp this

theorem ruledProfileField_translate {k τ ρ W F : ℝ → ℝ} {T n : ℝ → Ambient}
    (a : ℝ) (p : Coord) :
    ruledProfileField k τ ρ (fun s => W s - a) F T n p =
      ruledProfileField k τ ρ W (fun c => F (c + a)) T n p := by
  have hv : ruledFirstIntegral ρ (fun s => W s - a) p =
      ruledFirstIntegral ρ W p + a := by
    unfold ruledFirstIntegral
    ring
  simp only [ruledProfileField, ruledBending, ruledProfileAlpha, ruledProfileBeta, hv,
    deriv_comp_add_const]

theorem ruled_band_supported_kernel_classification_any_primitive
    {L b cb : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L) {W : ℝ → ℝ}
    (hWL : Function.Periodic W L)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s)
    (hb : 0 < b) (hmax : ∀ s, 1 / (ruledRho d.τ s * b) - W s ≤ cb)
    (hattained : ∃ s, 1 / (ruledRho d.τ s * b) - W s = cb)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hcompact : HasCompactSupport Y) :
    ∃! F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ioi cb ∧
      Y = d.profile (F := F) hWL := by
  let V : ℝ → ℝ := fun s => W s - W 0
  have hVL : Function.Periodic V L := fun s => by simp only [V, hWL s]
  have hV : ∀ s, HasDerivAt V (ruledPeriodCoefficient d.k d.τ s) s :=
    fun s => (hW s).sub_const (W 0)
  have hV0 : V 0 = 0 := sub_self _
  have hm : ∀ s, 1 / (ruledRho d.τ s * b) - V s ≤ cb + W 0 := by
    intro s
    dsimp only [V]
    have := hmax s
    linarith
  have ha : ∃ s, 1 / (ruledRho d.τ s * b) - V s = cb + W 0 := by
    obtain ⟨s, hs⟩ := hattained
    refine ⟨s, ?_⟩
    dsimp only [V]
    linarith
  obtain ⟨G, ⟨hGs, hGc, hGsupport, hYG⟩, _⟩ :=
    ruled_band_supported_kernel_classification d hVL hV hV0 hb hm ha hY hcompact
  let F : ℝ → ℝ := fun c => G (c + W 0)
  have hFs : ContDiff ℝ ∞ F := hGs.comp (contDiff_id.add contDiff_const)
  have hFc : HasCompactSupport F := hGc.comp_homeomorph (Homeomorph.addRight (W 0))
  have hFsupport : tsupport F ⊆ Ioi cb := translated_profile_support hGsupport
  have he : Y = d.profile (F := F) hWL := by
    rw [hYG]
    funext p
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
    have h := ruledProfileField_translate (k := d.k) (τ := d.τ)
      (ρ := ruledRho d.τ) (W := W) (F := G) (T := d.T) (n := d.n)
      (W 0) (![s, (p.2 : ℝ)] : Coord)
    have hv := periodic_bandProfile_real_lift d.period_k d.period_τ
      (ruledRho_periodic d.period_τ) hVL d.period_T d.period_n s p.2 (F := G)
    have hw := periodic_bandProfile_real_lift d.period_k d.period_τ
      (ruledRho_periodic d.period_τ) hWL d.period_T d.period_n s p.2 (F := F)
    have hs' : periodProjection L s = p.1 := hs
    rw [hs'] at hv hw
    exact hv.trans (h.trans hw.symm)
  refine ⟨F, ⟨hFs, hFc, hFsupport, he⟩, ?_⟩
  intro G hG
  exact periodic_bandProfile_injective d.period_k d.period_τ (ruledRho_periodic d.period_τ)
    hWL d.period_T d.period_n (d.orthonormal 0) (d.torsion_ne_zero 0)
    (ruledRho_pos (d.torsion_ne_zero 0)) hb (hmax 0) hG.2.2.1 hFsupport
    (hG.2.2.2.symm.trans he)

end
end TightVer401
