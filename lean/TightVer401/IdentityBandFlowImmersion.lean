import TightVer401.IdentityBandFlowAnnulus

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- The inclusion of the positive open annulus has the identity native derivative. -/
theorem identityFlow_annulus_inclusion_mfderiv {T δ : ℝ} [Fact (0 < T)]
    (p : AddCircle T × Ioo (0 : ℝ) δ) :
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (fun p : AddCircle T × Ioo (0 : ℝ) δ => (p.1, (p.2 : ℝ))) p =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (Prod.map id (Subtype.val : Ioo (0 : ℝ) δ → ℝ)) p = _
  have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (Subtype.val : Ioo (0 : ℝ) δ → ℝ) p.2 = ContinuousLinearMap.id ℝ ℝ :=
    mfderiv_extChartAt_self (I := 𝓘(ℝ, ℝ)) (x := p.2)
  have h := mfderiv_prodMap (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (J := 𝓘(ℝ, ℝ)) (J' := 𝓘(ℝ, ℝ)) (p := p) (f := id) (g := Subtype.val)
    mdifferentiableAt_id
    ((contMDiff_subtype_val (U := bandOpen δ) (n := ∞) p.2).mdifferentiableAt (by simp))
  rw [mfderiv_id, hv] at h
  exact h

/-- The smooth explicit inverse at every image point forces the actual flow
coordinate derivative to be injective. -/
theorem identityFlowCoordinates_immersion {T δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (p : AddCircle T × Ioo (0 : ℝ) δ) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (identityFlowCoordinates d hbalance s) p) := by
  let ρ := (ruledRho_periodic d.period_τ).lift
  let W := (periodicRuledFrame_omega_periodic d hbalance).lift
  let a := ruledRho d.τ s
  let c := fun q => W q - ruledOmega d.k d.τ s
  have hρ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := periodicLift_contMDiff
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) (ruledRho_periodic d.period_τ)
  have hW : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ W := periodicLift_contMDiff
    (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
    (periodicRuledFrame_omega_periodic d hbalance)
  have hρ0 (q) : ρ q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ne_of_gt (ruledRho_pos (d.torsion_ne_zero t))
  have hd (q : AddCircle T) (v : Ioo (0 : ℝ) δ) : 1 + a * (v : ℝ) * c q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hden _ v.property t
  have ha : a ≠ 0 := ne_of_gt (ruledRho_pos (d.torsion_ne_zero s))
  let F := identityFlowCoordinates (δ := δ) d hbalance s
  let g : AddCircle T × ℝ → AddCircle T × ℝ := fun z =>
    (z.1, ρ z.1 * z.2 / (a * (1 - ρ z.1 * z.2 * c z.1)))
  have hformula (v : ℝ) (q : AddCircle T) (hdv : 1 + a * v * c q ≠ 0) :
      1 - ρ q * (a * v / (ρ q * (1 + a * v * c q))) * c q =
      1 / (1 + a * v * c q) := by
    field_simp [hρ0 q, hdv]
    <;> ring
  have hinvden : a * (1 - ρ (F p).1 * (F p).2 * c (F p).1) ≠ 0 := by
    change a * (1 - ρ p.1 * (a * (p.2 : ℝ) /
      (ρ p.1 * (1 + a * (p.2 : ℝ) * c p.1))) * c p.1) ≠ 0
    rw [hformula _ _ (hd _ _)]
    exact mul_ne_zero ha (one_div_ne_zero (hd _ _))
  have hg : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ g (F p) := by
    have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : AddCircle T × ℝ => z.1) := contMDiff_fst
    have hr : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : AddCircle T × ℝ => ρ z.1) (F p) := (hρ.comp hs) (F p)
    have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : AddCircle T × ℝ => c z.1) (F p) :=
      ((hW.sub (contMDiff_const (c := ruledOmega d.k d.τ s))).comp hs) (F p)
    have hu := (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (n := ∞)) (F p)
    apply ((contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (n := ∞)) (F p)).prodMk
    exact (hr.mul hu).div₀
      (contMDiffAt_const.mul (contMDiffAt_const.sub ((hr.mul hu).mul hc))) hinvden
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ F :=
    contMDiff_fst.prodMk (identityFlowHeight_contMDiff d hbalance s hden)
  have he : g ∘ F = fun q : AddCircle T × Ioo (0 : ℝ) δ => (q.1, (q.2 : ℝ)) := by
    funext q
    apply Prod.ext
    · rfl
    · change ρ q.1 * (a * (q.2 : ℝ) / (ρ q.1 * (1 + a * (q.2 : ℝ) * c q.1))) /
        (a * (1 - ρ q.1 * (a * (q.2 : ℝ) /
          (ρ q.1 * (1 + a * (q.2 : ℝ) * c q.1))) * c q.1)) = (q.2 : ℝ)
      rw [hformula _ _ (hd _ _)]
      field_simp [hρ0 q.1, hd q.1 q.2, ha]
  have hchain := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    ((hF p).mdifferentiableAt (by simp))
  rw [he, identityFlow_annulus_inclusion_mfderiv] at hchain
  intro x y hxy
  have h := congrArg (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) g (F p)) hxy
  change ((mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) g (F p)).comp
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) F p)) x =
    ((mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) g (F p)).comp
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) F p)) y at h
  rw [← hchain] at h
  exact h

/-- The actual ambient derivative of the flow annulus is injective, by composing
its coordinate immersion with the already derived ruled-band immersion. -/
theorem identityFlowSurface_immersion {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    (p : AddCircle T × Ioo (0 : ℝ) δ) :
    Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance s) p) := by
  have hheight (q : AddCircle T × Ioo (0 : ℝ) δ) :
      identityFlowHeight d hbalance s q ∈ Ioo 0 w := by
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective q.1
    have hq : (periodProjection T t, q.2) = q := Prod.ext ht rfl
    rw [← hq]
    exact hinside _ q.2.property t
  let f : AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × Ioo (0 : ℝ) w :=
    fun q => (q.1, ⟨identityFlowHeight d hbalance s q, hheight q⟩)
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ f := by
    apply contMDiff_fst.prodMk
    exact (ContMDiff.subtypeVal_comp_iff (bandOpen w) _).mp
      (identityFlowHeight_contMDiff d hbalance s hden)
  let ι : AddCircle T × Ioo (0 : ℝ) w → AddCircle T × ℝ := fun q => (q.1, q.2)
  have hi : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ ι :=
    contMDiff_fst.prodMk ((contMDiff_subtype_val (U := bandOpen w)).comp contMDiff_snd)
  have hc := mfderiv_comp p ((hi (f p)).mdifferentiableAt (by simp))
    ((hf p).mdifferentiableAt (by simp))
  have hfi : Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) f p) := by
    intro x y hxy
    apply identityFlowCoordinates_immersion d hbalance s hden p
    change (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (ι ∘ f) p) x =
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (ι ∘ f) p) y
    rw [hc]
    exact congrArg (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ι (f p)) hxy
  have hx := mfderiv_comp p ((d.bandMap_contMDiff (f p)).mdifferentiableAt (by simp))
    ((hf p).mdifferentiableAt (by simp))
  intro x y hxy
  apply hfi
  apply periodicRuledFrame_bandMap_immersion d (f p)
  change (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (d.bandMap ∘ f) p) x =
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (d.bandMap ∘ f) p) y at hxy
  rw [hx] at hxy
  exact hxy

end
end TightVer401
