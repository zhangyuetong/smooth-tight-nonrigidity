import TightVer401.IdentityBandGlobalFlow

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- The height of an actual periodic principal trajectory in quotient coordinates. -/
def identityFlowHeight {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ) :
    AddCircle T × Ioo (0 : ℝ) δ → ℝ := fun p =>
  ruledRho d.τ s * (p.2 : ℝ) /
    ((ruledRho_periodic d.period_τ).lift p.1 *
      (1 + ruledRho d.τ s * (p.2 : ℝ) *
        ((periodicRuledFrame_omega_periodic d hbalance).lift p.1 - ruledOmega d.k d.τ s)))

def identityFlowCoordinates {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ) :
    AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × ℝ :=
  fun p => (p.1, identityFlowHeight d hbalance s p)

theorem identityFlowHeight_real_lift {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (s t : ℝ) (v : Ioo (0 : ℝ) δ) :
    identityFlowHeight d hbalance s (periodProjection T t, v) =
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t := by
  rfl

theorem identityFlowHeight_contMDiff {T δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (identityFlowHeight (δ := δ) d hbalance s) := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle T × Ioo (0 : ℝ) δ => p.1) := contMDiff_fst
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle T × Ioo (0 : ℝ) δ => (p.2 : ℝ)) :=
    (contMDiff_subtype_val (U := bandOpen δ)).comp contMDiff_snd
  have hρ := (periodicLift_contMDiff
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero)
    (ruledRho_periodic d.period_τ)).comp hs
  have hW := (periodicLift_contMDiff
    (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
    (periodicRuledFrame_omega_periodic d hbalance)).comp hs
  apply (contMDiff_const.mul hv).div₀
    (hρ.mul (contMDiff_const.add ((contMDiff_const.mul hv).mul (hW.sub contMDiff_const))))
  intro p
  change (ruledRho_periodic d.period_τ).lift p.1 *
    (1 + ruledRho d.τ s * (p.2 : ℝ) *
      ((periodicRuledFrame_omega_periodic d hbalance).lift p.1 - ruledOmega d.k d.τ s)) ≠ 0
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
  rw [← ht]
  change ruledRho d.τ t *
    (1 + ruledRho d.τ s * (p.2 : ℝ) * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s)) ≠ 0
  exact mul_ne_zero (ne_of_gt (ruledRho_pos (d.torsion_ne_zero t))) (hden _ p.2.property t)

/-- Different initial values cannot meet on the same transverse section. -/
theorem principalTrajectory_initialValue_injective {ρ W : ℝ → ℝ} {s t : ℝ}
    (hρs : ρ s ≠ 0) (hρt : ρ t ≠ 0) {v z : ℝ}
    (hv : 1 + ρ s * v * (W t - W s) ≠ 0)
    (hz : 1 + ρ s * z * (W t - W s) ≠ 0)
    (he : principalTrajectory ρ W s v t = principalTrajectory ρ W s z t) : v = z := by
  have h := (div_eq_div_iff (mul_ne_zero hρt hv) (mul_ne_zero hρt hz)).mp he
  have hmul : ρ s * ρ t * (v - z) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hρs hρt))

theorem identityFlowCoordinates_injective {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0) :
    Function.Injective (identityFlowCoordinates (δ := δ) d hbalance s) := by
  rintro ⟨q, v⟩ ⟨q', z⟩ he
  have hq := congrArg Prod.fst he
  change q = q' at hq
  subst q'
  have hu := congrArg Prod.snd he
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hvz : (v : ℝ) = (z : ℝ) := principalTrajectory_initialValue_injective
    (ne_of_gt (ruledRho_pos (d.torsion_ne_zero s)))
    (ne_of_gt (ruledRho_pos (d.torsion_ne_zero t)))
    (hden _ v.property t) (hden _ z.property t) hu
  exact Prod.ext rfl (Subtype.ext hvz)

/-- The actual surface annulus swept by the closed asymptotic leaves. -/
def identityFlowSurface {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ) :
    AddCircle T × Ioo (0 : ℝ) δ → Ambient := fun p =>
  d.period_γ.lift p.1 + identityFlowHeight d hbalance s p • d.period_E.lift p.1

theorem identityFlowSurface_contMDiff {T δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
      (identityFlowSurface (δ := δ) d hbalance s) := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle T × Ioo (0 : ℝ) δ => p.1) := contMDiff_fst
  exact ((periodicLift_contMDiff d.smooth_γ d.period_γ).comp hs).add
    ((identityFlowHeight_contMDiff d hbalance s hden).smul
      ((periodicLift_contMDiff d.smooth_E d.period_E).comp hs))

theorem identityFlowSurface_real_lift {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (s t : ℝ) (v : Ioo (0 : ℝ) δ) :
    identityFlowSurface d hbalance s (periodProjection T t, v) =
      ruledMap d.γ d.E (![t,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t] : Coord) := by
  rfl

end
end TightVer401


