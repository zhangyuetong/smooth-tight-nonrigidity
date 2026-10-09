import TightVer401.NormalLoopCriterionImmersion
import TightVer401.ThinBandRuledGauss
import TightVer401.SphereCharts

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The normal on the native open band, with exactly the frame's normal formula. -/
def PeriodicRuledFrame.bandGaussMap {L b : ℝ} (d : PeriodicRuledFrame L) :
    AddCircle L × Ioo (0 : ℝ) b → Ambient :=
  fun p => d.fullGaussMap (p.1, (p.2 : ℝ))

theorem periodicRuledFrame_fullGaussMap_contMDiff {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ d.fullGaussMap := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : AddCircle L × ℝ → AddCircle L) := contMDiff_fst
  have hT := (periodicLift_contMDiff d.smooth_T d.period_T).comp hs
  have hn := (periodicLift_contMDiff d.smooth_n d.period_n).comp hs
  have hk := (periodicLift_contMDiff d.smooth_k d.period_k).comp hs
  have hτ := (periodicLift_contMDiff d.smooth_τ d.period_τ).comp hs
  have hu : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : AddCircle L × ℝ → ℝ) := contMDiff_snd
  have hτne (q : AddCircle L) : d.period_τ.lift q ≠ 0 := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa only [Function.Periodic.lift_coe] using d.torsion_ne_zero r
  have henergy : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × ℝ => ruledEnergy (d.period_k.lift p.1)
        (d.period_τ.lift p.1) p.2) := by
    exact ((contMDiff_const.sub (hk.mul hu)).pow 2).add ((hτ.pow 2).mul (hu.pow 2))
  have hroot : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × ℝ => Real.sqrt
        (ruledEnergy (d.period_k.lift p.1) (d.period_τ.lift p.1) p.2)) := by
    intro p
    exact (Real.contDiffAt_sqrt (ruledEnergy_pos (hτne p.1)).ne').contMDiffAt.comp p (henergy p)
  have hrootne (p : AddCircle L × ℝ) : Real.sqrt
      (ruledEnergy (d.period_k.lift p.1) (d.period_τ.lift p.1) p.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (ruledEnergy_pos (hτne p.1))).ne'
  exact (((hτ.neg.mul hu).div₀ hroot hrootne).smul hT).add
    (((contMDiff_const.sub (hk.mul hu)).div₀ hroot hrootne).smul hn)

theorem periodicRuledFrame_bandGaussMap_contMDiff {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (d.bandGaussMap (b := b)) := by
  exact (periodicRuledFrame_fullGaussMap_contMDiff d).comp
    (contMDiff_fst.prodMk ((contMDiff_subtype_val (U := bandOpen b)).comp contMDiff_snd))

theorem periodicRuledFrame_fullGaussMap_unit {L : ℝ} (d : PeriodicRuledFrame L)
    (p : AddCircle L × ℝ) : inner ℝ (d.fullGaussMap p) (d.fullGaussMap p) = 1 := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
  unfold PeriodicRuledFrame.fullGaussMap
  rw [← hr]
  simp only [Function.Periodic.lift_coe]
  exact ruledNormal_unit (d.orthonormal r) (d.torsion_ne_zero r)

theorem periodicRuledFrame_fullGaussMap_central {L : ℝ} (d : PeriodicRuledFrame L)
    (q : AddCircle L) : d.fullGaussMap (q, 0) = d.period_n.lift q := by
  simp [PeriodicRuledFrame.fullGaussMap, ruledNormal, ruledEnergy]

/-- Every tangent vector of the native band comes from the genuine planar coordinates. -/
theorem periodicRuledFrame_coordinate_differential_surjective {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (q : coordinateBandOpen b) :
    Function.Surjective (bandFromCoordinatesDifferential L b q) := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hraw : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates L b) q =
      fderiv ℝ (ruledMap d.γ d.E) q.val :=
    openCoordinate_restriction_derivative q (hX.differentiable (by simp) q.val)
  have hchain : fderiv ℝ (ruledMap d.γ d.E) q.val =
      (bandDifferential d.bandMap (bandFromCoordinates L b q)).comp
        (bandFromCoordinatesDifferential L b q) := by
    rw [← hraw]
    exact mfderiv_comp q ((d.bandMap_contMDiff _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff L b q).mdifferentiableAt (by simp))
  have hinj := ruled_differential_injective (d.deriv_γ (q.val 0))
    (d.deriv_E (q.val 0)) (d.orthonormal (q.val 0)) (d.torsion_ne_zero (q.val 0))
  have hcoord : Function.Injective (bandFromCoordinatesDifferential L b q) := by
    intro v z hvz
    apply hinj
    rw [hchain]
    exact congrArg (bandDifferential d.bandMap (bandFromCoordinates L b q)) hvz
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Coord]) (f := (bandFromCoordinatesDifferential L b q).toLinearMap)).mp hcoord

theorem periodicRuledFrame_bandGaussMap_orthogonal {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b) (v : ℝ × ℝ) :
    inner ℝ (bandDifferential d.bandMap p v) (d.bandGaussMap p) = 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : coordinateBandOpen b := ⟨![s, (p.2 : ℝ)], p.2.property⟩
  have hq : bandFromCoordinates L b q = p := Prod.ext hs (Subtype.ext rfl)
  obtain ⟨v₀, hv₀⟩ := periodicRuledFrame_coordinate_differential_surjective d q v
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hraw : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates L b) q =
      fderiv ℝ (ruledMap d.γ d.E) q.val :=
    openCoordinate_restriction_derivative q (hX.differentiable (by simp) q.val)
  have hchain : fderiv ℝ (ruledMap d.γ d.E) q.val =
      (bandDifferential d.bandMap (bandFromCoordinates L b q)).comp
        (bandFromCoordinatesDifferential L b q) := by
    rw [← hraw]
    exact mfderiv_comp q ((d.bandMap_contMDiff _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff L b q).mdifferentiableAt (by simp))
  have hd : bandDifferential d.bandMap p v = fderiv ℝ (ruledMap d.γ d.E) q.val v₀ := by
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, hv₀, hq]
  have hn : d.bandGaussMap p = d.rawGaussMap q.val := by
    rw [← hq]
    simp only [PeriodicRuledFrame.bandGaussMap, PeriodicRuledFrame.fullGaussMap,
      PeriodicRuledFrame.rawGaussMap, bandFromCoordinates]
    rfl
  rw [hd, hn]
  exact (ruled_isUnitNormal (d.deriv_γ (q.val 0)) (d.deriv_E (q.val 0))
    (d.orthonormal (q.val 0)) (d.torsion_ne_zero (q.val 0))).2 v₀


/-- The actual normal has nondegenerate differential in the native quotient coordinates. -/
theorem periodicRuledFrame_bandGaussMap_differential_injective {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b) :
    Function.Injective (bandDifferential (d.bandGaussMap (b := b)) p) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : coordinateBandOpen b := ⟨![s, (p.2 : ℝ)], p.2.property⟩
  have hq : bandFromCoordinates L b q = p := Prod.ext hs (Subtype.ext rfl)
  have hraw : openCoordinateDifferential (d.bandGaussMap ∘ bandFromCoordinates L b) q =
      fderiv ℝ d.rawGaussMap q.val :=
    openCoordinate_restriction_derivative q
      ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp) q.val)
  have hchain : fderiv ℝ d.rawGaussMap q.val =
      (bandDifferential d.bandGaussMap (bandFromCoordinates L b q)).comp
        (bandFromCoordinatesDifferential L b q) := by
    rw [← hraw]
    exact mfderiv_comp q ((periodicRuledFrame_bandGaussMap_contMDiff d _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff L b q).mdifferentiableAt (by simp))
  intro v z hvz
  obtain ⟨v₀, hv₀⟩ := periodicRuledFrame_coordinate_differential_surjective d q v
  obtain ⟨z₀, hz₀⟩ := periodicRuledFrame_coordinate_differential_surjective d q z
  have heq : v₀ = z₀ := periodicRuledFrame_rawGaussMap_differential_injective d q.val (by
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, hv₀, hz₀, hq]
    exact hvz)
  rw [← hv₀, ← hz₀, heq]

theorem periodicRuledFrame_fullGaussMap_norm {L : ℝ} (d : PeriodicRuledFrame L)
    (p : AddCircle L × ℝ) : ‖d.fullGaussMap p‖ = 1 := by
  have h := periodicRuledFrame_fullGaussMap_unit d p
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (d.fullGaussMap p)]

local instance periodicRuledNativeGaussSphereDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- The actual band normal as a map to the standard round sphere. -/
def PeriodicRuledFrame.bandSphereGauss {L b : ℝ} (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) : RoundSphere :=
  ⟨d.bandGaussMap p, by simpa [PeriodicRuledFrame.bandGaussMap] using periodicRuledFrame_fullGaussMap_norm d (p.1, (p.2 : ℝ))⟩

theorem periodicRuledFrame_bandSphereGauss_contMDiff {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (d.bandSphereGauss (b := b)) := by
  exact (periodicRuledFrame_bandGaussMap_contMDiff d).codRestrict_sphere
    (fun p => by simpa [PeriodicRuledFrame.bandGaussMap] using periodicRuledFrame_fullGaussMap_norm d (p.1, (p.2 : ℝ)))


theorem periodicRuledFrame_bandSphereGauss_differential_injective {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
      (d.bandSphereGauss (b := b)) p) := by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ ((↑) : RoundSphere → Ambient) :=
    contMDiff_coe_sphere
  have hchain := mfderiv_comp p
    ((hc (d.bandSphereGauss p)).mdifferentiableAt (by simp))
    ((periodicRuledFrame_bandSphereGauss_contMDiff d p).mdifferentiableAt (by simp))
  change bandDifferential d.bandGaussMap p = _ at hchain
  intro v z hvz
  apply periodicRuledFrame_bandGaussMap_differential_injective d p
  have hv := congrArg (fun F => F v) hchain
  have hz := congrArg (fun F => F z) hchain
  exact hv.trans ((congrArg
    (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) ((↑) : RoundSphere → Ambient) (d.bandSphereGauss p))
    hvz).trans hz.symm)

theorem periodicRuledFrame_bandSphereGauss_injective_of_actual {L b : ℝ}
    (d : PeriodicRuledFrame L) (hi : Function.Injective (d.bandGaussMap (b := b))) :
    Function.Injective (d.bandSphereGauss (b := b)) := by
  intro p q hpq
  exact hi (congrArg Subtype.val hpq)

end
end TightVer401
