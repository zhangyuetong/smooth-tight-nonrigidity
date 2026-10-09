import TightVer401.PositiveExitConstructionLevels
import TightVer401.PeriodicRuledNativeGauss
import TightVer401.NormalLoopEmbeddingArclength
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The same selected complete characteristic leaf, its actual spherical
Gauss image, and its derived unit-speed reparametrization. Geometric Gauss
injectivity/north are ordinary band inputs; no leaf or arclength witness is
supplied. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {T δ w : ℝ} (d : PeriodicRuledFrame T)
  (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
  (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
    principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
  (v : Ioo (0 : ℝ) δ)

/-- The selected actual characteristic leaf in the original positive band. -/
def positiveExitLeaf (q : AddCircle T) : AddCircle T × Ioo (0 : ℝ) w :=
  identityFlowBandInclusion d hb 0 hinside (q, v)

/-- Its actual spherical Gauss image. -/
def positiveExitGaussLeaf (q : AddCircle T) : RoundSphere :=
  d.bandSphereGauss (positiveExitLeaf d hb hinside v q)

/-- The actual ambient Gauss leaf, used for derivative calculations. -/
def positiveExitAmbientLeaf (q : AddCircle T) : Ambient :=
  (positiveExitGaussLeaf d hb hinside v q).val

/-- Its actual periodic real representative. -/
def positiveExitRawLeaf (t : ℝ) : Ambient :=
  positiveExitAmbientLeaf d hb hinside v (periodProjection T t)

@[simp] theorem positiveExitLeaf_fst (q : AddCircle T) :
    (positiveExitLeaf d hb hinside v q).1 = q := rfl

variable [Fact (0 < T)]

theorem positiveExitLeaf_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (positiveExitLeaf d hb hinside v) :=
  (identityFlowBandInclusion_contMDiff d hb 0
    (fun u hu t => positiveExit_trajectory_denominator_ne_zero d hinside hu t) hinside).comp
      (contMDiff_id.prodMk contMDiff_const)

theorem positiveExitLeaf_injective : Function.Injective (positiveExitLeaf d hb hinside v) := by
  intro q r h
  exact congrArg Prod.fst h

/-- First-coordinate identity gives actual tangent injection without a flow-rank premise. -/
theorem positiveExitLeaf_differential_injective (q : AddCircle T) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (positiveExitLeaf d hb hinside v) q) := by
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : AddCircle T × Ioo (0 : ℝ) w → AddCircle T) := contMDiff_fst
  have hD := mfderiv_comp q
    ((hf (positiveExitLeaf d hb hinside v q)).mdifferentiableAt (by simp))
    ((positiveExitLeaf_contMDiff d hb hinside v q).mdifferentiableAt (by simp))
  have he : (Prod.fst : AddCircle T × Ioo (0 : ℝ) w → AddCircle T) ∘
      positiveExitLeaf d hb hinside v = id := rfl
  rw [he, mfderiv_id] at hD
  intro a b hab
  have ha := congrArg (fun D => D a) hD
  have hz := congrArg (fun D => D b) hD
  change a = mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.fst
    (positiveExitLeaf d hb hinside v q)
    (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (positiveExitLeaf d hb hinside v) q a) at ha
  change b = mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.fst
    (positiveExitLeaf d hb hinside v q)
    (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (positiveExitLeaf d hb hinside v) q b) at hz
  exact ha.trans ((congrArg
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.fst
      (positiveExitLeaf d hb hinside v q)) hab).trans hz.symm)

theorem positiveExitGaussLeaf_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (positiveExitGaussLeaf d hb hinside v) :=
  (periodicRuledFrame_bandSphereGauss_contMDiff d).comp
    (positiveExitLeaf_contMDiff d hb hinside v)

theorem positiveExitAmbientLeaf_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ (positiveExitAmbientLeaf d hb hinside v) :=
  (periodicRuledFrame_bandGaussMap_contMDiff d).comp
    (positiveExitLeaf_contMDiff d hb hinside v)

theorem positiveExitAmbientLeaf_differential_injective (q : AddCircle T) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient)
      (positiveExitAmbientLeaf d hb hinside v) q) := by
  have hD := mfderiv_comp q
    ((periodicRuledFrame_bandGaussMap_contMDiff d _).mdifferentiableAt (by simp))
    ((positiveExitLeaf_contMDiff d hb hinside v q).mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (positiveExitAmbientLeaf d hb hinside v) q = _ at hD
  rw [hD]
  exact (periodicRuledFrame_bandGaussMap_differential_injective d _).comp
    (positiveExitLeaf_differential_injective d hb hinside v q)

theorem positiveExitAmbientLeaf_injective
    (hG : Function.Injective (d.bandGaussMap (b := w))) :
    Function.Injective (positiveExitAmbientLeaf d hb hinside v) :=
  hG.comp (positiveExitLeaf_injective d hb hinside v)

theorem positiveExitGaussLeaf_isEmbedding
    (hG : Function.Injective (d.bandGaussMap (b := w))) :
    Topology.IsEmbedding (positiveExitGaussLeaf d hb hinside v) := by
  have hi : Function.Injective (positiveExitGaussLeaf d hb hinside v) := by
    intro p q h
    exact positiveExitAmbientLeaf_injective d hb hinside v hG (congrArg Subtype.val h)
  exact ((positiveExitGaussLeaf_contMDiff d hb hinside v).continuous.isClosedEmbedding hi).isEmbedding

theorem positiveExitGaussLeaf_north
    (hn : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) (q : AddCircle T) :
    0 < (positiveExitGaussLeaf d hb hinside v q).val 2 := hn _

theorem positiveExitRawLeaf_contDiff : ContDiff ℝ ∞ (positiveExitRawLeaf d hb hinside v) :=
  ((positiveExitAmbientLeaf_contMDiff d hb hinside v).comp (periodProjection_contMDiff T)).contDiff

theorem positiveExitRawLeaf_periodic : Function.Periodic (positiveExitRawLeaf d hb hinside v) T := by
  intro t
  change positiveExitAmbientLeaf d hb hinside v ((t + T : ℝ) : AddCircle T) =
    positiveExitAmbientLeaf d hb hinside v (t : AddCircle T)
  rw [AddCircle.coe_add_period]

theorem positiveExitRawLeaf_deriv_ne_zero (t : ℝ) : deriv (positiveExitRawLeaf d hb hinside v) t ≠ 0 := by
  have hproj : Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection T) t : ℝ →L[ℝ] ℝ) := by
    let D : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection T) t
    obtain ⟨z, hz⟩ := periodProjection_mfderiv_surjective T t (1 : ℝ)
    change D z = 1 at hz
    have hlin (x : ℝ) : D x = x * D 1 := by
      simpa only [smul_eq_mul, mul_one] using D.map_smul x (1 : ℝ)
    have hD1 : D 1 ≠ 0 := by
      intro hh
      have he := hlin z
      rw [hz, hh, mul_zero] at he
      norm_num at he
    change Function.Injective (D : ℝ → ℝ)
    refine fun (x y : ℝ) (hxy : D x = D y) => ?_
    rw [hlin x, hlin y] at hxy
    exact mul_right_cancel₀ hD1 hxy
  have hD := mfderiv_comp t
    ((positiveExitAmbientLeaf_contMDiff d hb hinside v _).mdifferentiableAt (by simp))
    ((periodProjection_contMDiff T t).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hD
  change fderiv ℝ (positiveExitRawLeaf d hb hinside v) t = _ at hD
  have hi : Function.Injective (fderiv ℝ (positiveExitRawLeaf d hb hinside v) t) := by
    rw [hD]
    exact (positiveExitAmbientLeaf_differential_injective d hb hinside v _).comp hproj
  intro hz
  have he : fderiv ℝ (positiveExitRawLeaf d hb hinside v) t (1 : ℝ) =
      fderiv ℝ (positiveExitRawLeaf d hb hinside v) t (0 : ℝ) := by
    rw [((positiveExitRawLeaf_contDiff d hb hinside v).differentiable (by simp) t).hasDerivAt.hasFDerivAt.fderiv]
    simp [hz]
  have hbad := hi he
  norm_num at hbad

theorem positiveExitRawLeaf_injOn (hG : Function.Injective (d.bandGaussMap (b := w))) :
    InjOn (positiveExitRawLeaf d hb hinside v) (Ico 0 T) := by
  intro r hr s hs h
  have hp := positiveExitAmbientLeaf_injective d hb hinside v hG h
  change (r : AddCircle T) = (s : AddCircle T) at hp
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) (p := T)
    (by simpa only [zero_add] using hr) (by simpa only [zero_add] using hs)).mp hp

/-- Actual positive periodic speed of the selected raw spherical leaf. -/
def positiveExitLeafSpeed (t : ℝ) : ℝ := ‖deriv (positiveExitRawLeaf d hb hinside v) t‖

theorem positiveExitLeafSpeed_contDiff : ContDiff ℝ ∞ (positiveExitLeafSpeed d hb hinside v) :=
  (contDiff_infty_iff_deriv.mp (positiveExitRawLeaf_contDiff d hb hinside v)).2.norm ℝ
    (positiveExitRawLeaf_deriv_ne_zero d hb hinside v)

theorem positiveExitLeafSpeed_pos (t : ℝ) : 0 < positiveExitLeafSpeed d hb hinside v t :=
  norm_pos_iff.mpr (positiveExitRawLeaf_deriv_ne_zero d hb hinside v t)

theorem positiveExitLeafSpeed_periodic : Function.Periodic (positiveExitLeafSpeed d hb hinside v) T := by
  have hp := normalLoop_derivative_periodic (positiveExitRawLeaf_periodic d hb hinside v)
    (fun t => ((positiveExitRawLeaf_contDiff d hb hinside v).differentiable (by simp) t).hasDerivAt)
  intro t
  unfold positiveExitLeafSpeed
  rw [hp t]

/-- Actual unit-speed northern embedded periodic parametrization of this
same leaf. Its length, inverse arclength and speed are all constructed. -/
theorem positiveExitLeaf_exists_unitSpeed
    (hG : Function.Injective (d.bandGaussMap (b := w)))
    (hn : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) :
    ∃ e : ℝ ≃ₜ ℝ, ∃ L > 0,
      (e : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v) ∧
      L = rawPrimitive (positiveExitLeafSpeed d hb hinside v) T ∧
      ContDiff ℝ ∞ e.symm ∧
      (∀ s, e.symm (s + L) = e.symm s + T) ∧
      ∃ hp : Function.Periodic (positiveExitRawLeaf d hb hinside v ∘ e.symm) L,
        ContDiff ℝ ∞ (positiveExitRawLeaf d hb hinside v ∘ e.symm) ∧
        Function.Injective hp.lift ∧
        (∀ s, inner ℝ ((positiveExitRawLeaf d hb hinside v ∘ e.symm) s)
          ((positiveExitRawLeaf d hb hinside v ∘ e.symm) s) = 1) ∧
        (∀ s, 0 < (positiveExitRawLeaf d hb hinside v ∘ e.symm) s 2) ∧
        (∀ s, inner ℝ (deriv (positiveExitRawLeaf d hb hinside v ∘ e.symm) s)
          (deriv (positiveExitRawLeaf d hb hinside v ∘ e.symm) s) = 1) := by
  let a := positiveExitLeafSpeed d hb hinside v
  let ξ := positiveExitRawLeaf d hb hinside v
  have ha : ContDiff ℝ ∞ a := positiveExitLeafSpeed_contDiff d hb hinside v
  have hapos : ∀ t, 0 < a t := positiveExitLeafSpeed_pos d hb hinside v
  have hap : Function.Periodic a T := positiveExitLeafSpeed_periodic d hb hinside v
  have hξ : ContDiff ℝ ∞ ξ := positiveExitRawLeaf_contDiff d hb hinside v
  have hξp : Function.Periodic ξ T := positiveExitRawLeaf_periodic d hb hinside v
  obtain ⟨e, he, hψ, hderiv, hshift⟩ := normalLoop_exists_global_arclength_inverse ha hapos hap (Fact.out : 0 < T)
  let L := rawPrimitive a T
  have hL : 0 < L := normalLoop_arclength_period_pos ha.continuous hapos (Fact.out : 0 < T)
  letI : Fact (0 < L) := ⟨hL⟩
  have hp : Function.Periodic (ξ ∘ e.symm) L := by
    intro s
    change ξ (e.symm (s + L)) = ξ (e.symm s)
    rw [hshift s, hξp]
  have hζ : ContDiff ℝ ∞ (ξ ∘ e.symm) := hξ.comp hψ
  have hi : InjOn (ξ ∘ e.symm) (Ico 0 L) :=
    normalLoop_arclength_reparameterized_injective ha.continuous hapos e he
      (positiveExitRawLeaf_injOn d hb hinside v hG)
  refine ⟨e, L, hL, he, rfl, hψ, hshift, hp, hζ, periodicCurve_lift_injective hp hi, ?_, ?_, ?_⟩
  · intro s
    have hu : ‖ξ (e.symm s)‖ = 1 := by
      exact (periodicRuledFrame_fullGaussMap_norm d _)
    rw [real_inner_self_eq_norm_sq]
    change ‖ξ (e.symm s)‖ ^ 2 = 1
    rw [hu]
    norm_num
  · intro s
    exact positiveExitGaussLeaf_north d hb hinside v hn (periodProjection T (e.symm s))
  · intro s
    have hd : HasDerivAt (ξ ∘ e.symm) ((a (e.symm s))⁻¹ • deriv ξ (e.symm s)) s :=
      ((hξ.differentiable (by simp) (e.symm s)).hasDerivAt).scomp s (hderiv s)
    have hnorm : ‖deriv (ξ ∘ e.symm) s‖ = 1 := by
      rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hapos _))]
      change (a (e.symm s))⁻¹ * a (e.symm s) = 1
      exact inv_mul_cancel₀ (hapos _).ne'
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num

end
end TightVer401
