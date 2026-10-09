import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.RevolutionEndImmersion
import TightVer401.NativeCompactEmbeddingStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Local representatives of the literal protected torus assembly.
The square-root end profiles are converted to signed smooth parabolic collars,
including their actual nonzero transverse derivatives at both seams.
-/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private def protectedTorusRotation (A B : ℝ → ℝ) (p : ℝ × ℝ) : Ambient :=
  A p.2 • revolutionRadial p.1 + B p.2 • revolutionAxis

private theorem protectedTorusRotation_contDiffAt {A B : ℝ → ℝ} {s u : ℝ}
    (hA : ContDiffAt ℝ ∞ A u) (hB : ContDiffAt ℝ ∞ B u) :
    ContDiffAt ℝ ∞ (protectedTorusRotation A B) (s, u) := by
  exact ((hA.comp (s,u) contDiffAt_snd).smul
    (revolutionRadial_contDiff.contDiffAt.comp (s,u) contDiffAt_fst)).add
    ((hB.comp (s,u) contDiffAt_snd).smul contDiffAt_const)

private theorem protectedTorusRotation_fderiv_apply {A B : ℝ → ℝ} {s u A' B' : ℝ}
    (hA : HasDerivAt A A' u) (hB : HasDerivAt B B' u) (v : ℝ × ℝ) :
    fderiv ℝ (protectedTorusRotation A B) (s,u) v =
      (v.2 * A') • revolutionRadial s +
      (A u * v.1) • revolutionAngular s + (v.2 * B') • revolutionAxis := by
  unfold protectedTorusRotation
  have hAr := hA.hasFDerivAt.comp (s,u)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (s,u)))
  have hBr := hB.hasFDerivAt.comp (s,u)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (s,u)))
  have hEr := (revolutionRadial_hasDerivAt s).hasFDerivAt.comp (s,u)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (s,u)))
  have hd := (hAr.smul hEr).add (hBr.smul (hasFDerivAt_const (c := revolutionAxis) (s,u)))
  have hv := congrArg (fun D => D v) hd.fderiv
  have hfun : (A ∘ (Prod.snd : ℝ × ℝ → ℝ) •
      revolutionRadial ∘ (Prod.fst : ℝ × ℝ → ℝ) +
      B ∘ (Prod.snd : ℝ × ℝ → ℝ) • (fun (_ : ℝ × ℝ) => revolutionAxis)) =
      (fun p : ℝ × ℝ => A p.2 • revolutionRadial p.1 + B p.2 • revolutionAxis) := by
    funext p
    rfl
  rw [hfun] at hv
  simpa [ContinuousLinearMap.comp_apply, smul_smul, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc] using hv

private theorem protectedTorusRotation_fderiv_injective {A B : ℝ → ℝ} {s u A' B' : ℝ}
    (hA : HasDerivAt A A' u) (hB : HasDerivAt B B' u)
    (hR : A u ≠ 0) (htrans : A' ≠ 0 ∨ B' ≠ 0) :
    Function.Injective (fderiv ℝ (protectedTorusRotation A B) (s,u)) := by
  rcases revolution_frame s with ⟨hrr, haa, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular s) (revolutionRadial s) = 0 := by
    rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial s) = 0 := by
    rw [real_inner_comm, hrz]
  have hza : inner ℝ revolutionAxis (revolutionAngular s) = 0 := by
    rw [real_inner_comm, haz]
  intro v w he
  have hzero : fderiv ℝ (protectedTorusRotation A B) (s,u) (v-w) = 0 := by
    simp only [map_sub, he, sub_self]
  rw [protectedTorusRotation_fderiv_apply hA hB] at hzero
  have hfirst : (v-w).1 = 0 := by
    have h := congrArg (fun z : Ambient => inner ℝ z (revolutionAngular s)) hzero
    simp only [inner_add_left, real_inner_smul_left, hra, haa, hza,
      mul_zero, mul_one, zero_add, add_zero, inner_zero_left] at h
    exact (mul_eq_zero.mp h).resolve_left hR
  have hsecond : (v-w).2 = 0 := by
    rcases htrans with hA' | hB'
    · have h := congrArg (fun z : Ambient => inner ℝ z (revolutionRadial s)) hzero
      simp only [inner_add_left, real_inner_smul_left, hrr, har, hzr,
        mul_zero, mul_one, zero_add, add_zero, inner_zero_left] at h
      exact (mul_eq_zero.mp h).resolve_right hA'
    · have h := congrArg (fun z : Ambient => inner ℝ z revolutionAxis) hzero
      simp only [inner_add_left, real_inner_smul_left, hrz, haz, hzz,
        mul_zero, mul_one, zero_add, add_zero, inner_zero_left] at h
      exact (mul_eq_zero.mp h).resolve_right hB'
  apply sub_eq_zero.mp
  exact Prod.ext hfirst hsecond

private theorem protectedTorusCollarScale_positive {h μ : ℝ} (hh : 0 < h) (hμ : 0 < μ) :
    0 < protectedTorusCollarScale h μ := by
  unfold protectedTorusCollarScale
  positivity

private theorem protectedTorusCollarScale_square {h μ : ℝ} (hh : 0 < h) (hμ : 0 < μ) :
    μ * (protectedTorusCollarScale h μ)^2 = 4 * h := by
  have hs := Real.sq_sqrt (le_of_lt (div_pos hh hμ))
  have hm : (Real.sqrt (h / μ))^2 * μ = h := (eq_div_iff hμ.ne').mp hs
  dsimp [protectedTorusCollarScale]
  nlinarith

private theorem protectedTorusMap_real_representative
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h s u : ℝ)
    (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    protectedTorusMap S r h (periodProjection (2 * Real.pi) s,
      periodProjection (2 * Real.pi) u) =
      if u ≤ Real.pi then S (periodProjection (2 * Real.pi) s,u)
      else protectedTorusConvexCylinder r h (periodProjection (2 * Real.pi) s,u) := by
  unfold protectedTorusMap
  have he : (AddCircle.equivIco (2 * Real.pi) 0
      (periodProjection (2 * Real.pi) u)).val = u := by
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hu))
  rw [he]

private theorem protectedTorusConvexCylinder_north_eq {RN μ h : ℝ}
    (hh : 0 < h) (hμ : 0 < μ) {r : ℝ → ℝ}
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Icc Real.pi (2 * Real.pi))
    (hr : r (-h * Real.cos u) = RN + Real.sqrt (2 * μ * (h + h * Real.cos u))) :
    protectedTorusConvexCylinder r h (q,u) = protectedTorusNorthCollar RN μ h
      (q,-protectedTorusCollarScale h μ * Real.cos (u/2)) := by
  let c := protectedTorusCollarScale h μ
  have hc : 0 < c := protectedTorusCollarScale_positive hh hμ
  have hc2 : μ * c^2 = 4*h := protectedTorusCollarScale_square hh hμ
  have hcos : Real.cos (u/2) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le
    (by linarith [hu.1]) (by linarith [hu.2, Real.pi_pos])
  have hd : Real.cos u = 2 * Real.cos (u/2)^2 - 1 := by
    convert Real.cos_two_mul (u/2) using 1 <;> ring
  have hsquare : (μ * (-c * Real.cos (u/2)))^2 = 2*μ*(h+h*Real.cos u) := by
    calc
      (μ * (-c * Real.cos (u/2)))^2 = μ * (μ*c^2) * Real.cos (u/2)^2 := by ring
      _ = 2*μ*(h+h*Real.cos u) := by rw [hc2, hd]; ring
  have hnonneg : 0 ≤ μ * (-c * Real.cos (u/2)) :=
    mul_nonneg hμ.le (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hc.le) hcos)
  have hsqrt : Real.sqrt (2*μ*(h+h*Real.cos u)) = μ * (-c * Real.cos (u/2)) :=
    (Real.sqrt_eq_iff_eq_sq (by rw [← hsquare]; positivity) hnonneg).mpr hsquare.symm
  have hheight : h - μ * (-c * Real.cos (u/2))^2/2 = -h * Real.cos u := by
    calc
      h - μ * (-c * Real.cos (u/2))^2/2 = h - (μ*c^2)*Real.cos (u/2)^2/2 := by ring
      _ = -h * Real.cos u := by rw [hc2, hd]; ring
  dsimp only [protectedTorusConvexCylinder, revolutionEndCircleFull, protectedTorusNorthCollar]
  change r (-h * Real.cos u) • revolutionCircleRadial q + (-h * Real.cos u) • revolutionAxis =
    (RN + μ * (-c * Real.cos (u/2))) • revolutionCircleRadial q +
      (h - μ * (-c * Real.cos (u/2))^2/2) • revolutionAxis
  rw [hr,hsqrt,hheight]

private theorem protectedTorusConvexCylinder_south_eq {RN μ h : ℝ}
    (hh : 0 < h) (hμ : 0 < μ) {r : ℝ → ℝ}
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Icc (-Real.pi) (0 : ℝ))
    (hr : r (-h * Real.cos u) = RN + Real.sqrt (2 * μ * (h - h * Real.cos u))) :
    protectedTorusConvexCylinder r h (q,u) = protectedTorusSouthCollar RN μ h
      (q,-protectedTorusCollarScale h μ * Real.sin (u/2)) := by
  let c := protectedTorusCollarScale h μ
  have hc : 0 < c := protectedTorusCollarScale_positive hh hμ
  have hc2 : μ * c^2 = 4*h := protectedTorusCollarScale_square hh hμ
  have hsin : Real.sin (u/2) ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (by linarith [hu.2]) (by linarith [hu.1, Real.pi_pos])
  have hd : Real.cos u = 1 - 2 * Real.sin (u/2)^2 := by
    convert Real.cos_two_mul_eq_one_sub (u/2) using 1 <;> ring
  have hsquare : (μ * (-c * Real.sin (u/2)))^2 = 2*μ*(h-h*Real.cos u) := by
    calc
      (μ * (-c * Real.sin (u/2)))^2 = μ * (μ*c^2) * Real.sin (u/2)^2 := by ring
      _ = 2*μ*(h-h*Real.cos u) := by rw [hc2, hd]; ring
  have hnonneg : 0 ≤ μ * (-c * Real.sin (u/2)) :=
    mul_nonneg hμ.le (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hc.le) hsin)
  have hsqrt : Real.sqrt (2*μ*(h-h*Real.cos u)) = μ * (-c * Real.sin (u/2)) :=
    (Real.sqrt_eq_iff_eq_sq (by rw [← hsquare]; positivity) hnonneg).mpr hsquare.symm
  have hheight : -h + μ * (-c * Real.sin (u/2))^2/2 = -h * Real.cos u := by
    calc
      -h + μ * (-c * Real.sin (u/2))^2/2 = -h + (μ*c^2)*Real.sin (u/2)^2/2 := by ring
      _ = -h * Real.cos u := by rw [hc2, hd]; ring
  dsimp only [protectedTorusConvexCylinder, revolutionEndCircleFull, protectedTorusSouthCollar]
  change r (-h * Real.cos u) • revolutionCircleRadial q + (-h * Real.cos u) • revolutionAxis =
    (RN + μ * (-c * Real.sin (u/2))) • revolutionCircleRadial q +
      (-h + μ * (-c * Real.sin (u/2))^2/2) • revolutionAxis
  rw [hr,hsqrt,hheight]

private def protectedTorusRealLift {RN μ h : ℝ} (d : ProtectedTorusAssemblyInput RN μ h)
    (p : ℝ × ℝ) : Ambient :=
  protectedTorusMap d.saddle d.meridian h
    (periodProjection (2 * Real.pi) p.1, periodProjection (2 * Real.pi) p.2)

private def protectedTorusNorthReal (RN μ h : ℝ) : ℝ × ℝ → Ambient :=
  protectedTorusRotation
    (fun u => RN + μ * (-protectedTorusCollarScale h μ * Real.cos (u/2)))
    (fun u => h - μ * (-protectedTorusCollarScale h μ * Real.cos (u/2))^2/2)

private def protectedTorusSouthReal (RN μ h : ℝ) : ℝ × ℝ → Ambient :=
  protectedTorusRotation
    (fun u => RN + μ * (-protectedTorusCollarScale h μ * Real.sin (u/2)))
    (fun u => -h + μ * (-protectedTorusCollarScale h μ * Real.sin (u/2))^2/2)

private theorem protectedTorusNorthReal_eq (RN μ h s u : ℝ) :
    protectedTorusNorthReal RN μ h (s,u) = protectedTorusNorthCollar RN μ h
      (periodProjection (2 * Real.pi) s,-protectedTorusCollarScale h μ * Real.cos (u/2)) := by
  simp only [protectedTorusNorthReal, protectedTorusRotation, protectedTorusNorthCollar,
    revolutionCircleRadial_representative]

private theorem protectedTorusSouthReal_eq (RN μ h s u : ℝ) :
    protectedTorusSouthReal RN μ h (s,u) = protectedTorusSouthCollar RN μ h
      (periodProjection (2 * Real.pi) s,-protectedTorusCollarScale h μ * Real.sin (u/2)) := by
  simp only [protectedTorusSouthReal, protectedTorusRotation, protectedTorusSouthCollar,
    revolutionCircleRadial_representative]

private theorem protectedTorusNorthReal_smooth_rank {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) :
    ContDiffAt ℝ ∞ (protectedTorusNorthReal RN μ h) (s,Real.pi) ∧
      Function.Injective (fderiv ℝ (protectedTorusNorthReal RN μ h) (s,Real.pi)) := by
  let A : ℝ → ℝ := fun u => RN + μ * (-protectedTorusCollarScale h μ * Real.cos (u/2))
  let B : ℝ → ℝ := fun u => h - μ * (-protectedTorusCollarScale h μ * Real.cos (u/2))^2/2
  have hA : ContDiff ℝ ∞ A := by dsimp [A]; fun_prop
  have hB : ContDiff ℝ ∞ B := by dsimp [B]; fun_prop
  have hAd : HasDerivAt A (μ * protectedTorusCollarScale h μ / 2) Real.pi := by
    convert! ((((hasDerivAt_id Real.pi).div_const 2).cos.const_mul
      (-protectedTorusCollarScale h μ)).const_mul μ).const_add RN using 1 <;>
      simp [A, Real.sin_pi_div_two] <;> ring
  refine ⟨protectedTorusRotation_contDiffAt hA.contDiffAt hB.contDiffAt, ?_⟩
  apply protectedTorusRotation_fderiv_injective hAd
    ((hB.differentiable (by simp) Real.pi).hasDerivAt)
  · simpa [A] using d.radius_pos.ne'
  · left
    exact ne_of_gt (div_pos (mul_pos d.coefficient_pos
      (protectedTorusCollarScale_positive d.height_pos d.coefficient_pos)) (by norm_num))

private theorem protectedTorusSouthReal_smooth_rank {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) :
    ContDiffAt ℝ ∞ (protectedTorusSouthReal RN μ h) (s,(0 : ℝ)) ∧
      Function.Injective (fderiv ℝ (protectedTorusSouthReal RN μ h) (s,(0 : ℝ))) := by
  let A : ℝ → ℝ := fun u => RN + μ * (-protectedTorusCollarScale h μ * Real.sin (u/2))
  let B : ℝ → ℝ := fun u => -h + μ * (-protectedTorusCollarScale h μ * Real.sin (u/2))^2/2
  have hA : ContDiff ℝ ∞ A := by dsimp [A]; fun_prop
  have hB : ContDiff ℝ ∞ B := by dsimp [B]; fun_prop
  have hAd : HasDerivAt A (-(μ * protectedTorusCollarScale h μ / 2)) (0 : ℝ) := by
    convert! ((((hasDerivAt_id (0 : ℝ)).div_const 2).sin.const_mul
      (-protectedTorusCollarScale h μ)).const_mul μ).const_add RN using 1 <;>
      simp [A] <;> ring
  refine ⟨protectedTorusRotation_contDiffAt hA.contDiffAt hB.contDiffAt, ?_⟩
  apply protectedTorusRotation_fderiv_injective hAd
    ((hB.differentiable (by simp) (0 : ℝ)).hasDerivAt)
  · simpa [A] using d.radius_pos.ne'
  · left
    exact neg_ne_zero.mpr (ne_of_gt (div_pos (mul_pos d.coefficient_pos
      (protectedTorusCollarScale_positive d.height_pos d.coefficient_pos)) (by norm_num)))

private theorem protectedTorusRealLift_north_germ {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) :
    protectedTorusRealLift d =ᶠ[𝓝 (s,Real.pi)] protectedTorusNorthReal RN μ h := by
  obtain ⟨ε, hε, hεπ, hS⟩ := d.north_germ
  obtain ⟨α, hα, hR⟩ := d.meridian_north_germ
  have hu : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,Real.pi), p.2 ∈ Ioo (Real.pi-ε) (Real.pi+ε) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds (by constructor <;> linarith)
  have hz : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,Real.pi), h-α < -h * Real.cos p.2 :=
    (isOpen_lt continuous_const (continuous_const.mul (Real.continuous_cos.comp continuous_snd))).mem_nhds
      (by simp; linarith)
  filter_upwards [hu,hz] with p hp hz
  have hp0 : 0 < p.2 := by linarith [hp.1, Real.pi_pos]
  have hp2 : p.2 < 2*Real.pi := by linarith [hp.2, Real.pi_pos]
  rw [protectedTorusNorthReal_eq]
  change protectedTorusMap d.saddle d.meridian h
    (periodProjection (2*Real.pi) p.1, periodProjection (2*Real.pi) p.2) = _
  rw [protectedTorusMap_real_representative _ _ _ _ _ ⟨hp0.le,hp2⟩]
  by_cases hside : p.2 ≤ Real.pi
  · rw [if_pos hside]
    exact hS _ _ ⟨by linarith [hp.1], hside⟩
  · rw [if_neg hside]
    have hzh : -h * Real.cos p.2 ≤ h := by nlinarith [Real.neg_one_le_cos p.2, d.height_pos]
    apply protectedTorusConvexCylinder_north_eq d.height_pos d.coefficient_pos _
      ⟨le_of_not_ge hside, hp2.le⟩
    convert hR (-h * Real.cos p.2) ⟨hz.le,hzh⟩ using 1 <;> ring

private theorem protectedTorusRealLift_south_germ {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) :
    protectedTorusRealLift d =ᶠ[𝓝 (s,(0 : ℝ))] protectedTorusSouthReal RN μ h := by
  obtain ⟨ε, hε, hεπ, hS⟩ := d.south_germ
  obtain ⟨α, hα, hR⟩ := d.meridian_south_germ
  have hu : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,(0 : ℝ)), p.2 ∈ Ioo (-ε) ε :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds (by constructor <;> linarith)
  have hz : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,(0 : ℝ)), -h * Real.cos p.2 < -h+α :=
    (isOpen_lt (continuous_const.mul (Real.continuous_cos.comp continuous_snd)) continuous_const).mem_nhds
      (by simp; linarith)
  filter_upwards [hu,hz] with p hp hz
  rw [protectedTorusSouthReal_eq]
  change protectedTorusMap d.saddle d.meridian h
    (periodProjection (2*Real.pi) p.1, periodProjection (2*Real.pi) p.2) = _
  by_cases hside : 0 ≤ p.2
  · have hp2 : p.2 < 2*Real.pi := by linarith [hp.2, Real.pi_pos]
    rw [protectedTorusMap_real_representative _ _ _ _ _ ⟨hside,hp2⟩,
      if_pos (by linarith [hp.2])]
    exact hS _ _ ⟨hside,hp.2.le⟩
  · have hneg : p.2 < 0 := lt_of_not_ge hside
    have hphase : periodProjection (2*Real.pi) (p.2+2*Real.pi) =
        periodProjection (2*Real.pi) p.2 := AddCircle.coe_add_period (2*Real.pi) p.2
    have hpperiod : p.2+2*Real.pi ∈ Ico (0 : ℝ) (2*Real.pi) :=
      ⟨by linarith [hp.1,Real.pi_pos], by linarith⟩
    rw [← hphase, protectedTorusMap_real_representative _ _ _ _ _ hpperiod,
      if_neg (by linarith [hp.1,Real.pi_pos])]
    have hperiod : protectedTorusConvexCylinder d.meridian h
        (periodProjection (2*Real.pi) p.1,p.2+2*Real.pi) =
        protectedTorusConvexCylinder d.meridian h (periodProjection (2*Real.pi) p.1,p.2) := by
      simp only [protectedTorusConvexCylinder, Real.cos_add_two_pi]
    rw [hperiod]
    have hzh : -h ≤ -h * Real.cos p.2 := by nlinarith [Real.cos_le_one p.2, d.height_pos]
    apply protectedTorusConvexCylinder_south_eq d.height_pos d.coefficient_pos _
      ⟨by linarith [hp.1,Real.pi_pos],hneg.le⟩
    convert hR (-h * Real.cos p.2) ⟨hzh,hz.le⟩ using 1 <;> ring
private theorem protectedTorusRealLift_saddle_interior {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ (protectedTorusRealLift d) (s,u) ∧
      Function.Injective (fderiv ℝ (protectedTorusRealLift d) (s,u)) := by
  have he : protectedTorusRealLift d =ᶠ[𝓝 (s,u)] d.saddle ∘ revolutionCylinderProjection := by
    have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,u), p.2 ∈ Ioo (0 : ℝ) Real.pi :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds hu
    filter_upwards [hev] with p hp
    change protectedTorusMap d.saddle d.meridian h
      (periodProjection (2*Real.pi) p.1,periodProjection (2*Real.pi) p.2) = _
    rw [protectedTorusMap_real_representative _ _ _ _ _
      ⟨hp.1.le,by linarith [hp.2,Real.pi_pos]⟩,if_pos hp.2.le]
    rfl
  have hmem : revolutionCylinderProjection (s,u) ∈
      (univ : Set (AddCircle (2*Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi := ⟨mem_univ _,hu⟩
  have hS : ContMDiffAt nativeProductModel 𝓘(ℝ, Ambient) ∞ d.saddle
      (revolutionCylinderProjection (s,u)) :=
    d.saddle_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)
  have hP := revolutionCylinderProjection_contMDiff (s,u)
  have hcomp := hS.comp (s,u) hP
  have hs : ContDiffAt ℝ ∞ (d.saddle ∘ revolutionCylinderProjection) (s,u) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp.contDiffAt
  letI : FiniteDimensional ℝ (TangentSpace nativeProductModel (s,u)) :=
    inferInstanceAs (FiniteDimensional ℝ (ℝ × ℝ))
  have hPi : Function.Injective (mfderiv nativeProductModel nativeProductModel
      revolutionCylinderProjection (s,u)) :=
    (LinearMap.injective_iff_surjective (f :=
      (mfderiv nativeProductModel nativeProductModel revolutionCylinderProjection (s,u)).toLinearMap)).mpr
      (revolutionCylinderProjection_mfderiv_surjective (s,u))
  have hd := mfderiv_comp (s,u) (hS.mdifferentiableAt (by simp))
    (hP.mdifferentiableAt (by simp))
  have hi : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (d.saddle ∘ revolutionCylinderProjection) (s,u)) := by
    rw [hd]
    exact (d.saddle_immersion _ hmem).comp hPi
  have hi' : Function.Injective (fderiv ℝ (d.saddle ∘ revolutionCylinderProjection) (s,u)) := by
    unfold nativeProductModel at hi
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv] at hi
    exact hi
  refine ⟨hs.congr_of_eventuallyEq he, ?_⟩
  rw [he.fderiv_eq]
  exact hi'

private theorem protectedTorusRealLift_convex_interior {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) {u : ℝ}
    (hu : u ∈ Ioo Real.pi (2*Real.pi)) :
    ContDiffAt ℝ ∞ (protectedTorusRealLift d) (s,u) ∧
      Function.Injective (fderiv ℝ (protectedTorusRealLift d) (s,u)) := by
  have hsin : Real.sin u < 0 := by
    have ht := Real.sin_neg_of_neg_of_neg_pi_lt
      (show u-2*Real.pi < 0 by linarith [hu.2])
      (show -Real.pi < u-2*Real.pi by linarith [hu.1])
    simpa only [Real.sin_sub_two_pi] using ht
  have hcoslo : -1 < Real.cos u := by
    nlinarith [Real.sin_sq_add_cos_sq u, sq_pos_of_ne_zero hsin.ne]
  have hcoshi : Real.cos u < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq u, sq_pos_of_ne_zero hsin.ne]
  have hz : -h * Real.cos u ∈ Ioo (-h) h := by
    constructor <;> nlinarith [d.height_pos]
  let B : ℝ → ℝ := fun v => -h * Real.cos v
  let A : ℝ → ℝ := fun v => d.meridian (B v)
  have hB : ContDiff ℝ ∞ B := by dsimp [B]; fun_prop
  have hr : ContDiffAt ℝ ∞ d.meridian (B u) :=
    d.meridian_smooth.contDiffAt (isOpen_Ioo.mem_nhds hz)
  have hA : ContDiffAt ℝ ∞ A u := hr.comp u hB.contDiffAt
  have hBd : HasDerivAt B (h * Real.sin u) u := by
    convert! (Real.hasDerivAt_cos u).const_mul (-h) using 1 <;> simp [B] <;> ring
  have hAd : HasDerivAt A (deriv d.meridian (B u) * (h * Real.sin u)) u :=
    (hr.differentiableAt (by simp)).hasDerivAt.comp u hBd
  have hR : A u ≠ 0 := by
    have hx := d.meridian_exterior (B u) hz
    exact ne_of_gt (lt_trans d.radius_pos hx)
  have hi := protectedTorusRotation_fderiv_injective (s := s) hAd hBd hR
    (Or.inr (mul_ne_zero d.height_pos.ne' hsin.ne))
  have hs := protectedTorusRotation_contDiffAt (s := s) hA hB.contDiffAt
  have he : protectedTorusRealLift d =ᶠ[𝓝 (s,u)] protectedTorusRotation A B := by
    have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,u), p.2 ∈ Ioo Real.pi (2*Real.pi) :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds hu
    filter_upwards [hev] with p hp
    change protectedTorusMap d.saddle d.meridian h
      (periodProjection (2*Real.pi) p.1,periodProjection (2*Real.pi) p.2) = _
    rw [protectedTorusMap_real_representative _ _ _ _ _
      ⟨by linarith [hp.1,Real.pi_pos],hp.2⟩,if_neg (not_le.mpr hp.1)]
    simp only [protectedTorusConvexCylinder, revolutionEndCircleFull,
      revolutionCircleRadial_representative, protectedTorusRotation, A, B]
  refine ⟨hs.congr_of_eventuallyEq he, ?_⟩
  rw [he.fderiv_eq]
  exact hi

private theorem protectedTorusRealLift_smooth_rank {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (s : ℝ) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) (2*Real.pi)) :
    ContDiffAt ℝ ∞ (protectedTorusRealLift d) (s,u) ∧
      Function.Injective (fderiv ℝ (protectedTorusRealLift d) (s,u)) := by
  by_cases h0 : u = 0
  · subst u
    have he := protectedTorusRealLift_south_germ d s
    have ht := protectedTorusSouthReal_smooth_rank d s
    refine ⟨ht.1.congr_of_eventuallyEq he, ?_⟩
    rw [he.fderiv_eq]
    exact ht.2
  · rcases lt_trichotomy u Real.pi with hlt | heq | hgt
    · exact protectedTorusRealLift_saddle_interior d s
        ⟨lt_of_le_of_ne hu.1 (Ne.symm h0),hlt⟩
    · subst u
      have he := protectedTorusRealLift_north_germ d s
      have ht := protectedTorusNorthReal_smooth_rank d s
      refine ⟨ht.1.congr_of_eventuallyEq he, ?_⟩
      rw [he.fderiv_eq]
      exact ht.2
    · exact protectedTorusRealLift_convex_interior d s ⟨hgt,hu.2⟩

private theorem protectedTorus_circle_chart_zero (q : AddCircle (2*Real.pi)) :
    chartAt ℝ q q = (0 : ℝ) := by
  change (periodChart (2*Real.pi)).symm (-q+q) = 0
  rw [neg_add_cancel]
  have hz : periodChart (2*Real.pi) (0 : ℝ) = 0 := rfl
  rw [← hz, (periodChart (2*Real.pi)).left_inv (periodChart_zero_source _)]

private theorem protectedTorus_chart_zero (p : NonrigidTorusSource) :
    chartAt (ModelProd ℝ ℝ) p p = ((0 : ℝ),(0 : ℝ)) :=
  Prod.ext (protectedTorus_circle_chart_zero p.1) (protectedTorus_circle_chart_zero p.2)
private theorem protectedTorus_chart_lift {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (p : NonrigidTorusSource)
    (s u : ℝ) (hs : periodProjection (2*Real.pi) s = p.1)
    (hu : periodProjection (2*Real.pi) u = p.2) :
    (fun v : ℝ × ℝ => protectedTorusMap d.saddle d.meridian h
      ((chartAt (ModelProd ℝ ℝ) p).symm v)) =
      (fun v : ℝ × ℝ => protectedTorusRealLift d ((s,u)+v)) := by
  funext v
  have hc (q : AddCircle (2*Real.pi)) (a b : ℝ)
      (ha : periodProjection (2*Real.pi) a = q) :
      (chartAt ℝ q).symm b = periodProjection (2*Real.pi) (a+b) := by
    change (OAI.RawQuotientLie.addLeftChart (periodChart (2*Real.pi)) q).symm b = _
    rw [OAI.RawQuotientLie.addLeftChart_symm_apply, ← ha]
    exact (map_add (periodProjection (2*Real.pi)) a b).symm
  change protectedTorusMap d.saddle d.meridian h
    ((chartAt ℝ p.1).symm v.1,(chartAt ℝ p.2).symm v.2) = _
  rw [hc p.1 s v.1 hs, hc p.2 u v.2 hu]
  rfl

/-- Actual local representatives of the literal glued map are smooth and have
injective native differentials. Both seam ranks come from signed parabolic
collar derivatives, rather than the singular height parameter at an endpoint. -/
theorem protectedTorusMap_contMDiff_and_immersion_from_data {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (protectedTorusMap d.saddle d.meridian h) ∧
      ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (protectedTorusMap d.saddle d.meridian h) p) := by
  have hlocal (p : NonrigidTorusSource) :
      ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => protectedTorusMap d.saddle d.meridian h
        ((chartAt (ModelProd ℝ ℝ) p).symm v)) ((0 : ℝ),(0 : ℝ)) ∧
      Function.Injective (fderiv ℝ
        (fun v : ℝ × ℝ => protectedTorusMap d.saddle d.meridian h
          ((chartAt (ModelProd ℝ ℝ) p).symm v)) ((0 : ℝ),(0 : ℝ))) := by
    obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective p.1
    let u := (AddCircle.equivIco (2*Real.pi) 0 p.2).val
    have hu : u ∈ Ico (0 : ℝ) (2*Real.pi) := by
      simpa [u] using (AddCircle.equivIco (2*Real.pi) 0 p.2).property
    have hup : periodProjection (2*Real.pi) u = p.2 := AddCircle.coe_equivIco
    have ht := protectedTorusRealLift_smooth_rank d s hu
    rw [protectedTorus_chart_lift d p s u hs hup]
    have hsmooth : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => protectedTorusRealLift d ((s,u)+v))
        ((0 : ℝ),(0 : ℝ)) := by
      have hbase : ContDiffAt ℝ ∞ (protectedTorusRealLift d) ((s,u)+(0,0)) := by
        simpa using ht.1
      exact hbase.comp (0,0) (contDiffAt_const.add contDiffAt_id)
    refine ⟨hsmooth, ?_⟩
    simpa [fderiv_comp_add_left] using ht.2
  have hs : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (protectedTorusMap d.saddle d.meridian h) := by
    intro p
    rw [contMDiffAt_iff_source]
    have hr : range nativeProductModel = univ := ModelWithCorners.range_eq_univ nativeProductModel
    rw [hr]
    convert! (hlocal p).1.contMDiffAt.contMDiffWithinAt using 1 <;>
      simp [extChartAt, nativeProductModel, Function.comp_def, protectedTorus_circle_chart_zero]
  refine ⟨hs, fun p => ?_⟩
  rw [← nativeCompactEmbedding_chart_fderiv hs p, protectedTorus_chart_zero]
  exact (hlocal p).2
end
end TightVer401







