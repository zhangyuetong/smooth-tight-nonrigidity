import TightVer401.ProtectedTorusMapDefinitions

/-! Injection and range of the literal quotient torus map, from ordinary
closed-cylinder producer data. No pending root assembly proof is imported. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem protectedTorus_radial_horizontal_norm
    (R z : ℝ) (q : AddCircle (2 * Real.pi)) :
    ‖corrugatedAmbientHorizontalCLM
      (R • revolutionCircleRadial q + z • revolutionAxis)‖ = |R| := by
  have hs : ‖corrugatedAmbientHorizontalCLM
      (R • revolutionCircleRadial q + z • revolutionAxis)‖ ^ 2 = R ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [corrugatedAmbientHorizontalCLM_apply, corrugatedAmbientHorizontal,
      revolutionCircleRadial, revolutionAxis, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul, mul_zero, add_zero]
    have htrig := congrArg (fun x : ℝ => R ^ 2 * x) (Real.Angle.cos_sq_add_sin_sq q)
    nlinarith [htrig]
  nlinarith [norm_nonneg (corrugatedAmbientHorizontalCLM
    (R • revolutionCircleRadial q + z • revolutionAxis)), abs_nonneg R, sq_abs R]

private theorem protectedTorus_saddle_endpoints {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (q : AddCircle (2 * Real.pi)) :
    d.saddle (q, 0) = RN • revolutionCircleRadial q + (-h) • revolutionAxis ∧
      d.saddle (q, Real.pi) = RN • revolutionCircleRadial q + h • revolutionAxis := by
  obtain ⟨εs, hεs, _, hs⟩ := d.south_germ
  obtain ⟨εn, hεn, _, hn⟩ := d.north_germ
  constructor
  · simpa [protectedTorusSouthCollar] using hs q 0 ⟨le_rfl, hεs.le⟩
  · simpa [protectedTorusNorthCollar] using
      hn q Real.pi ⟨by linarith, le_rfl⟩

private theorem protectedTorus_meridian_endpoints {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    d.meridian (-h) = RN ∧ d.meridian h = RN := by
  obtain ⟨εs, hεs, hs⟩ := d.meridian_south_germ
  obtain ⟨εn, hεn, hn⟩ := d.meridian_north_germ
  constructor
  · simpa using hs (-h) ⟨le_rfl, by linarith⟩
  · simpa using hn h ⟨by linarith, le_rfl⟩

private theorem protectedTorus_saddle_closed_radius {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Icc 0 Real.pi) :
    ‖corrugatedAmbientHorizontalCLM (d.saddle (q, u))‖ ≤ RN := by
  by_cases hu0 : u = 0
  · rw [hu0, (protectedTorus_saddle_endpoints d q).1,
      protectedTorus_radial_horizontal_norm, abs_of_pos d.radius_pos]
  · by_cases huπ : u = Real.pi
    · rw [huπ, (protectedTorus_saddle_endpoints d q).2,
        protectedTorus_radial_horizontal_norm, abs_of_pos d.radius_pos]
    · exact (d.saddle_radius (q, u)
        ⟨mem_univ _, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),
          lt_of_le_of_ne hu.2 huπ⟩⟩).le

private theorem protectedTorus_cos_injective :
    InjOn Real.cos (Icc Real.pi (2 * Real.pi)) := by
  intro u hu v hv he
  have hU : 2 * Real.pi - u ∈ Icc 0 Real.pi :=
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hV : 2 * Real.pi - v ∈ Icc 0 Real.pi :=
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hsame := Real.injOn_cos hU hV (by simpa only [Real.cos_two_pi_sub] using he)
  linarith

private theorem protectedTorus_convex_height_interior {h u : ℝ}
    (hh : 0 < h) (hu : u ∈ Ioo Real.pi (2 * Real.pi)) :
    -h * Real.cos u ∈ Ioo (-h) h := by
  let v := 2 * Real.pi - u
  have hv0 : 0 < v := by dsimp [v]; linarith [hu.2]
  have hvπ : v < Real.pi := by dsimp [v]; linarith [hu.1]
  have hlo : -1 < Real.cos u := by
    have hx := Real.strictAntiOn_cos ⟨hv0.le, hvπ.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ hvπ
    simpa only [v, Real.cos_two_pi_sub, Real.cos_pi] using hx
  have hhi : Real.cos u < 1 := by
    have hx := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨hv0.le, hvπ.le⟩ hv0
    simpa only [v, Real.cos_two_pi_sub, Real.cos_zero] using hx
  constructor <;> nlinarith

private theorem protectedTorus_convex_closed_radius_pos {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) {u : ℝ}
    (hu : u ∈ Icc Real.pi (2 * Real.pi)) :
    0 < d.meridian (-h * Real.cos u) := by
  by_cases huπ : u = Real.pi
  · simpa [huπ, (protectedTorus_meridian_endpoints d).2] using d.radius_pos
  · by_cases hu2π : u = 2 * Real.pi
    · simpa [hu2π, (protectedTorus_meridian_endpoints d).1] using d.radius_pos
    · exact d.radius_pos.trans (d.meridian_exterior _
        (protectedTorus_convex_height_interior d.height_pos
          ⟨lt_of_le_of_ne hu.1 (Ne.symm huπ), lt_of_le_of_ne hu.2 hu2π⟩))

private theorem protectedTorus_convex_injective {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    InjOn (protectedTorusConvexCylinder d.meridian h)
      ((univ : Set (AddCircle (2 * Real.pi))) ×ˢ Icc Real.pi (2 * Real.pi)) := by
  intro p hp q hq he
  have hz : -h * Real.cos p.2 = -h * Real.cos q.2 := by
    have ht := congrArg (fun v : Ambient => v 2) he
    simpa [protectedTorusConvexCylinder, revolutionEndCircleFull,
      revolutionCircleRadial, revolutionAxis] using ht
  have hc : Real.cos p.2 = Real.cos q.2 :=
    (mul_left_cancel₀ (neg_ne_zero.mpr (ne_of_gt d.height_pos))) hz
  have huv : p.2 = q.2 := protectedTorus_cos_injective hp.2 hq.2 hc
  have hr : d.meridian (-h * Real.cos p.2) ≠ 0 :=
    ne_of_gt (protectedTorus_convex_closed_radius_pos d hp.2)
  have hc0 := congrArg (fun v : Ambient => v 0) he
  have hs0 := congrArg (fun v : Ambient => v 1) he
  have hc1 : d.meridian (-h * Real.cos p.2) * Real.Angle.cos p.1 =
      d.meridian (-h * Real.cos q.2) * Real.Angle.cos q.1 := by
    simpa [protectedTorusConvexCylinder, revolutionEndCircleFull,
      revolutionCircleRadial, revolutionAxis] using hc0
  have hs1 : d.meridian (-h * Real.cos p.2) * Real.Angle.sin p.1 =
      d.meridian (-h * Real.cos q.2) * Real.Angle.sin q.1 := by
    simpa [protectedTorusConvexCylinder, revolutionEndCircleFull,
      revolutionCircleRadial, revolutionAxis] using hs0
  rw [← huv] at hc1 hs1
  exact Prod.ext (revolutionAngle_cos_sin_injective
    ((mul_left_cancel₀ hr) hc1) ((mul_left_cancel₀ hr) hs1)) huv

private theorem protectedTorus_saddle_ne_convex_interior {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h)
    {q t : AddCircle (2 * Real.pi)} {u v : ℝ}
    (hu : u ∈ Icc 0 Real.pi) (hv : v ∈ Ioo Real.pi (2 * Real.pi)) :
    d.saddle (q, u) ≠ protectedTorusConvexCylinder d.meridian h (t, v) := by
  intro he
  have hs := protectedTorus_saddle_closed_radius d q hu
  have hr := d.meridian_exterior _ (protectedTorus_convex_height_interior d.height_pos hv)
  have hp : 0 < d.meridian (-h * Real.cos v) := d.radius_pos.trans hr
  rw [he, protectedTorusConvexCylinder, revolutionEndCircleFull,
    protectedTorus_radial_horizontal_norm, abs_of_pos hp] at hs
  exact (not_le_of_gt hr) hs

private theorem protectedTorus_seams {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) (q : AddCircle (2 * Real.pi)) :
    protectedTorusConvexCylinder d.meridian h (q, Real.pi) = d.saddle (q, Real.pi) ∧
      protectedTorusConvexCylinder d.meridian h (q, 2 * Real.pi) = d.saddle (q, 0) := by
  constructor
  · simp [protectedTorusConvexCylinder, revolutionEndCircleFull,
      (protectedTorus_meridian_endpoints d).2, (protectedTorus_saddle_endpoints d q).2]
  · simp [protectedTorusConvexCylinder, revolutionEndCircleFull,
      (protectedTorus_meridian_endpoints d).1, (protectedTorus_saddle_endpoints d q).1]

private theorem protectedTorusMap_coe_phase
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ico 0 (2 * Real.pi)) :
    protectedTorusMap S r h (q, (u : AddCircle (2 * Real.pi))) =
      if u ≤ Real.pi then S (q, u) else protectedTorusConvexCylinder r h (q, u) := by
  have hrep : AddCircle.equivIco (2 * Real.pi) 0 (u : AddCircle (2 * Real.pi)) =
      ⟨u, by simpa using hu⟩ := AddCircle.equivIco_coe_eq (by simpa using hu)
  simp only [protectedTorusMap, hrep]

/-- Global injection of the actual quotient torus map, with mixed branches
separated by their actual horizontal radii. -/
theorem protectedTorusMap_injective_from_data {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    Function.Injective (protectedTorusMap d.saddle d.meridian h) := by
  intro p q he
  let u : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  let v : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 q.2).val
  have hu : u ∈ Ico 0 (2 * Real.pi) := by
    simpa [u] using (AddCircle.equivIco (2 * Real.pi) 0 p.2).property
  have hv : v ∈ Ico 0 (2 * Real.pi) := by
    simpa [v] using (AddCircle.equivIco (2 * Real.pi) 0 q.2).property
  have hup : (u : AddCircle (2 * Real.pi)) = p.2 := AddCircle.coe_equivIco
  have hvq : (v : AddCircle (2 * Real.pi)) = q.2 := AddCircle.coe_equivIco
  change (if u ≤ Real.pi then d.saddle (p.1, u)
    else protectedTorusConvexCylinder d.meridian h (p.1, u)) =
    (if v ≤ Real.pi then d.saddle (q.1, v)
      else protectedTorusConvexCylinder d.meridian h (q.1, v)) at he
  by_cases huπ : u ≤ Real.pi
  · by_cases hvπ : v ≤ Real.pi
    · simp only [if_pos huπ, if_pos hvπ] at he
      have hsame := d.saddle_injective ⟨mem_univ _, ⟨hu.1, huπ⟩⟩
        ⟨mem_univ _, ⟨hv.1, hvπ⟩⟩ he
      apply Prod.ext
      · exact congrArg (fun z : AddCircle (2 * Real.pi) × ℝ => z.1) hsame
      · rw [← hup, ← hvq]
        exact congrArg (fun z : AddCircle (2 * Real.pi) × ℝ =>
          (z.2 : AddCircle (2 * Real.pi))) hsame
    · simp only [if_pos huπ, if_neg hvπ] at he
      exact False.elim (protectedTorus_saddle_ne_convex_interior d
        ⟨hu.1, huπ⟩ ⟨lt_of_not_ge hvπ, hv.2⟩ he)
  · by_cases hvπ : v ≤ Real.pi
    · simp only [if_neg huπ, if_pos hvπ] at he
      exact False.elim (protectedTorus_saddle_ne_convex_interior d
        ⟨hv.1, hvπ⟩ ⟨lt_of_not_ge huπ, hu.2⟩ he.symm)
    · simp only [if_neg huπ, if_neg hvπ] at he
      have hsame := protectedTorus_convex_injective d
        ⟨mem_univ _, ⟨(lt_of_not_ge huπ).le, hu.2.le⟩⟩
        ⟨mem_univ _, ⟨(lt_of_not_ge hvπ).le, hv.2.le⟩⟩ he
      apply Prod.ext
      · exact congrArg (fun z : AddCircle (2 * Real.pi) × ℝ => z.1) hsame
      · rw [← hup, ← hvq]
        exact congrArg (fun z : AddCircle (2 * Real.pi) × ℝ =>
          (z.2 : AddCircle (2 * Real.pi))) hsame

/-- The image is exactly the union of the two literal closed cylinder images;
the phase 2π endpoint is represented by phase zero using the actual south seam. -/
theorem protectedTorusMap_range_from_data {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    range (protectedTorusMap d.saddle d.meridian h) =
      d.saddle '' (univ ×ˢ Icc (0 : ℝ) Real.pi) ∪
      protectedTorusConvexCylinder d.meridian h ''
        (univ ×ˢ Icc Real.pi (2 * Real.pi)) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p, rfl⟩
    let u : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
    have hu : u ∈ Ico 0 (2 * Real.pi) := by
      simpa [u] using (AddCircle.equivIco (2 * Real.pi) 0 p.2).property
    by_cases hupi : u ≤ Real.pi
    · exact Or.inl ⟨(p.1, u), ⟨mem_univ _, ⟨hu.1, hupi⟩⟩,
        by change d.saddle (p.1, u) = (if u ≤ Real.pi then
             d.saddle (p.1, u) else protectedTorusConvexCylinder d.meridian h (p.1, u))
           rw [if_pos hupi]⟩
    · exact Or.inr ⟨(p.1, u),
        ⟨mem_univ _, ⟨(lt_of_not_ge hupi).le, hu.2.le⟩⟩,
        by change protectedTorusConvexCylinder d.meridian h (p.1, u) =
             (if u ≤ Real.pi then d.saddle (p.1, u)
               else protectedTorusConvexCylinder d.meridian h (p.1, u))
           rw [if_neg hupi]⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have hu : p.2 ∈ Ico 0 (2 * Real.pi) :=
        ⟨hp.2.1, lt_of_le_of_lt hp.2.2 (by linarith [Real.pi_pos])⟩
      refine ⟨(p.1, (p.2 : AddCircle (2 * Real.pi))), ?_⟩
      rw [protectedTorusMap_coe_phase d.saddle d.meridian h p.1 hu,
        if_pos hp.2.2]
    · by_cases hp2 : p.2 = 2 * Real.pi
      · refine ⟨(p.1, (0 : AddCircle (2 * Real.pi))), ?_⟩
        have h0 : (0 : ℝ) ∈ Ico 0 (2 * Real.pi) :=
          ⟨le_rfl, by positivity⟩
        have hm := protectedTorusMap_coe_phase d.saddle d.meridian h p.1 h0
        simp only [if_pos Real.pi_pos.le] at hm
        change protectedTorusMap d.saddle d.meridian h (p.1, 0) =
          protectedTorusConvexCylinder d.meridian h (p.1, p.2)
        rw [hp2, (protectedTorus_seams d p.1).2]
        exact hm
      · have hu : p.2 ∈ Ico 0 (2 * Real.pi) :=
          ⟨le_trans Real.pi_pos.le hp.2.1, lt_of_le_of_ne hp.2.2 hp2⟩
        refine ⟨(p.1, (p.2 : AddCircle (2 * Real.pi))), ?_⟩
        rw [protectedTorusMap_coe_phase d.saddle d.meridian h p.1 hu]
        change (if p.2 ≤ Real.pi then d.saddle (p.1, p.2)
          else protectedTorusConvexCylinder d.meridian h (p.1, p.2)) =
          protectedTorusConvexCylinder d.meridian h (p.1, p.2)
        by_cases hppi : p.2 ≤ Real.pi
        · have he : p.2 = Real.pi := le_antisymm hppi hp.2.1
          rw [if_pos hppi, he, (protectedTorus_seams d p.1).1]
        · rw [if_neg hppi]

end
end TightVer401
