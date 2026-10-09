import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns
import TightVer401.SeamPeriodicity

/-! Compact local-domain estimates for the actual incoming ruling.  Smoothness
of the ruling is used only on its actual open Omega.  All real-parameter
conclusions are transported by literal periodicity, not by a global smooth
extension.  No side, source order or smoothing package is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingCarrier_compact_joint_strip {L : ℝ}
    {D : Set (ℝ × ℝ)} {F : (ℝ × ℝ) × ℝ → Coord} {U : Set Coord}
    (hD : IsOpen D) (hU : IsOpen U)
    (hF : ContinuousOn F {z | z.1 ∈ D})
    (haxis : ∀ s, (0, s) ∈ D) (hFU : ∀ s, F ((0, s), 0) ∈ U) :
    ∃ r > 0, ∀ rho s t, s ∈ Icc (0 : ℝ) L → |rho| < r → |t| < r →
      (rho, s) ∈ D ∧ F ((rho, s), t) ∈ U := by
  let K : Set ((ℝ × ℝ) × ℝ) := (fun s : ℝ => ((0, s), 0)) '' Icc 0 L
  have hpath : Continuous (fun s : ℝ => (((0 : ℝ), s), (0 : ℝ))) :=
    (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hK : IsCompact K := isCompact_Icc.image hpath
  have hDom : IsOpen {z : (ℝ × ℝ) × ℝ | z.1 ∈ D} := hD.preimage continuous_fst
  let Z := {z : (ℝ × ℝ) × ℝ | z.1 ∈ D} ∩ F ⁻¹' U
  have hZ : IsOpen Z := hF.isOpen_inter_preimage hDom hU
  have hKZ : K ⊆ Z := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨haxis s, hFU s⟩
  obtain ⟨r, hr, hrZ⟩ := hK.exists_cthickening_subset_open hZ hKZ
  refine ⟨r, hr, ?_⟩
  intro rho s t hs hρ ht
  apply hrZ
  apply Metric.thickening_subset_cthickening r K
  apply Metric.mem_thickening_iff.mpr
  refine ⟨((0, s), 0), ⟨s, hs, rfl⟩, ?_⟩
  simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
    max_eq_left (abs_nonneg rho)] using max_lt hρ ht

/-- Joint local continuity constructs one actual domain strip and height
margin.  Every real phase is covered by the SAME periodic ruling. -/
theorem visibleConnectorIncomingGinCarrier_exists_ruling_strip {L : ℝ} (hL : 0 < L)
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)} {U : Set Coord}
    (hp : Continuous p) (hw0 : Continuous w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hOmega : IsOpen Omega) (hw : ContinuousOn w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hOmegaL : ∀ rho s, (rho, s + L) ∈ Omega ↔ (rho, s) ∈ Omega)
    (hU : IsOpen U) (hpU : ∀ s, p s ∈ U) :
    ∃ r > 0, ∀ rho s t, |rho| < r → |t| < r →
      (rho, s) ∈ Omega ∧ p s + rho • w0 s + t • w (rho, s) ∈ U := by
  let F : (ℝ × ℝ) × ℝ → Coord := fun z =>
    p z.1.2 + z.1.1 • w0 z.1.2 + z.2 • w z.1
  have hs : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) := continuous_snd.comp continuous_fst
  have hρ : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.1) := continuous_fst.comp continuous_fst
  have hww : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => w z.1) {z | z.1 ∈ Omega} :=
    hw.comp continuous_fst.continuousOn (fun _ hz => hz)
  have hF : ContinuousOn F {z | z.1 ∈ Omega} :=
    ((hp.comp hs).continuousOn.add
      (hρ.continuousOn.smul (hw0.comp hs).continuousOn)).add
      (continuous_snd.continuousOn.smul hww)
  have hFU (s : ℝ) : F ((0, s), 0) ∈ U := by
    simpa only [F, zero_smul, add_zero] using hpU s
  obtain ⟨r, hr, hstrip⟩ := incomingCarrier_compact_joint_strip hOmega hU hF haxis hFU
  refine ⟨r, hr, ?_⟩
  intro rho s t hρ ht
  let sm := toIcoMod hL 0 s
  have hsm : sm ∈ Icc (0 : ℝ) L := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hlocal := hstrip rho sm t hsm hρ ht
  have hOp : Periodic (fun x : ℝ => (rho, x) ∈ Omega) L :=
    fun x => propext (hOmegaL rho x)
  have hΩeq := seam_periodic_eq_representative hL hOp s
  have hFp : Periodic (fun x : ℝ => p x + rho • w0 x + t • w (rho, x)) L := by
    intro x
    rw [hpL x, hw0L x, hwL rho x]
  have hFeq := seam_periodic_eq_representative hL hFp s
  refine ⟨?_, ?_⟩
  · rw [hΩeq]
    exact hlocal.1
  · rw [hFeq]
    exact hlocal.2

/-- Uniform convergence of the actual periodic inverse height to zero uses
only continuity on its ACTUAL open domain around the central axis. -/
theorem visibleConnectorIncomingGinCarrier_exists_height_bound {L : ℝ} (hL : 0 < L)
    {b : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hb : ContinuousOn b D) (haxis : ∀ s, (0, s) ∈ D)
    (hb0 : ∀ s, b (0, s) = 0) (hbL : ∀ rho, Periodic (fun s => b (rho, s)) L)
    {r : ℝ} (hr : 0 < r) :
    ∃ delta > 0, ∀ rho s, |rho| < delta → |b (rho, s)| < r := by
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := (isCompact_singleton (0 : ℝ)).prod isCompact_Icc
  let Z := D ∩ b ⁻¹' Ioo (-r) r
  have hZ : IsOpen Z := hb.isOpen_inter_preimage hD isOpen_Ioo
  have hKZ : K ⊆ Z := by
    intro z hz
    have hz0 : z.1 = 0 := mem_singleton_iff.mp hz.1
    have he : z = (0, z.2) := Prod.ext hz0 rfl
    rw [he]
    exact ⟨haxis z.2, by rw [hb0]; exact ⟨by linarith, hr⟩⟩
  obtain ⟨delta, hd, hdZ⟩ := hK.exists_cthickening_subset_open hZ hKZ
  refine ⟨delta, hd, ?_⟩
  intro rho s hρ
  let sm := toIcoMod hL 0 s
  have hsm : sm ∈ Icc (0 : ℝ) L := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hm : (rho, sm) ∈ Z := by
    apply hdZ
    apply Metric.thickening_subset_cthickening delta K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, sm), ⟨mem_singleton _, hsm⟩, ?_⟩
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      max_eq_left (abs_nonneg rho)] using hρ
  have heq := seam_periodic_eq_representative hL (hbL rho) s
  rw [heq]
  exact abs_lt.mpr hm.2

/-- The entire closed height interval from b(rho,s) to zero remains inside
the incoming domain, at EVERY real phase.  No phase closeness is needed. -/
theorem visibleConnectorIncomingGinCarrier_exists_negative_strip {L : ℝ} (hL : 0 < L)
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega D : Set (ℝ × ℝ)}
    {b : ℝ × ℝ → ℝ} {U : Set Coord}
    (hp : Continuous p) (hw0 : Continuous w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hOmega : IsOpen Omega) (hw : ContinuousOn w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hOmegaL : ∀ rho s, (rho, s + L) ∈ Omega ↔ (rho, s) ∈ Omega)
    (hU : IsOpen U) (hpU : ∀ s, p s ∈ U)
    (hD : IsOpen D) (hb : ContinuousOn b D) (hbaxis : ∀ s, (0, s) ∈ D)
    (hb0 : ∀ s, b (0, s) = 0) (hbL : ∀ rho, Periodic (fun s => b (rho, s)) L) :
    ∃ delta > 0, ∀ rho s x t, |rho| < delta → t ∈ Icc (b (rho, s)) 0 →
      (rho, x) ∈ Omega ∧ p x + rho • w0 x + t • w (rho, x) ∈ U := by
  obtain ⟨r, hr, hstrip⟩ := visibleConnectorIncomingGinCarrier_exists_ruling_strip hL
    hp hw0 hpL hw0L hwL hOmega hw haxis hOmegaL hU hpU
  obtain ⟨db, hdb, hbsmall⟩ := visibleConnectorIncomingGinCarrier_exists_height_bound hL
    hD hb hbaxis hb0 hbL hr
  refine ⟨min r db, lt_min hr hdb, ?_⟩
  intro rho s x t hρ ht
  have hbr : |b (rho, s)| < r := hbsmall rho s (lt_of_lt_of_le hρ (min_le_right _ _))
  have htr : |t| < r := by
    rw [abs_of_nonpos ht.2]
    have hbl := (abs_lt.mp hbr).1
    linarith [ht.1]
  exact hstrip rho x t (lt_of_lt_of_le hρ (min_le_left _ _)) htr

end
end TightVer401
