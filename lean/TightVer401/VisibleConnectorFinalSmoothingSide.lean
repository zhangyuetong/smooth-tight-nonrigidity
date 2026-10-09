import TightVer401.RelativeSaddleSmoothing
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Concrete fixed-domain seam side producers. No incoming inverse or carrier package is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A continuous scalar's strict sublevel has boundary only where the scalar
vanishes, within its actual open domain. -/
theorem visibleConnectorFinalSmoothing_sublevel_frontier_zero
    {B : Coord → ℝ} {V : Set Coord} (hV : IsOpen V) (hB : ContinuousOn B V) :
    ∀ x ∈ V ∩ frontier {y | B y < 0}, B x = 0 := by
  intro x hx
  have hc : ContinuousAt B x := (hB x hx.1).continuousAt (hV.mem_nhds hx.1)
  by_contra hz
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hm : {y | B y < 0} ∈ 𝓝 x := hc.eventually (gt_mem_nhds hn)
    have hi : x ∈ (frontier {y | B y < 0})ᶜ := by
      rw [compl_frontier_eq_union_interior]
      exact Or.inl (mem_interior_iff_mem_nhds.mpr hm)
    exact hi hx.2
  · have hm : {y | B y < 0}ᶜ ∈ 𝓝 x := by
      filter_upwards [hc.eventually (lt_mem_nhds hp)] with y hy
      exact not_lt.mpr hy.le
    have hi : x ∈ (frontier {y | B y < 0})ᶜ := by
      rw [compl_frontier_eq_union_interior]
      exact Or.inr (mem_interior_iff_mem_nhds.mpr hm)
    exact hi hx.2

private theorem finalSmoothing_normal_height_axis_partial
    {gamma : ℝ → ℂ} {B : Coord → ℝ} {V : Set Coord}
    (hgamma : ContDiff ℝ ∞ gamma) (hV : IsOpen V) (hB : ContDiffOn ℝ ∞ B V)
    (s : ℝ) (hs : seamComplexCoord (gamma s) ∈ V) :
    coordPartial 1 (fun q => B (seamNormalCoordinates gamma q)) (![s, 0] : Coord) =
      fderiv ℝ B (seamComplexCoord (gamma s))
        (seamComplexCoord (Complex.I * deriv gamma s)) := by
  have hdB : DifferentiableAt ℝ B (seamComplexCoord (gamma s)) :=
    ((hB _ hs).contDiffAt (hV.mem_nhds hs)).differentiableAt (by simp)
  have hdB0 : DifferentiableAt ℝ B (seamNormalCoordinates gamma (![s, 0] : Coord)) := by
    rwa [seamNormalCoordinates_central]
  have hc := hdB0.hasFDerivAt.comp (![s, 0] : Coord)
    ((seamNormalCoordinates_contDiff hgamma).differentiable (by simp) (![s, 0] : Coord)).hasFDerivAt
  simp only [seamNormalCoordinates_central] at hc
  rw [coordPartial]
  change fderiv ℝ (B ∘ seamNormalCoordinates gamma) (![s, 0] : Coord) (Pi.single 1 1) = _
  rw [hc.fderiv]
  change fderiv ℝ B (seamComplexCoord (gamma s))
    (fderiv ℝ (seamNormalCoordinates gamma) (![s, 0] : Coord) (Pi.single 1 1)) = _
  rw [seamNormalCoordinates_fderiv hgamma]
  simp

private theorem finalSmoothing_height_line_deriv {F : Coord → ℝ} {s t : ℝ}
    (hF : DifferentiableAt ℝ F (![s, t] : Coord)) :
    deriv (fun u => F (![s, u] : Coord)) t = coordPartial 1 F (![s, t] : Coord) := by
  have hpath : HasDerivAt (fun u : ℝ => (![s, u] : Coord)) (Pi.single 1 1 : Coord) t := by
    have he : (fun u : ℝ => (![s, u] : Coord)) = Function.update (![s, 0] : Coord) 1 := by
      funext u i
      fin_cases i <;> simp
    rw [he]
    exact hasDerivAt_update _ _ _
  exact (hF.hasFDerivAt.comp_hasDerivAt t hpath).deriv

/-- A uniform positive-normal classifier is CONSTRUCTED from the actual
negative inverse-height normal derivative. All smoothness is on V only. -/
theorem visibleConnectorFinalSmoothing_exists_canonical_side_threshold
    {L : ℝ} (hL : 0 < L) {gamma : ℝ → ℂ} {B : Coord → ℝ} {V : Set Coord}
    (hgamma : ContDiff ℝ ∞ gamma) (hperiod : Periodic gamma L)
    (hV : IsOpen V) (hB : ContDiffOn ℝ ∞ B V)
    (hseam : ∀ s, seamComplexCoord (gamma s) ∈ V)
    (hzero : ∀ s, B (seamComplexCoord (gamma s)) = 0)
    (hnormal : ∀ s, fderiv ℝ B (seamComplexCoord (gamma s))
      (seamComplexCoord (Complex.I * deriv gamma s)) < 0) :
    ∃ r > 0, ∀ s t, |t| ≤ r →
      seamNormalCoordinates gamma (![s, t] : Coord) ∈ V ∧
        (B (seamNormalCoordinates gamma (![s, t] : Coord)) < 0 ↔ 0 < t) := by
  let Phi := seamNormalCoordinates gamma
  let D : Set Coord := Phi ⁻¹' V
  let H : Coord → ℝ := fun q => B (Phi q)
  have hPhi : ContDiff ℝ ∞ Phi := seamNormalCoordinates_contDiff hgamma
  have hD : IsOpen D := hV.preimage hPhi.continuous
  have hH : ContDiffOn ℝ ∞ H D := hB.comp hPhi.contDiffOn (fun _ hx => hx)
  have hpartial : ContinuousOn (coordPartial 1 H) D :=
    (partial_contDiffOn hH hD 1).continuousOn
  let Z : Set Coord := D ∩ (coordPartial 1 H) ⁻¹' Iio 0
  have hZ : IsOpen Z := hpartial.isOpen_inter_preimage hD isOpen_Iio
  have haxis (s : ℝ) : (![s, 0] : Coord) ∈ Z := by
    refine ⟨?_, ?_⟩
    · change seamNormalCoordinates gamma (![s, 0] : Coord) ∈ V
      rw [seamNormalCoordinates_central]
      exact hseam s
    · change coordPartial 1 (fun q => B (seamNormalCoordinates gamma q)) (![s, 0] : Coord) < 0
      rw [finalSmoothing_normal_height_axis_partial hgamma hV hB s (hseam s)]
      exact hnormal s
  obtain ⟨r, hr, hstrip⟩ := seam_compact_axis_open_collar
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) L)) hZ (fun s _ => haxis s)
  have hlocal (s : ℝ) (hs : s ∈ Icc 0 L) (t : ℝ) (ht : |t| ≤ r) :
      Phi (![s, t] : Coord) ∈ V ∧ (H (![s, t] : Coord) < 0 ↔ 0 < t) := by
    have hmap : MapsTo (fun u : ℝ => (![s, u] : Coord)) (Icc (-r) r) D := by
      intro u hu
      exact (hstrip s hs u (abs_le.mpr hu)).1
    have hpath : Continuous (fun u : ℝ => (![s, u] : Coord)) := by
      apply continuous_pi
      intro i
      fin_cases i <;> first | exact continuous_const | exact continuous_id
    have hcont : ContinuousOn (fun u => H (![s, u] : Coord)) (Icc (-r) r) :=
      hH.continuousOn.comp hpath.continuousOn hmap
    have hanti : StrictAntiOn (fun u => H (![s, u] : Coord)) (Icc (-r) r) :=
      strictAntiOn_of_deriv_neg (convex_Icc (-r) r) hcont (by
        intro u hu
        have hu' := interior_subset hu
        have hq := hstrip s hs u (abs_le.mpr hu')
        rw [finalSmoothing_height_line_deriv
          (((hH _ hq.1).contDiffAt (hD.mem_nhds hq.1)).differentiableAt (by simp))]
        exact hq.2)
    have h0 : H (![s, 0] : Coord) = 0 := by
      simpa only [H, Phi, seamNormalCoordinates_central] using hzero s
    refine ⟨(hstrip s hs t ht).1, ?_⟩
    constructor
    · intro hneg
      by_contra hpos
      have ht0 : t ≤ 0 := not_lt.mp hpos
      rcases lt_or_eq_of_le ht0 with hlt | heq
      · have hgt := hanti (abs_le.mp ht) ⟨by linarith, hr.le⟩ hlt
        change H (![s, 0] : Coord) < H (![s, t] : Coord) at hgt
        rw [h0] at hgt
        linarith
      · rw [heq, h0] at hneg
        exact lt_irrefl 0 hneg
    · intro hpos
      have hlt := hanti ⟨by linarith, hr.le⟩ (abs_le.mp ht) hpos
      change H (![s, t] : Coord) < H (![s, 0] : Coord) at hlt
      rwa [h0] at hlt
  refine ⟨r, hr, ?_⟩
  intro s t ht
  let sm := toIcoMod hL 0 s
  have hsm : sm ∈ Icc 0 L := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hp : Periodic (fun a => Phi (![a, t] : Coord)) L := by
    intro a
    exact seamNormalCoordinates_periodic hperiod (![a, t] : Coord)
  have heq := seam_periodic_eq_representative hL hp s
  change Phi (![s, t] : Coord) = Phi (![sm, t] : Coord) at heq
  obtain ⟨hm, hsign⟩ := hlocal sm hsm t ht
  constructor
  · change Phi (![s, t] : Coord) ∈ V
    rw [heq]
    exact hm
  · change B (Phi (![s, t] : Coord)) < 0 ↔ 0 < t
    rw [heq]
    exact hsign

end
end TightVer401
