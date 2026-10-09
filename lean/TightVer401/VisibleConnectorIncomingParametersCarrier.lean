import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.VisibleConnectorIncomingParametersHeight

/-! Actual open incoming-domain margin for a joint periodic source/ruling
family. Both displacement and lower old height are bounded before choosing
rho; the whole negative strip, not only its lower curve, remains in GinU. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A compact central period inside the actual open U produces one source
margin valid for every real phase and every small transverse old height. -/
theorem visibleConnectorIncomingParameters_uniform_source_domain
    {L : ℝ} (hL : 0 < L) {P W : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} {U : Set Coord}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hW : ContDiffOn ℝ ∞ W Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hU : IsOpen U) (hcentral : ∀ s, P (0, s) ∈ U) :
    ∃ delta > 0, ∀ rho s u, |rho| < delta → |u| ≤ delta →
      P (rho, s) + u • W (rho, s) ∈ U := by
  let H : (ℝ × ℝ) × ℝ → Coord := fun z => P (z.1.1, z.2) + z.1.2 • W (z.1.1, z.2)
  have hnear : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ s ∈ Icc (0 : ℝ) L, H (z, s) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hpath : Continuous (fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2)) :=
      (continuous_fst.fst).prodMk continuous_snd
    have hPc : ContinuousAt P (0, s) :=
      (hP.continuousOn _ (haxis s)).continuousAt (hOmega.mem_nhds (haxis s))
    have hWc : ContinuousAt W (0, s) :=
      (hW.continuousOn _ (haxis s)).continuousAt (hOmega.mem_nhds (haxis s))
    have hPpath : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => P (z.1.1, z.2))
        (((0 : ℝ), (0 : ℝ)), s) := hPc.comp_of_eq (f := fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2))
          (x := (((0 : ℝ), (0 : ℝ)), s)) hpath.continuousAt rfl
    have hWpath : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => W (z.1.1, z.2))
        (((0 : ℝ), (0 : ℝ)), s) := hWc.comp_of_eq (f := fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2))
          (x := (((0 : ℝ), (0 : ℝ)), s)) hpath.continuousAt rfl
    have hUcoord : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => z.1.2)
        (((0 : ℝ), (0 : ℝ)), s) := (continuous_fst.snd).continuousAt
    have hHc : ContinuousAt H (((0 : ℝ), (0 : ℝ)), s) :=
      hPpath.add (hUcoord.smul hWpath)
    apply hHc.eventually
    apply hU.mem_nhds
    simpa [H] using hcentral s
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro rho s u hrho hu
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have hmem : (rho, u) ∈ ball ((0 : ℝ), (0 : ℝ)) r := by
    rw [mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (hrho.trans (half_lt_self hr)) (hu.trans_lt (half_lt_self hr))
  have h := hball hmem (s - n • L) ⟨hn.1, hn.2.le⟩
  change P (rho, s - n • L) + u • W (rho, s - n • L) ∈ U at h
  rw [(hPL rho).sub_zsmul_eq n, (hWL rho).sub_zsmul_eq n] at h
  exact h

/-- Selecting rho below both the constructed carrier margin and the SAME-e
height margin retains the ENTIRE lower-negative strip in the actual U. -/
theorem visibleConnectorIncomingParameters_exists_rho_negative_strip
    {L : ℝ} [hL : Fact (0 < L)] {p : ℝ → Coord}
    {P W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)} {U : Set Coord}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hW : ContDiffOn ℝ ∞ W Omega) (hOmegaAxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hU : IsOpen U) (hcentral : ∀ s, P (0, s) ∈ U)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hD : IsOpen (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞ (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hbL : ∀ rho, Periodic (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ rho > 0, rho < bound ∧ ∀ s u,
      (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 ≤ u → u ≤ 0 →
      P (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) +
        u • W (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) ∈ U := by
  obtain ⟨carrier, hc, hsource⟩ := visibleConnectorIncomingParameters_uniform_source_domain
    hL.out hOmega hP hW hOmegaAxis hPL hWL hU hcentral
  obtain ⟨height, hh, hsmall⟩ :=
    visibleConnectorIncomingParameters_uniform_height_small e hD hb haxis hb0 hbL hc
  let rho := min bound (min carrier height) / 2
  have hmin : 0 < min bound (min carrier height) := lt_min hbound (lt_min hc hh)
  have hrho : 0 < rho := half_pos hmin
  have hlt : rho < min bound (min carrier height) := half_lt_self hmin
  have hbnd : rho < bound := hlt.trans_le (min_le_left _ _)
  have hrest : rho < min carrier height := hlt.trans_le (min_le_right _ _)
  have hrc : |rho| < carrier := by simpa [abs_of_pos hrho] using hrest.trans_le (min_le_left _ _)
  have hrh : |rho| < height := by simpa [abs_of_pos hrho] using hrest.trans_le (min_le_right _ _)
  refine ⟨rho, hrho, hbnd, ?_⟩
  intro s u hbu hu
  apply hsource rho (visibleConnectorDisplacedRealPhase e p (rho, s)) u hrc
  have hbs := hsmall rho s hrh
  rw [abs_of_nonpos hu]
  have hlo := (abs_lt.mp hbs).1
  linarith

end
end TightVer401


