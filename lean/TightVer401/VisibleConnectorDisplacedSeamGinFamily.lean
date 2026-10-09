import TightVer401.VisibleConnectorUniformAngle

/-! Ordinary analytic inputs for the ACTUAL displaced Gin family. The gradient
is smooth on the preimage of the SAME open U. The literal visible ruling is
smooth on the DERIVED open norm-margin subdomain; no global Gin extension or
visibility bound away from that domain is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def visibleConnectorGinDisplacedPosition (p w0 : ℝ → Coord) (z : ℝ × ℝ) : Coord :=
  p z.2 + z.1 • w0 z.2

def visibleConnectorGinDisplacedGradient (Gin : Coord → ℝ) (p w0 : ℝ → Coord)
    (z : ℝ × ℝ) : Coord :=
  planarGradient Gin (visibleConnectorGinDisplacedPosition p w0 z)

def visibleConnectorGinDisplacedDomain (U : Set Coord) (p w0 : ℝ → Coord) :
    Set (ℝ × ℝ) := visibleConnectorGinDisplacedPosition p w0 ⁻¹' U

def visibleConnectorGinDisplacedVisibilityDomain (Gin : Coord → ℝ) (U : Set Coord)
    (R : ℝ) (p w0 : ℝ → Coord) : Set (ℝ × ℝ) :=
  visibleConnectorGinDisplacedDomain U p w0 ∩
    (fun z => ‖Complex.I * angularDescentComplex
      (visibleConnectorGinDisplacedGradient Gin p w0 z)‖) ⁻¹' Ioi R

/-- The literal clockwise eta rotation of the EXISTING actual visible direction. -/
def visibleConnectorGinRotatedDirection (R eta : ℝ) (gamma : ℝ → Coord) (s : ℝ) : Coord :=
  Real.cos eta • visibleConnectorTangentDirection R gamma s -
    Real.sin eta • visibleConnectorJ (visibleConnectorTangentDirection R gamma s)

def visibleConnectorGinRotatedRuling (R eta : ℝ) (gamma : ℝ → Coord) : ℝ → Coord :=
  visibleConnectorActualRuling R gamma (visibleConnectorGinRotatedDirection R eta gamma)

/-- Use the SAME fixed eta for the actual gradient of Gin at the displaced seam. -/
def visibleConnectorGinDisplacedRuling (Gin : Coord → ℝ) (R eta : ℝ)
    (p w0 : ℝ → Coord) (z : ℝ × ℝ) : Coord :=
  visibleConnectorGinRotatedRuling R eta
    (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (z.1, s)) z.2

/-- The literal rotated direction agrees with the old angular-frame ruling. -/
theorem visibleConnectorGinRotatedRuling_eq_shifted {R eta : ℝ}
    {gamma : ℝ → Coord} {theta : ℝ → ℝ}
    (hdir : ∀ s, visibleConnectorTangentDirection R gamma s =
      visibleConnectorUnitDirection (theta s)) :
    visibleConnectorGinRotatedRuling R eta gamma = visibleConnectorShiftedRuling R gamma theta eta := by
  funext s
  unfold visibleConnectorGinRotatedRuling visibleConnectorShiftedRuling visibleConnectorActualRuling
  apply congrArg (fun v : Coord => visibleConnectorJ (gamma s) - R • v)
  rw [visibleConnectorGinRotatedDirection, hdir s]
  ext i
  fin_cases i <;> simp [visibleConnectorShiftedDirection, visibleConnectorUnitDirection,
    visibleConnectorJ, Real.cos_sub, Real.sin_sub] <;> ring

private theorem displacedGin_J_smooth : ContDiff ℝ ∞ visibleConnectorJ := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun v : Coord => -(v 1))
    exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
  · change ContDiff ℝ ∞ (fun v : Coord => v 0)
    exact contDiff_apply ℝ ℝ (0 : Fin 2)

/-- Smoothness of the literal analytic visibility formula on its ACTUAL
strict norm-margin domain. This is used only for this joint Gin family. -/
private theorem displacedGin_direction_smooth {R : ℝ} (hR : 0 < R)
    {delta : ℝ × ℝ → ℂ} {V : Set (ℝ × ℝ)}
    (hd : ContDiffOn ℝ ∞ delta V) (hr : ∀ z ∈ V, R < ‖delta z‖) :
    ContDiffOn ℝ ∞ (fun z => corrugatedVisibilityDirection R (delta z)) V := by
  have hN : ContDiffOn ℝ ∞ (fun z => ‖delta z‖ ^ 2) V := by
    have hs := ((Complex.reCLM.contDiff.comp_contDiffOn hd).pow 2).add
      ((Complex.imCLM.contDiff.comp_contDiffOn hd).pow 2)
    have he : (fun z => ‖delta z‖ ^ 2) =
        (fun z => (delta z).re ^ 2 + (delta z).im ^ 2) := by
      funext z
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [he]
    exact hs
  have hpositive (z : ℝ × ℝ) (hz : z ∈ V) : 0 < ‖delta z‖ ^ 2 - R ^ 2 := by
    have hn := norm_nonneg (delta z)
    have h := hr z hz
    nlinarith
  have hsqrt := (hN.sub contDiffOn_const).sqrt (fun z hz => (hpositive z hz).ne')
  have hnum : ContDiffOn ℝ ∞ (fun z =>
      ((R : ℂ) + (Real.sqrt (‖delta z‖ ^ 2 - R ^ 2) : ℂ) * Complex.I) * delta z) V :=
    (contDiffOn_const.add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt).mul contDiffOn_const)).mul hd
  have hden : ContDiffOn ℝ ∞ (fun z => ((‖delta z‖ ^ 2 : ℝ) : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hN
  have hden0 (z : ℝ × ℝ) (hz : z ∈ V) : ((‖delta z‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt (hR.trans (hr z hz))))
  have hprod := hnum.mul (hden.inv hden0)
  convert! hprod using 1

/-- These are the actual analytic/domain/period inputs for the displaced-seam
inverse producer. Omega_vis is CONSTRUCTED from U and the strict central norm
margin. The arbitrary values of Gin outside U are never used for smoothness.
The original ruling agreement uses the SAME literal eta formula. -/
theorem visibleConnectorGinDisplacedFamily_properties {L R eta : ℝ}
    {Gin : Coord → ℝ} {U : Set Coord} {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ U)
    (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s) :
    ContDiff ℝ ∞ (visibleConnectorGinDisplacedPosition p w0) ∧
    IsOpen (visibleConnectorGinDisplacedDomain U p w0) ∧
    ContDiffOn ℝ ∞ (visibleConnectorGinDisplacedGradient Gin p w0)
      (visibleConnectorGinDisplacedDomain U p w0) ∧
    IsOpen (visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) ∧
    visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0 ⊆
      visibleConnectorGinDisplacedDomain U p w0 ∧
    (∀ s, (0, s) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) ∧
    ContDiffOn ℝ ∞ (visibleConnectorGinDisplacedRuling Gin R eta p w0)
      (visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) ∧
    (∀ rho, Periodic (fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)) L) ∧
    (∀ rho, Periodic (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (rho, s)) L) ∧
    (∀ rho, Periodic (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)) L) ∧
    (∀ rho s, (rho, s + L) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0 ↔
      (rho, s) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) ∧
    (∀ s, visibleConnectorGinDisplacedGradient Gin p w0 (0, s) = gamma s) ∧
    (∀ s, visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, s) = w0 s) := by
  let pc := visibleConnectorGinDisplacedPosition p w0
  let gc := visibleConnectorGinDisplacedGradient Gin p w0
  let DU := visibleConnectorGinDisplacedDomain U p w0
  let V := visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0
  have hpc : ContDiff ℝ ∞ pc :=
    (hp.comp contDiff_snd).add (contDiff_fst.smul (hw0.comp contDiff_snd))
  have hDU : IsOpen DU := hU.preimage hpc.continuous
  have hgc : ContDiffOn ℝ ∞ gc DU :=
    (planarGradient_contDiffOn hGin hU).comp hpc.contDiffOn (fun _ hz => hz)
  let delta : ℝ × ℝ → ℂ := fun z => Complex.I * angularDescentComplex (gc z)
  have hd : ContDiffOn ℝ ∞ delta DU :=
    contDiffOn_const.mul (angularDescentComplex_contDiff.comp_contDiffOn hgc)
  have hV : IsOpen V := hd.continuousOn.norm.isOpen_inter_preimage hDU isOpen_Ioi
  have hVsub : V ⊆ DU := inter_subset_left
  have hgc0 (s : ℝ) : gc (0, s) = gamma s := by
    change planarGradient Gin (p s + (0 : ℝ) • w0 s) = gamma s
    simpa only [zero_smul, add_zero] using (hgamma s).symm
  have haxisV (s : ℝ) : (0, s) ∈ V := by
    refine ⟨?_, ?_⟩
    · change p s + (0 : ℝ) • w0 s ∈ U
      simpa only [zero_smul, add_zero] using hpU s
    · change R < ‖Complex.I * angularDescentComplex (gc (0, s))‖
      rw [hgc0]
      exact hmargin s
  let t : ℝ × ℝ → Coord := fun z =>
    visibleConnectorTangentDirection R (fun s => gc (z.1, s)) z.2
  have hdc : ContDiffOn ℝ ∞ (fun z => corrugatedVisibilityDirection R (delta z)) V :=
    displacedGin_direction_smooth hR (hd.mono hVsub) (fun _ hz => hz.2)
  have ht : ContDiffOn ℝ ∞ t V := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · change ContDiffOn ℝ ∞ (fun z => (corrugatedVisibilityDirection R (delta z)).re) V
      exact Complex.reCLM.contDiff.comp_contDiffOn hdc
    · change ContDiffOn ℝ ∞ (fun z => (corrugatedVisibilityDirection R (delta z)).im) V
      exact Complex.imCLM.contDiff.comp_contDiffOn hdc
  have hrot : ContDiffOn ℝ ∞ (fun z => Real.cos eta • t z -
      Real.sin eta • visibleConnectorJ (t z)) V :=
    ((contDiffOn_const (c := Real.cos eta)).smul ht).sub
      ((contDiffOn_const (c := Real.sin eta)).smul (displacedGin_J_smooth.comp_contDiffOn ht))
  have hw : ContDiffOn ℝ ∞ (visibleConnectorGinDisplacedRuling Gin R eta p w0) V :=
    (displacedGin_J_smooth.comp_contDiffOn (hgc.mono hVsub)).sub
      ((contDiffOn_const (c := R)).smul hrot)
  have hpcL (rho : ℝ) : Periodic (fun s => pc (rho, s)) L := by
    intro s
    change p (s + L) + rho • w0 (s + L) = p s + rho • w0 s
    rw [hpL s, hw0L s]
  have hgcL (rho : ℝ) : Periodic (fun s => gc (rho, s)) L := by
    intro s
    change planarGradient Gin (pc (rho, s + L)) = planarGradient Gin (pc (rho, s))
    have he : pc (rho, s + L) = pc (rho, s) := hpcL rho s
    rw [he]
  have hwL (rho : ℝ) : Periodic
      (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)) L := by
    intro s
    have he : visibleConnectorGinDisplacedGradient Gin p w0 (rho, s + L) =
        visibleConnectorGinDisplacedGradient Gin p w0 (rho, s) := hgcL rho s
    simp only [visibleConnectorGinDisplacedRuling, visibleConnectorGinRotatedRuling,
      visibleConnectorActualRuling, visibleConnectorGinRotatedDirection,
      visibleConnectorTangentDirection, he]
  have hperiodV (rho s : ℝ) : (rho, s + L) ∈ V ↔ (rho, s) ∈ V := by
    change pc (rho, s + L) ∈ U ∧
      R < ‖Complex.I * angularDescentComplex (gc (rho, s + L))‖ ↔
      pc (rho, s) ∈ U ∧ R < ‖Complex.I * angularDescentComplex (gc (rho, s))‖
    have he : pc (rho, s + L) = pc (rho, s) := hpcL rho s
    have hg : gc (rho, s + L) = gc (rho, s) := hgcL rho s
    rw [he, hg]
  have hwzero (s : ℝ) : visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, s) = w0 s := by
    have heq : (fun r => gc (0, r)) = gamma := funext hgc0
    change visibleConnectorGinRotatedRuling R eta (fun r => gc (0, r)) s = w0 s
    rw [heq]
    exact (hw0same s).symm
  exact ⟨hpc, hDU, hgc, hV, hVsub, haxisV, hw, hpcL, hgcL, hwL, hperiodV, hgc0, hwzero⟩

end
end TightVer401