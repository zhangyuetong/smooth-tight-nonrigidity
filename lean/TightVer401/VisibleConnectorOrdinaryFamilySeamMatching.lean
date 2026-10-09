import TightVer401.VisibleConnectorOrdinaryFamilyBandCarrier
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedCoefficients
import TightVer401.VisibleConnectorIncomingRebaseMatching

/-! Actual displaced-seam matching for ONE retained raw Cartesian inverse.
The whole physical strip is recovered from existing calculus on SAME E.
The old seam is an interior rebased point, not a new source or inverse. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- From actual original coefficients and a retained raw E/U, construct the
full physical strip and both Gin/raw seam jets. Matching conclusions are
outputs. The supplied raw-band image/domain facts are exact outputs of the
raw-potential assembly; no final smoothing scalar enters this theorem. -/
theorem visibleConnectorOrdinaryFamilySeamMatching_actual
    {L : ℝ} (hL : 0 < L) {Gin : Coord → ℝ} {GinU : Set Coord}
    {p w : ℝ → Coord} {a b : ℝ → ℝ}
    (hGinU : IsOpen GinU) (hGin : ContDiffOn ℝ ∞ Gin GinU)
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hpGin : ∀ s, p s ∈ GinU)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hshift : ∀ s, a (s + L) = a s + L) (hbL : Periodic b L)
    (hap : ∀ s, 0 < deriv a s) (hbneg : ∀ s, b s < 0)
    (hA : ∀ s, 0 < visibleConnectorA p w s)
    (hB : ∀ s, 0 < visibleConnectorB (planarGradient Gin ∘ p) w s)
    (hC : ∀ s, 0 < visibleConnectorC (planarGradient Gin ∘ p) w s)
    (hLower : ∀ s, 0 < visibleConnectorDelta p (planarGradient Gin ∘ p) w ![a s, b s])
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a (fun s =>
        visibleConnectorActualTerminalHeight p (planarGradient Gin ∘ p) w (a s) - b s))
      (fun _ => 1))
    (hEs : E.source ⊆ {z : Coord | 0 < planarRadius z})
    (hi : ContDiffOn ℝ ∞ E.symm E.target)
    (hClosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    {Ho Hi : ℂ ≃ₜ ℂ} {Uraw : Set Coord}
    (hImage : visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a (fun s =>
        visibleConnectorActualTerminalHeight p (planarGradient Gin ∘ p) w (a s) - b s))
      (fun _ => 1) '' {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
      annularCoordJordanClosure Ho Hi)
    (hBandU : annularCoordJordanClosure Ho Hi ⊆ Uraw) :
    let tc := visibleConnectorActualTerminalHeight p (planarGradient Gin ∘ p) w
    let d := fun s => tc (a s) - b s
    let P := visibleConnectorRebasedSource p w a b
    let f := visibleConnectorRebasedHeight (Gin ∘ p) (planarGradient Gin ∘ p) w a b
    let W := visibleConnectorRebasedRuling w a d
    let Gamma := visibleConnectorRebasedGradient p (planarGradient Gin ∘ p) w a b
    let Vphys := visibleConnectorCartesianPotentialRuledDomain L P Gamma W (fun _ => 1) E
    let raw := visibleConnectorCartesianPotential L f Gamma W (fun _ => 1) E
    IsOpen Vphys ∧ {q : Coord | 0 ≤ q 1 ∧ q 1 ≤ 1} ⊆ Vphys ∧
    ContDiffOn ℝ ∞ raw E.target ∧
    ∀ s, (-b s / d s) ∈ Ioo (0 : ℝ) 1 ∧
      (![s, -b s / d s] : Coord) ∈ Vphys ∧ p (a s) ∈ Uraw ∧
      raw (p (a s)) = Gin (p (a s)) ∧
      planarGradient raw (p (a s)) = planarGradient Gin (p (a s)) := by
  dsimp only
  let gamma := planarGradient Gin ∘ p
  let g := Gin ∘ p
  let tc := visibleConnectorActualTerminalHeight p gamma w
  let d := fun s => tc (a s) - b s
  let P := visibleConnectorRebasedSource p w a b
  let f := visibleConnectorRebasedHeight g gamma w a b
  let W := visibleConnectorRebasedRuling w a d
  let Gamma := visibleConnectorRebasedGradient p gamma w a b
  let Vphys := visibleConnectorCartesianPotentialRuledDomain L P Gamma W (fun _ => 1) E
  have hg : ContDiff ℝ ∞ g := contDiffOn_univ.mp
    (hGin.comp hp.contDiffOn (fun s _ => hpGin s))
  have hgamma : ContDiff ℝ ∞ gamma := contDiffOn_univ.mp
    ((planarGradient_contDiffOn hGin hGinU).comp hp.contDiffOn (fun s _ => hpGin s))
  have hgL : Periodic g L := by intro s; dsimp [g]; rw [hpL s]
  have hgammaL : Periodic gamma L := by intro s; dsimp [gamma]; rw [hpL s]
  have hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s :=
    visibleConnectorIncomingSeam_trace_deriv hGinU hGin hp hpGin
  obtain ⟨htc, _htcL, htcpos, hd, hdL, hdpos, _hUpper,
    hP, hf, hW, hGamma, hPL, hfL, hWL, hGammaL, hval, hANew, hBNew, hDelta, _hOut⟩ :=
    visibleConnectorOrdinaryFamilyRebasedCoefficients_actual hp hgamma hw hg ha hb
      hpL hgammaL hwL hgL hshift hbL hap hbneg hA hB hC hLower hvalue
  have hOneL : Periodic (fun _ : ℝ => (1 : ℝ)) L := fun _ => rfl
  have hOne : ∀ s : ℝ, 0 < (fun _ : ℝ => (1 : ℝ)) s := fun _ => zero_lt_one
  obtain ⟨hraw, hV, hStrip, _hrec, _hgrad, _hAction, _hDet, _hNeighborhood⟩ :=
    visibleConnectorCartesianPotential_closed_strip_calculus hL hP hGamma hW hf
      (contDiff_const (c := (1 : ℝ))) hPL hGammaL hWL hfL hOneL hOne hval
      hANew hBNew hDelta E hE hEs hi hClosed
  have hu (s : ℝ) : (-b s / d s) ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (neg_pos.mpr (hbneg s)) (hdpos s), ?_⟩
    apply (div_lt_one (hdpos s)).mpr
    change -b s < tc (a s) - b s
    linarith [htcpos (a s)]
  have hSeam (s : ℝ) : (![s, -b s / d s] : Coord) ∈ Vphys :=
    hStrip ⟨(hu s).1.le, (hu s).2.le⟩
  have hMatch := visibleConnectorIncomingRebase_cartesian_seam_matches hL
    hGinU hGin hp hw hpGin ha hb hd hpL hwL hshift hbL hdL
    (fun s => (hLower s).ne') (fun s => (hap s).ne') (fun s => (hdpos s).ne')
    E hE hV (fun q hq => hq.2.1) (fun q hq => hq.1)
    (fun q hq => hq.2.2.ne') hSeam
  refine ⟨hV, hStrip, hraw, ?_⟩
  intro s
  have hInRaw : p (a s) ∈ Uraw := by
    let q : Coord := ![s, -b s / d s]
    have hq : q ∈ Vphys := hSeam s
    have hRadius : visibleConnectorCartesianPotentialRadius (fun _ => 1) q =
        1 + (-b s / d s) := by simp [visibleConnectorCartesianPotentialRadius, q]
    have hr : 0 < visibleConnectorCartesianPotentialRadius (fun _ => 1) q := hq.1
    have hrad : planarRadius (visibleConnectorCartesianPotentialPhysicalChart L (fun _ => 1) q) =
        visibleConnectorCartesianPotentialRadius (fun _ => 1) q :=
      angularDescent_radius_polar (q :=
        ![visibleConnectorCartesianPotentialRadius (fun _ => 1) q, 2 * Real.pi * q 0 / L])
        (by simpa only [Matrix.cons_val_zero] using hr)
    have hround : visibleConnectorCartesianPotentialPhysicalChart L (fun _ => 1) q ∈
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} := by
      rw [mem_setOf_eq, hrad, hRadius]
      constructor <;> linarith [(hu s).1, (hu s).2]
    have hzero : b s + (-b s / d s) * d s = 0 := by
      have hdne : d s ≠ 0 := (hdpos s).ne'
      rw [div_mul_cancel₀ _ hdne]
      ring
    have hSource : visibleConnectorSource P W q = p (a s) := by
      dsimp only [q]
      rw [visibleConnector_rebase_source, hzero]
      simp [visibleConnectorSource, q]
    have hPull := (visibleConnectorCartesianPotential_physical_pullbacks hL
      hPL hGammaL hWL hfL hOneL hOne hr).1
    apply hBandU
    rw [← hImage]
    refine ⟨visibleConnectorCartesianPotentialPhysicalChart L (fun _ => 1) q, hround, ?_⟩
    exact hPull.trans hSource
  exact ⟨hu s, hSeam s, hInRaw, (hMatch s).1, (hMatch s).2⟩

end
end TightVer401
