import TightVer401.VisibleConnectorIncomingSeamJets
import TightVer401.VisibleConnectorCartesianPotentialCalculus

/-! Literal VALUE and gradient matches of the actual rebased Cartesian scalar
at the displaced seam. SAME Cartesian E is retained throughout. Ordinary
physical-domain/inverse bounds remain real inputs, not desired matches. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The zero of the rebased old height is the displaced seam, not the original
lower curve. This statement supplies the exact hValue/hGradient at p(a s)
required by full-carrier relative smoothing, for the literal SAME raw scalar. -/
theorem visibleConnectorIncomingRebase_cartesian_seam_matches
    {L : ℝ} (hL : 0 < L) {Gin : Coord → ℝ} {U : Set Coord}
    {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hpU : ∀ s, p s ∈ U)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hshift : ∀ s, a (s + L) = a s + L) (hbL : Periodic b L) (hdL : Periodic d L)
    (hDb : ∀ s, visibleConnectorDelta p (planarGradient Gin ∘ p) w (![a s, b s] : Coord) ≠ 0)
    (hap : ∀ s, deriv a s ≠ 0) (hdp : ∀ s, d s ≠ 0)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b) (visibleConnectorRebasedRuling w a d) (fun _ => 1))
    {V : Set Coord} (hV : IsOpen V)
    (hpsi : MapsTo (visibleConnectorCartesianPotentialPhysicalChart L (fun _ => 1)) V E.source)
    (hr : ∀ q ∈ V, 0 < visibleConnectorCartesianPotentialRadius (fun _ => 1) q)
    (hDelta : ∀ q ∈ V, visibleConnectorDelta
      (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedGradient p (planarGradient Gin ∘ p) w a b)
      (visibleConnectorRebasedRuling w a d) q ≠ 0)
    (hseam : ∀ s, (![s, -b s / d s] : Coord) ∈ V) :
    let raw := visibleConnectorCartesianPotential L
      (visibleConnectorRebasedHeight (Gin ∘ p) (planarGradient Gin ∘ p) w a b)
      (visibleConnectorRebasedGradient p (planarGradient Gin ∘ p) w a b)
      (visibleConnectorRebasedRuling w a d) (fun _ => 1) E
    ∀ s, raw (p (a s)) = Gin (p (a s)) ∧
      planarGradient raw (p (a s)) = planarGradient Gin (p (a s)) := by
  dsimp only
  let g := Gin ∘ p
  let gamma := planarGradient Gin ∘ p
  have hg : ContDiff ℝ ∞ g := contDiffOn_univ.mp
    (hGin.comp hp.contDiffOn (fun s _ => hpU s))
  have hgamma : ContDiff ℝ ∞ gamma := contDiffOn_univ.mp
    ((planarGradient_contDiffOn hGin hU).comp hp.contDiffOn (fun s _ => hpU s))
  have hgL : Periodic g L := by intro s; dsimp [g]; rw [hpL s]
  have hgammaL : Periodic gamma L := by intro s; dsimp [gamma]; rw [hpL s]
  have hvalue (s : ℝ) : deriv g s = gamma s ⬝ᵥ deriv p s :=
    visibleConnectorIncomingSeam_trace_deriv hU hGin hp hpU s
  obtain ⟨hpNew, hgNew, hwNew, hgammaNew⟩ :=
    visibleConnector_rebase_smooth hg hp hgamma hw ha hb hd hDb
  obtain ⟨hpNewL, hgNewL, hwNewL, hgammaNewL⟩ :=
    visibleConnector_rebase_periodic hpL hgL hgammaL hwL hshift hbL hdL
  have hvalueNew (s : ℝ) :=
    visibleConnector_rebase_value_deriv hg hp hgamma hw ha hb hvalue s (hDb s)
  have hOneL : Periodic (fun _ : ℝ => (1 : ℝ)) L := by intro s; rfl
  have hOne : ∀ s : ℝ, 0 < (fun _ : ℝ => (1 : ℝ)) s := by intro s; norm_num
  have hv := visibleConnectorCartesianPotential_height_eqOn hL
    hpNewL hgammaNewL hwNewL hgNewL hOneL hOne E hE hpsi hr
  have hj := visibleConnectorCartesianPotential_gradient_eqOn hL
    hpNew hgammaNew hwNew hgNew hpNewL hgammaNewL hwNewL hgNewL hOneL
    hOne E hE hV hpsi hr hDelta hvalueNew
  intro s
  let u := -b s / d s
  have hz : b s + u * d s = 0 := by dsimp [u]; field_simp [hdp s]; ring
  have hSource : visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) = p (a s) := by
    rw [visibleConnector_rebase_source, hz]
    simp [visibleConnectorSource]
  have hDu : visibleConnectorDelta p gamma w (![a s, b s + u * d s] : Coord) ≠ 0 := by
    have htransport := (visibleConnector_rebase_determinants (gamma := gamma) hp hw ha hb hd s u).2
    have hneq := hDelta _ (hseam s)
    rw [htransport] at hneq
    exact (mul_ne_zero_iff.mp hneq).2
  have hHeight := visibleConnector_rebase_height g p gamma w a b d s u (hDb s)
  have hGradient := visibleConnector_rebase_gradient hp hgamma hw ha hb hd hDb hap hdp s u hDu
  have hVal := hv (hseam s)
  have hGrad := hj (hseam s)
  simp only [Function.comp_apply] at hVal hGrad
  rw [hSource, hHeight, hz] at hVal
  rw [hSource, hGradient, hz] at hGrad
  constructor
  · simpa [visibleConnectorHeight, g, Function.comp_apply] using hVal
  · simpa [visibleConnectorGradient, gamma, Function.comp_apply] using hGrad

end
end TightVer401


