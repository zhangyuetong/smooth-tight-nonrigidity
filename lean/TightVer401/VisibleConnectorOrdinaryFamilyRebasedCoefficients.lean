import TightVer401.VisibleConnectorOrdinaryFamilySourceChart

/-! Actual coefficients of the SAME rebased connector. The remaining length
is defined from the literal terminal height and the supplied lower graph.
Its positivity, upper Delta sign and all rebased scalar/ruling facts are
produced from the original A/B/C signs, rather than granted separately. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem rebasedCoefficients_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hL : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hL
  have hd := congrArg (fun F : ℝ → Coord => deriv F s) he
  simpa only [deriv_comp_add_const] using hd

/-- The literal terminal height gives the exact endpoint Delta formula,
for arbitrary actual ruling data, independently of a circle parametrization. -/
theorem visibleConnectorOrdinaryFamilyRebasedCoefficients_terminal_delta
    (p gamma w : ℝ → Coord) (s : ℝ)
    (hC : visibleConnectorC gamma w s ≠ 0) :
    visibleConnectorDelta p gamma w
      ![s, visibleConnectorActualTerminalHeight p gamma w s] =
      visibleConnectorA p w s * visibleConnectorB gamma w s /
        visibleConnectorC gamma w s := by
  change visibleConnectorA p w s +
    (visibleConnectorA p w s / visibleConnectorC gamma w s) *
      (visibleConnectorB gamma w s - visibleConnectorC gamma w s) = _
  field_simp [hC]
  <;> ring

/-- The SAME original coefficients, phase and negative lower height construct
all analytic scalar/ruling inputs of the raw-potential producer. The upper
endpoint and remaining length are defined, never independent witnesses. -/
theorem visibleConnectorOrdinaryFamilyRebasedCoefficients_actual
    {L : ℝ} {p gamma w : ℝ → Coord} {g a b : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hshift : ∀ s, a (s + L) = a s + L) (hbL : Periodic b L)
    (hap : ∀ s, 0 < deriv a s) (hbneg : ∀ s, b s < 0)
    (hA : ∀ s, 0 < visibleConnectorA p w s)
    (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    (hC : ∀ s, 0 < visibleConnectorC gamma w s)
    (hLower : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s])
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s) :
    let tc := visibleConnectorActualTerminalHeight p gamma w
    let d := fun s => tc (a s) - b s
    let P := visibleConnectorRebasedSource p w a b
    let f := visibleConnectorRebasedHeight g gamma w a b
    let W := visibleConnectorRebasedRuling w a d
    let Gamma := visibleConnectorRebasedGradient p gamma w a b
    ContDiff ℝ ∞ tc ∧ Periodic tc L ∧ (∀ s, 0 < tc s) ∧
    ContDiff ℝ ∞ d ∧ Periodic d L ∧ (∀ s, 0 < d s) ∧
    (∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s + d s]) ∧
    ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ Gamma ∧
    Periodic P L ∧ Periodic f L ∧ Periodic W L ∧ Periodic Gamma L ∧
    (∀ s, deriv f s = Gamma s ⬝ᵥ deriv P s) ∧
    (∀ s, 0 < visibleConnectorA P W s) ∧
    (∀ s, 0 < visibleConnectorB Gamma W s) ∧
    (∀ q : Coord, 0 ≤ q 1 → q 1 ≤ 1 → 0 < visibleConnectorDelta P Gamma W q) ∧
    (∀ s, P s + W s = p (a s) + tc (a s) • w (a s)) := by
  dsimp only
  let tc := visibleConnectorActualTerminalHeight p gamma w
  let d := fun s => tc (a s) - b s
  have htc : ContDiff ℝ ∞ tc :=
    visibleConnectorActualTerminalHeight_contDiff hp hgamma hw (fun s => (hC s).ne')
  have hdpL := rebasedCoefficients_deriv_periodic hpL
  have hdgL := rebasedCoefficients_deriv_periodic hgammaL
  have hdwL := rebasedCoefficients_deriv_periodic hwL
  have hAL : Periodic (visibleConnectorA p w) L := by
    intro s
    unfold visibleConnectorA
    rw [hdpL s, hwL s]
  have hBL : Periodic (visibleConnectorB gamma w) L := by
    intro s
    unfold visibleConnectorB
    rw [hdgL s, hwL s]
  have hCL : Periodic (visibleConnectorC gamma w) L := by
    intro s
    unfold visibleConnectorC
    rw [hBL s, hdwL s, hwL s]
  have htcL : Periodic tc L := by
    intro s
    change visibleConnectorA p w (s + L) / visibleConnectorC gamma w (s + L) =
      visibleConnectorA p w s / visibleConnectorC gamma w s
    rw [hAL s, hCL s]
  have htcpos : ∀ s, 0 < tc s := fun s => div_pos (hA s) (hC s)
  have hd : ContDiff ℝ ∞ d := (htc.comp ha).sub hb
  have hdL : Periodic d L := by
    intro s
    dsimp [d]
    rw [hshift s, htcL (a s), hbL s]
  have hdpos : ∀ s, 0 < d s := by
    intro s
    exact sub_pos.mpr ((hbneg s).trans (htcpos (a s)))
  have hsum (s : ℝ) : b s + d s = tc (a s) := by dsimp [d]; ring
  have hUpper : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s + d s] := by
    intro s
    rw [hsum s, visibleConnectorOrdinaryFamilyRebasedCoefficients_terminal_delta
      p gamma w (a s) (hC (a s)).ne']
    exact div_pos (mul_pos (hA (a s)) (hB (a s))) (hC (a s))
  obtain ⟨hP, hf, hW, hGamma⟩ := visibleConnector_rebase_smooth
    hg hp hgamma hw ha hb hd (fun s => (hLower s).ne')
  obtain ⟨hPL, hfL, hWL, hGammaL⟩ := visibleConnector_rebase_periodic
    hpL hgL hgammaL hwL hshift hbL hdL
  have hval := fun s => visibleConnector_rebase_value_deriv hg hp hgamma hw ha hb
    hvalue s (hLower s).ne'
  have hsign (s : ℝ) := visibleConnector_rebase_positive hp hgamma hw ha hb hd
    hap hdpos (fun s => hA (a s)) (fun s => hB (a s)) hLower s 1
    (by simpa only [one_mul] using hUpper s)
  have hClosed := visibleConnectorOrdinaryFamilySourceChart_rebased_delta_closed
    hp hw ha hb hd hap hdpos hLower hUpper
  refine ⟨htc, htcL, htcpos, hd, hdL, hdpos, hUpper,
    hP, hf, hW, hGamma, hPL, hfL, hWL, hGammaL, hval,
    (fun s => (hsign s).1), (fun s => (hsign s).2.1), hClosed, ?_⟩
  intro s
  have he := visibleConnector_rebase_source p w a b d s 1
  simp only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_smul, one_mul, hsum s] at he
  exact he

end
end TightVer401
