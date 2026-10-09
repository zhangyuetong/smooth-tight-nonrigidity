import TightVer401.VisibleConnectorIncomingGinGlobalSide

/-! Actual derivatives of the globally descended height at the displaced
zero seam.  The ruling derivative is proved by an actual source pullback
germ.  The canonical normal sign uses the retained source determinant, not
an assumed side classification or a Jordan normal-side Boolean. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem visibleConnectorIncomingGinGlobalHeight_seam_derivatives {L : ℝ} (hL : 0 < L)
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (ha : ContDiff ℝ ∞ a)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingGinGlobalHeight L b d E) E.target) (s : ℝ) :
    visibleConnectorIncomingGinGlobalHeight L b d E (pc (a s)) = 0 ∧
      fderiv ℝ (visibleConnectorIncomingGinGlobalHeight L b d E) (pc (a s))
        (deriv (pc ∘ a) s) = 0 ∧
      fderiv ℝ (visibleConnectorIncomingGinGlobalHeight L b d E) (pc (a s)) (wc (a s)) = 1 := by
  let B := visibleConnectorIncomingGinGlobalHeight L b d E
  have hseam (r : ℝ) := visibleConnectorIncomingGinGlobalHeight_rebased_band hL
    hpL hwL hbL hdL hb hd ht E hE hclosed r
  have hmem : pc (a s) ∈ E.target := (hseam s).2.2.2.2.1
  have hzero (r : ℝ) : B (pc (a r)) = 0 := (hseam r).2.2.2.2.2.1
  have hBd : DifferentiableAt ℝ B (pc (a s)) :=
    ((hB _ hmem).contDiffAt (E.open_target.mem_nhds hmem)).differentiableAt (by simp)
  have hc := hBd.hasFDerivAt.comp_hasDerivAt s
    ((hp.comp ha).differentiable (by simp) s).hasDerivAt
  have hcz : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (fderiv ℝ B (pc (a s)) (deriv (pc ∘ a) s)) s := by
    simpa only [Function.comp_def, hzero] using hc
  let u0 := -b s / d s
  have hu0 : 0 < u0 := div_pos (neg_pos.mpr (hb s)) (hd s)
  have hu1 : u0 < 1 := (div_lt_one (hd s)).mpr (by linarith [ht s])
  have hz : b s + u0 * d s = 0 := by
    dsimp [u0]
    field_simp [(hd s).ne']
    ring
  have hpath : Continuous (fun t : ℝ => u0 + t / d s) :=
    continuous_const.add (continuous_id.div_const _)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), u0 + t / d s ∈ Ioo (0 : ℝ) 1 :=
    (isOpen_Ioo.preimage hpath).mem_nhds (by simpa using (show u0 ∈ Ioo (0 : ℝ) 1 from ⟨hu0, hu1⟩))
  have heq : (fun t : ℝ => B (pc (a s) + t • wc (a s))) =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [hnear] with t htube
    have hpull := (visibleConnectorIncomingGinGlobalHeight_closed_band hL hpL hwL hbL hdL
      E hE hclosed s (u0 + t / d s) htube.1.le htube.2.le).2
    rw [visibleConnector_rebase_source] at hpull
    have hscalar : b s + (u0 + t / d s) * d s = t := by
      calc
        b s + (u0 + t / d s) * d s = b s + u0 * d s + t := by
          field_simp [(hd s).ne']
          ring
        _ = t := by rw [hz, zero_add]
    rw [hscalar] at hpull
    simpa only [B, visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one, id_eq]
      using hpull
  have hline : HasDerivAt (fun t : ℝ => pc (a s) + t • wc (a s)) (wc (a s)) 0 := by
    simpa using (hasDerivAt_const 0 (pc (a s))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (wc (a s))))
  have hBdLine : DifferentiableAt ℝ B (pc (a s) + (0 : ℝ) • wc (a s)) := by
    simpa only [zero_smul, add_zero] using hBd
  have hu := hBdLine.hasFDerivAt.comp_hasDerivAt 0 hline
  simp only [zero_smul, add_zero] at hu
  have hui : HasDerivAt (id : ℝ → ℝ)
      (fderiv ℝ B (pc (a s)) (wc (a s))) 0 := hu.congr_of_eventuallyEq heq.symm
  exact ⟨hzero s, hcz.unique (hasDerivAt_const s 0), hui.unique (hasDerivAt_id 0)⟩

/-- Negative actual source determinant at the seam, after the SAME phase
clock.  The input is the ordinary strict coefficient from the ruling. -/
theorem visibleConnectorIncomingGinGlobalHeight_seam_determinant
    {pc wc : ℝ → Coord} {a : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hphase : ∀ s, 0 < deriv a s) (hA : ∀ s, 0 < visibleConnectorA pc wc (a s))
    (s : ℝ) : visibleConnectorDet (deriv (pc ∘ a) s) (wc (a s)) < 0 := by
  have hc := ((hp.differentiable (by simp) (a s)).hasDerivAt).comp s
    (ha.differentiable (by simp) s).hasDerivAt
  have hdet := visibleConnectorSource_actual_determinant hp hw pc (![a s, 0] : Coord)
  rw [(visibleConnectorSource_partials hp hw (![a s, 0] : Coord)).1,
    (visibleConnectorSource_partials hp hw (![a s, 0] : Coord)).2] at hdet
  simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, add_zero, zero_mul] at hdet
  have hclock : visibleConnectorDet (deriv (pc ∘ a) s) (wc (a s)) =
      deriv a s * visibleConnectorDet (deriv pc (a s)) (wc (a s)) := by
    rw [hc.deriv]
    simp only [visibleConnectorDet, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hclock, hdet]
  exact mul_neg_of_pos_of_neg (hphase s) (neg_neg_of_pos (hA s))

/-- Canonical positive normal lies on the NEGATIVE-height side.  This
canonical positive-normal side is the incoming Gin side in relative smoothing. -/
theorem visibleConnectorIncomingGinGlobalHeight_normal_neg {L : ℝ} (hL : 0 < L)
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (hphase : ∀ s, 0 < deriv a s) (hA : ∀ s, 0 < visibleConnectorA pc wc (a s))
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingGinGlobalHeight L b d E) E.target)
    (s : ℝ) :
    fderiv ℝ (visibleConnectorIncomingGinGlobalHeight L b d E) (pc (a s))
      (visibleConnectorJ (deriv (pc ∘ a) s)) < 0 := by
  obtain ⟨_, hv, hwB⟩ := visibleConnectorIncomingGinGlobalHeight_seam_derivatives hL hp ha
    hpL hwL hbL hdL hb hd ht E hE hclosed hB s
  exact visibleConnectorIncomingGin_normal_derivative_neg _ _ _ hv hwB
    (visibleConnectorIncomingGinGlobalHeight_seam_determinant hp hw ha hphase hA s)

private theorem incomingGinGlobal_complex_normal (z : ℂ) :
    seamComplexCoord (Complex.I * z) = visibleConnectorJ (seamComplexCoord z) := by
  ext i
  fin_cases i <;>
    simp [seamComplexCoord_apply, visibleConnectorJ, Complex.mul_re, Complex.mul_im]

/-- A uniform canonical classifier for the globally defined negative sublevel
on a FIXED open carrier V.  The carrier can be the entire actual raw potential
domain; it is not replaced by a thin inverse slice.  Neither the classification
nor an incoming-potential domain containment is assumed. -/
theorem visibleConnectorIncomingGinGlobalHeight_exists_side_threshold {L : ℝ} (hL : 0 < L)
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hcL : Periodic (pc ∘ a) L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (hphase : ∀ s, 0 < deriv a s) (hA : ∀ s, 0 < visibleConnectorA pc wc (a s))
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingGinGlobalHeight L b d E) E.target)
    {V : Set Coord} (hV : IsOpen V) (hVE : V ⊆ E.target) (hseamV : ∀ s, pc (a s) ∈ V) :
    let gamma := fun s => seamComplexCoord.symm (pc (a s))
    ∃ r > 0, ∀ s t, |t| ≤ r →
      seamNormalCoordinates gamma (![s, t] : Coord) ∈ V ∧
        (seamNormalCoordinates gamma (![s, t] : Coord) ∈
          visibleConnectorIncomingGinGlobalSide L b d E ↔ 0 < t) := by
  let c := pc ∘ a
  let gamma := fun s => seamComplexCoord.symm (c s)
  have hc : ContDiff ℝ ∞ c := hp.comp ha
  have hg : ContDiff ℝ ∞ gamma := seamComplexCoord.symm.contDiff.comp hc
  have hgL : Periodic gamma L := by
    intro s
    change seamComplexCoord.symm (c (s + L)) = seamComplexCoord.symm (c s)
    rw [hcL s]
  have hmem (s : ℝ) : seamComplexCoord (gamma s) ∈ V := by
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      using hseamV s
  have hzero (s : ℝ) : visibleConnectorIncomingGinGlobalHeight L b d E
      (seamComplexCoord (gamma s)) = 0 := by
    simpa only [gamma, c, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      using (visibleConnectorIncomingGinGlobalHeight_seam_derivatives hL hp ha
        hpL hwL hbL hdL hb hd ht E hE hclosed hB s).1
  have hnormal (s : ℝ) : fderiv ℝ (visibleConnectorIncomingGinGlobalHeight L b d E)
      (seamComplexCoord (gamma s)) (seamComplexCoord (Complex.I * deriv gamma s)) < 0 := by
    have hderiv : deriv gamma s = seamComplexCoord.symm (deriv c s) :=
      (seamComplexCoord.symm.hasFDerivAt.comp_hasDerivAt s
        (hc.differentiable (by simp) s).hasDerivAt).deriv
    rw [incomingGinGlobal_complex_normal, hderiv]
    simp only [gamma, ContinuousLinearEquiv.apply_symm_apply]
    exact visibleConnectorIncomingGinGlobalHeight_normal_neg hL hp hw ha
      hpL hwL hbL hdL hb hd ht hphase hA E hE hclosed hB s
  exact visibleConnectorIncomingGin_exists_canonical_side_threshold hL hg hgL hV
    (hB.mono hVE) hmem hzero hnormal

end
end TightVer401
