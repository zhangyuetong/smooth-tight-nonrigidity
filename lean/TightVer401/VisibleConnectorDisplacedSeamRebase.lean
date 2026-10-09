import TightVer401.VisibleConnectorTerminalCircle
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Literal simultaneous rebase of the raw source, height AND gradient to the
original lower graph. Every formula uses the same old ruling. No Cartesian
inverse, annular potential or retained Gin germ is supplied as a premise. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def visibleConnectorRebaseParameter (a b : ℝ → ℝ) (s : ℝ) : Coord := ![a s, b s]

def visibleConnectorRebasedSource (p w : ℝ → Coord) (a b : ℝ → ℝ) : ℝ → Coord :=
  visibleConnectorSource p w ∘ visibleConnectorRebaseParameter a b

def visibleConnectorRebasedHeight (g : ℝ → ℝ) (gamma w : ℝ → Coord)
    (a b : ℝ → ℝ) : ℝ → ℝ :=
  visibleConnectorHeight g gamma w ∘ visibleConnectorRebaseParameter a b

def visibleConnectorRebasedRuling (w : ℝ → Coord) (a d : ℝ → ℝ) (s : ℝ) : Coord :=
  d s • w (a s)

def visibleConnectorRebasedGradient (p gamma w : ℝ → Coord) (a b : ℝ → ℝ) : ℝ → Coord :=
  visibleConnectorGradient p gamma w ∘ visibleConnectorRebaseParameter a b

private theorem rebase_parameter_smooth {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (visibleConnectorRebaseParameter a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ a
    exact ha
  · change ContDiff ℝ ∞ b
    exact hb

private theorem rebase_parameter_deriv {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (s : ℝ) :
    HasDerivAt (visibleConnectorRebaseParameter a b) (![deriv a s, deriv b s] : Coord) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt a (deriv a s) s
    exact (ha.differentiable (by simp) s).hasDerivAt
  · change HasDerivAt b (deriv b s) s
    exact (hb.differentiable (by simp) s).hasDerivAt

private theorem rebase_J_smooth {w : ℝ → Coord} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun s => visibleConnectorJ (w s)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun s => -(w s 1))
    exact ((contDiff_apply ℝ ℝ (1 : Fin 2)).comp hw).neg
  · change ContDiff ℝ ∞ (fun s => w s 0)
    exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp hw

private theorem rebase_delta_geometry (p gamma w : ℝ → Coord) (q : Coord) :
    visibleConnectorDelta p gamma w q =
      -visibleConnectorDet (deriv p (q 0)) (w (q 0)) -
        q 1 * visibleConnectorDet (deriv w (q 0)) (w (q 0)) := by
  simp only [visibleConnectorDelta, visibleConnectorA, visibleConnectorC]
  ring

/-- The actual source rebase is an affine change of the old ruling height. -/
theorem visibleConnector_rebase_source (p w : ℝ → Coord) (a b d : ℝ → ℝ) (s u : ℝ) :
    visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) =
    visibleConnectorSource p w (![a s, b s + u * d s] : Coord) := by
  simp only [visibleConnectorSource, visibleConnectorRebasedSource, visibleConnectorRebasedRuling,
    visibleConnectorRebaseParameter, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [smul_smul, add_smul]
  module

/-- Retain the old actual gradient, so height is rebased with the SAME jet. -/
theorem visibleConnector_rebase_height (g : ℝ → ℝ) (p gamma w : ℝ → Coord)
    (a b d : ℝ → ℝ) (s u : ℝ)
    (hD : visibleConnectorDelta p gamma w (![a s, b s] : Coord) ≠ 0) :
    visibleConnectorHeight (visibleConnectorRebasedHeight g gamma w a b)
      (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) =
    visibleConnectorHeight g gamma w (![a s, b s + u * d s] : Coord) := by
  have hdot := (visibleConnector_gradient_equations p gamma w (![a s, b s] : Coord) hD).1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hdot
  simp only [visibleConnectorHeight, visibleConnectorRebasedHeight,
    visibleConnectorRebasedGradient, visibleConnectorRebasedRuling, visibleConnectorRebaseParameter,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, dotProduct_smul]
  rw [hdot]
  ring

/-- All four rebased functions are actual smooth functions, including the
literal old gradient evaluated on the negative lower graph. -/
theorem visibleConnector_rebase_smooth {g a b d : ℝ → ℝ} {p gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hd : ContDiff ℝ ∞ d)
    (hD : ∀ s, visibleConnectorDelta p gamma w (![a s, b s] : Coord) ≠ 0) :
    ContDiff ℝ ∞ (visibleConnectorRebasedSource p w a b) ∧
      ContDiff ℝ ∞ (visibleConnectorRebasedHeight g gamma w a b) ∧
      ContDiff ℝ ∞ (visibleConnectorRebasedRuling w a d) ∧
      ContDiff ℝ ∞ (visibleConnectorRebasedGradient p gamma w a b) := by
  have hq := rebase_parameter_smooth ha hb
  have hDb : ContDiff ℝ ∞ (fun s => visibleConnectorDelta p gamma w (![a s, b s] : Coord)) :=
    ((visibleConnectorA_contDiff hp hw).comp ha).add
      (hb.mul (((visibleConnectorB_contDiff hgamma hw).sub
        (visibleConnectorC_contDiff hgamma hw)).comp ha))
  have hc : ContDiff ℝ ∞ (fun s => b s * visibleConnectorB gamma w (a s) /
      visibleConnectorDelta p gamma w (![a s, b s] : Coord)) :=
    (hb.mul ((visibleConnectorB_contDiff hgamma hw).comp ha)).div hDb hD
  refine ⟨(visibleConnectorSource_contDiff hp hw).comp hq,
    (visibleConnectorHeight_contDiff hg hgamma hw).comp hq, hd.smul (hw.comp ha), ?_⟩
  exact (hgamma.comp ha).add (hc.smul ((rebase_J_smooth hw).comp ha))

/-- The actual longitudinal derivative of the rebased lower curve. -/
theorem visibleConnector_rebased_source_deriv {p w : ℝ → Coord} {a b : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (s : ℝ) :
    deriv (visibleConnectorRebasedSource p w a b) s =
      deriv a s • (deriv p (a s) + b s • deriv w (a s)) + deriv b s • w (a s) := by
  have hpa := ((hp.differentiable (by simp) (a s)).hasDerivAt).scomp s
    (ha.differentiable (by simp) s).hasDerivAt
  have hwa := ((hw.differentiable (by simp) (a s)).hasDerivAt).scomp s
    (ha.differentiable (by simp) s).hasDerivAt
  have h := hpa.add (((hb.differentiable (by simp) s).hasDerivAt).smul hwa)
  change HasDerivAt (visibleConnectorRebasedSource p w a b) _ s at h
  rw [h.deriv]
  simp only [Function.comp_apply]
  module

theorem visibleConnector_rebased_ruling_deriv {w : ℝ → Coord} {a d : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ d) (s : ℝ) :
    deriv (visibleConnectorRebasedRuling w a d) s =
      deriv d s • w (a s) + (d s * deriv a s) • deriv w (a s) := by
  have hwa := ((hw.differentiable (by simp) (a s)).hasDerivAt).scomp s
    (ha.differentiable (by simp) s).hasDerivAt
  have h := ((hd.differentiable (by simp) s).hasDerivAt).smul hwa
  change HasDerivAt (visibleConnectorRebasedRuling w a d) _ s at h
  rw [h.deriv]
  simp only [Function.comp_apply]
  module

/-- Exact A and Delta transport; these are actual source determinant formulas. -/
theorem visibleConnector_rebase_determinants {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d) (s u : ℝ) :
    visibleConnectorA (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) s =
        deriv a s * d s * visibleConnectorDelta p gamma w (![a s, b s] : Coord) ∧
    visibleConnectorDelta (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) =
        deriv a s * d s * visibleConnectorDelta p gamma w (![a s, b s + u * d s] : Coord) := by
  have hp' := visibleConnector_rebased_source_deriv hp hw ha hb s
  have hw' := visibleConnector_rebased_ruling_deriv hw ha hd s
  constructor
  · rw [visibleConnectorA, hp', rebase_delta_geometry]
    simp only [visibleConnectorRebasedRuling, Matrix.cons_val_zero, Matrix.cons_val_one,
      visibleConnectorDet, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [rebase_delta_geometry, rebase_delta_geometry]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hp', hw']
    simp only [visibleConnectorRebasedRuling, visibleConnectorDet,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The height trace keeps the actual gradient jet after the rebase. -/
theorem visibleConnector_rebase_value_deriv {g a b : ℝ → ℝ} {p gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hp : ContDiff ℝ ∞ p)
    (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (s : ℝ) (hD : visibleConnectorDelta p gamma w (![a s, b s] : Coord) ≠ 0) :
    deriv (visibleConnectorRebasedHeight g gamma w a b) s =
      visibleConnectorRebasedGradient p gamma w a b s ⬝ᵥ
        deriv (visibleConnectorRebasedSource p w a b) s := by
  let q := (![a s, b s] : Coord)
  have hFirst := visibleConnector_actual_first_jets hg hp hgamma hw hvalue q hD
  have hq := rebase_parameter_deriv ha hb s
  have hH := ((visibleConnectorHeight_contDiff hg hgamma hw).differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt s hq
  have hP := ((visibleConnectorSource_contDiff hp hw).differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt s hq
  have hv : (![deriv a s, deriv b s] : Coord) =
      deriv a s • (Pi.single 0 1 : Coord) + deriv b s • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  change HasDerivAt (visibleConnectorRebasedHeight g gamma w a b) _ s at hH
  change HasDerivAt (visibleConnectorRebasedSource p w a b) _ s at hP
  rw [hH.deriv, hP.deriv, hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  change deriv a s * coordPartial 0 (visibleConnectorHeight g gamma w) q +
      deriv b s * coordPartial 1 (visibleConnectorHeight g gamma w) q =
    visibleConnectorGradient p gamma w q ⬝ᵥ
      (deriv a s • coordPartial 0 (visibleConnectorSource p w) q +
        deriv b s • coordPartial 1 (visibleConnectorSource p w) q)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hFirst 0, hFirst 1]
  simp only [smul_eq_mul]

/-- The actual new B is obtained by differentiating the retained old gradient.
The lower-graph derivative b' cancels through Jw dot w = 0. -/
theorem visibleConnector_rebase_B {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hD : ∀ s, visibleConnectorDelta p gamma w (![a s, b s] : Coord) ≠ 0) (s : ℝ) :
    visibleConnectorB (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) s =
        deriv a s * d s * visibleConnectorA p w (a s) * visibleConnectorB gamma w (a s) /
          visibleConnectorDelta p gamma w (![a s, b s] : Coord) := by
  let c : ℝ → ℝ := fun t => b t * visibleConnectorB gamma w (a t) /
    visibleConnectorDelta p gamma w (![a t, b t] : Coord)
  have hDb : ContDiff ℝ ∞ (fun t => visibleConnectorDelta p gamma w (![a t, b t] : Coord)) :=
    ((visibleConnectorA_contDiff hp hw).comp ha).add
      (hb.mul (((visibleConnectorB_contDiff hgamma hw).sub
        (visibleConnectorC_contDiff hgamma hw)).comp ha))
  have hc : ContDiff ℝ ∞ c :=
    (hb.mul ((visibleConnectorB_contDiff hgamma hw).comp ha)).div hDb hD
  have hga := ((hgamma.differentiable (by simp) (a s)).hasDerivAt).scomp s
    (ha.differentiable (by simp) s).hasDerivAt
  have hwa := ((hw.differentiable (by simp) (a s)).hasDerivAt).scomp s
    (ha.differentiable (by simp) s).hasDerivAt
  have hJwa : HasDerivAt (fun t => visibleConnectorJ (w (a t)))
      (deriv a s • visibleConnectorJ (deriv w (a s))) s := by
    simpa [visibleConnectorJ, Pi.smul_apply, smul_eq_mul] using visibleConnectorJ_hasDerivAt hwa
  have hG := hga.add (((hc.differentiable (by simp) s).hasDerivAt).smul hJwa)
  change HasDerivAt (visibleConnectorRebasedGradient p gamma w a b) _ s at hG
  have hmid : visibleConnectorB (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) s =
        deriv a s * d s * (visibleConnectorB gamma w (a s) +
          c s * visibleConnectorDet (deriv w (a s)) (w (a s))) := by
    rw [visibleConnectorB, hG.deriv]
    simp only [visibleConnectorRebasedRuling, add_dotProduct, smul_dotProduct, dotProduct_smul,
      visibleConnectorJ_dot_self, visibleConnectorJ_dot]
    simp only [visibleConnectorB, visibleConnectorDet]
    ring
  rw [hmid]
  dsimp only [c]
  have hDs := hD s
  field_simp [hDs]
  simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
    visibleConnectorC]
  ring

/-- Strict actual old A/B/Delta signs give the corresponding new signs,
including when the original lower graph has negative b. -/
theorem visibleConnector_rebase_positive {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hap : ∀ s, 0 < deriv a s) (hdp : ∀ s, 0 < d s)
    (hA : ∀ s, 0 < visibleConnectorA p w (a s))
    (hB : ∀ s, 0 < visibleConnectorB gamma w (a s))
    (hDb : ∀ s, 0 < visibleConnectorDelta p gamma w (![a s, b s] : Coord))
    (s u : ℝ) (hDu : 0 < visibleConnectorDelta p gamma w (![a s, b s + u * d s] : Coord)) :
    0 < visibleConnectorA (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) s ∧
      0 < visibleConnectorB (visibleConnectorRebasedGradient p gamma w a b)
        (visibleConnectorRebasedRuling w a d) s ∧
      0 < visibleConnectorDelta (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedGradient p gamma w a b)
        (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) := by
  obtain ⟨hAA, hDD⟩ := visibleConnector_rebase_determinants (gamma := gamma) hp hw ha hb hd s u
  rw [hAA, visibleConnector_rebase_B hp hgamma hw ha hb hd (fun t => (hDb t).ne') s, hDD]
  exact ⟨mul_pos (mul_pos (hap s) (hdp s)) (hDb s),
    div_pos (mul_pos (mul_pos (mul_pos (hap s) (hdp s)) (hA s)) (hB s)) (hDb s),
    mul_pos (mul_pos (hap s) (hdp s)) hDu⟩

/-- The explicit rebased gradient is the SAME actual old gradient at the
rebased raw point, not an independent prescribed gradient field. -/
theorem visibleConnector_rebase_gradient {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hDb : ∀ s, visibleConnectorDelta p gamma w (![a s, b s] : Coord) ≠ 0)
    (hap : ∀ s, deriv a s ≠ 0) (hdp : ∀ s, d s ≠ 0)
    (s u : ℝ) (hDu : visibleConnectorDelta p gamma w (![a s, b s + u * d s] : Coord) ≠ 0) :
    visibleConnectorGradient (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord) =
    visibleConnectorGradient p gamma w (![a s, b s + u * d s] : Coord) := by
  have hB := visibleConnector_rebase_B hp hgamma hw ha hb hd hDb s
  have hDelta := (visibleConnector_rebase_determinants (gamma := gamma) hp hw ha hb hd s u).2
  change visibleConnectorRebasedGradient p gamma w a b s +
      (u * visibleConnectorB (visibleConnectorRebasedGradient p gamma w a b)
        (visibleConnectorRebasedRuling w a d) s /
        visibleConnectorDelta (visibleConnectorRebasedSource p w a b)
          (visibleConnectorRebasedGradient p gamma w a b)
          (visibleConnectorRebasedRuling w a d) (![s, u] : Coord)) •
        visibleConnectorJ (visibleConnectorRebasedRuling w a d s) = _
  rw [hB, hDelta]
  simp only [visibleConnectorRebasedGradient, visibleConnectorRebaseParameter,
    Function.comp_apply, visibleConnectorGradient, visibleConnectorRebasedRuling,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ext i
  fin_cases i <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, visibleConnectorJ,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    dsimp <;>
    field_simp [hDb s, hDu, hap s, hdp s] <;>
    simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

private theorem rebase_deriv_periodic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {L : ℝ} (hL : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hL
  have hd := congrArg (fun F : ℝ → V => deriv F s) he
  simpa only [deriv_comp_add_const] using hd

/-- Full-period phase equivariance and the actual old periods give periods for
ALL FOUR rebased functions, including the retained gradient. -/
theorem visibleConnector_rebase_periodic {L : ℝ} {g a b d : ℝ → ℝ} {p gamma w : ℝ → Coord}
    (hpL : Periodic p L) (hgL : Periodic g L) (hgammaL : Periodic gamma L)
    (hwL : Periodic w L) (hshift : ∀ s, a (s + L) = a s + L)
    (hbL : Periodic b L) (hdL : Periodic d L) :
    Periodic (visibleConnectorRebasedSource p w a b) L ∧
      Periodic (visibleConnectorRebasedHeight g gamma w a b) L ∧
      Periodic (visibleConnectorRebasedRuling w a d) L ∧
      Periodic (visibleConnectorRebasedGradient p gamma w a b) L := by
  have hdpL := rebase_deriv_periodic hpL
  have hdgL := rebase_deriv_periodic hgammaL
  have hdwL := rebase_deriv_periodic hwL
  have hAL : Periodic (visibleConnectorA p w) L := by
    intro s
    simp only [visibleConnectorA, hdpL s, hwL s]
  have hBL : Periodic (visibleConnectorB gamma w) L := by
    intro s
    simp only [visibleConnectorB, hdgL s, hwL s]
  have hCL : Periodic (visibleConnectorC gamma w) L := by
    intro s
    simp only [visibleConnectorC, hBL s, hdwL s, hwL s]
  have hDeltaL (s u : ℝ) : visibleConnectorDelta p gamma w (![s + L, u] : Coord) =
      visibleConnectorDelta p gamma w (![s, u] : Coord) := by
    simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
      hAL s, hBL s, hCL s]
  have hGradientL (s u : ℝ) : visibleConnectorGradient p gamma w (![s + L, u] : Coord) =
      visibleConnectorGradient p gamma w (![s, u] : Coord) := by
    simp only [visibleConnectorGradient, Matrix.cons_val_zero, Matrix.cons_val_one,
      hgammaL s, hBL s, hDeltaL s u, hwL s]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    change p (a (s + L)) + b (s + L) • w (a (s + L)) = p (a s) + b s • w (a s)
    rw [hshift s, hbL s, hpL (a s), hwL (a s)]
  · intro s
    change g (a (s + L)) + b (s + L) * (gamma (a (s + L)) ⬝ᵥ w (a (s + L))) =
      g (a s) + b s * (gamma (a s) ⬝ᵥ w (a s))
    rw [hshift s, hbL s, hgL (a s), hgammaL (a s), hwL (a s)]
  · intro s
    change d (s + L) • w (a (s + L)) = d s • w (a s)
    rw [hshift s, hdL s, hwL (a s)]
  · intro s
    change visibleConnectorGradient p gamma w (![a (s + L), b (s + L)] : Coord) =
      visibleConnectorGradient p gamma w (![a s, b s] : Coord)
    rw [hshift s, hbL s, hGradientL]
end
end TightVer401
