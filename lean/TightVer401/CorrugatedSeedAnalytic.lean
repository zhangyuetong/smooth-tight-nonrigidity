import TightVer401.CorrugatedSeedClosure

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff

theorem corrugatedSeedBeta_contDiff_analytic (N : ℝ) :
    ContDiff ℝ ω (corrugatedSeedBeta N) := by
  unfold corrugatedSeedBeta corrugatedSeedPhase corrugatedSeedRadius
  change ContDiff ℝ ω (fun t => Complex.ofRealCLM (1 + (1 / N) * Real.sin (N * t)) *
    Complex.exp (Complex.ofRealCLM (t + 2 * (1 / N) * Real.sin (N * t)) * Complex.I))
  fun_prop

def corrugatedSeedEntireVelocity (k N : ℝ) (z : ℂ) : ℂ :=
  (corrugatedSeedNormalization k : ℂ)⁻¹ * Complex.exp (-(k : ℂ) * Complex.cos ((N : ℂ) * z)) *
    (Complex.exp ((z + 2 * (1 / (N : ℂ)) * Complex.sin ((N : ℂ) * z)) * Complex.I) *
      (Complex.cos ((N : ℂ) * z) + Complex.I *
        (1 + (1 / (N : ℂ)) * Complex.sin ((N : ℂ) * z)) *
        (1 + 2 * Complex.cos ((N : ℂ) * z))))

theorem corrugatedSeedEntireVelocity_differentiable (k N : ℝ) :
    Differentiable ℂ (corrugatedSeedEntireVelocity k N) := by
  unfold corrugatedSeedEntireVelocity
  fun_prop

theorem corrugatedSeedEntireVelocity_ofReal (k N t : ℝ) :
    corrugatedSeedEntireVelocity k N (t : ℂ) = corrugatedSeedDeltaVelocity k N t := by
  simp only [corrugatedSeedEntireVelocity, corrugatedSeedDeltaVelocity,
    corrugatedSeedMultiplier, corrugatedSeedBetaVelocity, corrugatedSeedRadius,
    corrugatedSeedPhase, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_inv, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_exp,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_neg]

theorem corrugatedSeedDelta_contDiff_analytic (k N : ℝ) :
    ContDiff ℝ ω (corrugatedSeedDelta k N) := by
  obtain ⟨g, hg⟩ := (corrugatedSeedEntireVelocity_differentiable k N).isExactOn_univ
  have hgc : Differentiable ℂ g := fun z => (hg z (mem_univ z)).differentiableAt
  have hgr (t : ℝ) : HasDerivAt (fun s : ℝ => g (s : ℂ))
      (corrugatedSeedDeltaVelocity k N t) t := by
    have h := (hg (t : ℂ) (mem_univ _)).comp_ofReal
    rw [corrugatedSeedEntireVelocity_ofReal] at h
    exact h
  have hga : ContDiff ℝ ω (fun t : ℝ => g (t : ℂ)) := by
    apply AnalyticOnNhd.contDiff
    intro t _
    exact (hgc.analyticAt (t : ℂ)).restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => corrugatedSeedDelta k N s - g (s : ℂ)) 0 t := by
    have h := (corrugatedSeedDelta_hasDerivAt k N t).sub (hgr t)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun s : ℝ => corrugatedSeedDelta k N s - g (s : ℂ))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact (sub_self (corrugatedSeedDeltaVelocity k N t)) ▸ h'
  have he : corrugatedSeedDelta k N = fun t : ℝ =>
      g (t : ℂ) + (corrugatedSeedDelta k N 0 - g (0 : ℂ)) := by
    funext t
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [Complex.ofReal_zero, add_comm] using (sub_eq_iff_eq_add.mp h)
  rw [he]
  exact hga.add contDiff_const

theorem corrugatedSeedPartner_contDiff_analytic (N : ℝ) :
    ContDiff ℝ ω (corrugatedSeedPartner N) := corrugatedSeedDelta_contDiff_analytic _ _

end
end TightVer401
