import TightVer401.DualRadialCompletionExitApplicationGeometry
import TightVer401.DualRadialCompletionExitApplicationCollar

/-! Construct the ordinary completion inputs from the SAME returned exit
data, retaining its source and reversed-gradient annuli and protected core. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix RealInnerProductSpace

variable {T w delta : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G : Coord → ℝ} {U : Set Coord}
    {e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {he : e.source = univ} {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0}
    {hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w}
    {O : Set Coord} {xi : ℝ}

/-- An OUTPUT of the actual exit adapter, containing ordinary completion
inputs. It contains no completed potential, filling or connector witness. -/
structure DualRadialCompletionExitApplicationInputs
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) where
  E : OpenPartialHomeomorph Coord Coord
  HpPlus : ℂ ≃ₜ ℂ
  HpMinus : ℂ ≃ₜ ℂ
  HgPlus : ℂ ≃ₜ ℂ
  HgMinus : ℂ ≃ₜ ℂ
  closed_in_source : closure X.source_annulus ⊆ E.source
  source_in_domain : E.source ⊆ X.Uexit
  smooth : ContDiffOn ℝ ∞ X.Gexit E.source
  saddle : ∀ q ∈ E.source, (planarHessian X.Gexit q).det < 0
  actual_gradient : (E : Coord → Coord) = planarGradient X.Gexit
  inverse_smooth : ContDiffOn ℝ ∞ E.symm E.target
  gradient_in_target : X.gradient_annulus ⊆ E.target
  forward_agreement : EqOn E X.gradient_chart X.source_annulus
  inverse_agreement : EqOn E.symm X.gradient_chart.symm X.gradient_annulus
  p_plus : DualRadialCompletionPositiveTrace HpPlus
    (fun t => positiveExitComplexTrace X.outer.p (X.outer_return.period*t))
  p_minus : DualRadialCompletionPositiveTrace HpMinus
    (fun t => positiveExitComplexTrace X.inner.p (X.inner_return.period*t))
  g_plus : DualRadialCompletionPositiveTrace HgPlus
    (fun t => positiveExitComplexTrace X.outer.gamma (X.outer_return.period*t))
  g_minus : DualRadialCompletionPositiveTrace HgMinus
    (fun t => positiveExitComplexTrace X.inner.gamma (X.inner_return.period*t))
  source_outer_inside : positiveExitInside X.outer.p = seamComplexCoord '' (HpPlus '' ball (0 : ℂ) 1)
  source_inner_inside : positiveExitInside X.inner.p = seamComplexCoord '' (HpMinus '' ball (0 : ℂ) 1)
  gradient_outer_inside : positiveExitInside X.outer.gamma = seamComplexCoord '' (HgPlus '' ball (0 : ℂ) 1)
  gradient_inner_inside : positiveExitInside X.inner.gamma = seamComplexCoord '' (HgMinus '' ball (0 : ℂ) 1)
  source_nested : closure (HpMinus '' ball (0 : ℂ) 1) ⊆ HpPlus '' ball (0 : ℂ) 1
  gradient_nested : closure (HgPlus '' ball (0 : ℂ) 1) ⊆ HgMinus '' ball (0 : ℂ) 1
  source_origin : (0 : ℂ) ∈ HpMinus '' ball (0 : ℂ) 1
  gradient_origin : (0 : ℂ) ∈ HgPlus '' ball (0 : ℂ) 1
  source_annulus_eq : X.source_annulus = annularCoordJordanInterior HpPlus HpMinus
  gradient_annulus_eq : X.gradient_annulus = annularCoordJordanInterior HgMinus HgPlus
  closed_annulus_eq : closure X.source_annulus = annularCoordJordanClosure HpPlus HpMinus
  core_compact : IsCompact (e '' tsupport Y)
  core_in_annulus : e '' tsupport Y ⊆ annularCoordJordanInterior HpPlus HpMinus

theorem exists_dualRadialCompletionExitApplication_inputs
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) :
    Nonempty (DualRadialCompletionExitApplicationInputs X) := by
  obtain ⟨HpPlus,HgPlus,hpPlus,hgPlus,hpPlus0,hgPlus0,hInsidePlus,hGradientPlus⟩ :=
    dualRadialCompletionExitApplicationPeriod_positive_traces X.outer
  obtain ⟨HpMinus,HgMinus,hpMinus,hgMinus,hpMinus0,hgMinus0,hInsideMinus,hGradientMinus⟩ :=
    dualRadialCompletionExitApplicationPeriod_positive_traces X.inner
  obtain ⟨E,hClosed,hDomain,hSmooth,hSaddle,hActual,hInverse,hTarget,hForward,hAgreement⟩ :=
    exists_dualRadialCompletion_exit_application_collar X
  have hNested := dualRadialCompletionExitApplication_nested
    hInsidePlus hInsideMinus X.source_nesting
  have hGNested := dualRadialCompletionExitApplication_nested
    hGradientMinus hGradientPlus X.gradient_nesting
  have hSource : X.source_annulus = annularCoordJordanInterior HpPlus HpMinus :=
    X.source_annulus_eq.trans (dualRadialCompletionExitApplication_annulus hInsidePlus hInsideMinus)
  have hGradient : X.gradient_annulus = annularCoordJordanInterior HgMinus HgPlus :=
    X.gradient_annulus_eq.trans (dualRadialCompletionExitApplication_annulus hGradientMinus hGradientPlus)
  have hClosure : closure X.source_annulus = annularCoordJordanClosure HpPlus HpMinus := by
    rw [hSource]
    exact closure_annularCoordJordanInterior HpPlus HpMinus hNested
  have hCore : IsCompact (e '' tsupport Y) :=
    X.same_native_compact_support.image_of_continuousOn
      (e.continuousOn.mono (by rw [he]; exact subset_univ _))
  have hCoreIn : e '' tsupport Y ⊆ annularCoordJordanInterior HpPlus HpMinus := by
    rw [← hSource]
    exact X.protected_support.trans X.protected_in_annulus
  exact ⟨⟨E,HpPlus,HpMinus,HgPlus,HgMinus,hClosed,hDomain,hSmooth,hSaddle,hActual,
    hInverse,hTarget,hForward,hAgreement,hpPlus,hpMinus,hgPlus,hgMinus,
    hInsidePlus,hInsideMinus,hGradientPlus,hGradientMinus,hNested,hGNested,
    hpMinus0,hgPlus0,hSource,hGradient,hClosure,hCore,hCoreIn⟩⟩

end
end TightVer401
