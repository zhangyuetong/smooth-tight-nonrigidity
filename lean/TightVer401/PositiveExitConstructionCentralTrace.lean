import TightVer401.IdentityBandCentralSupport
import TightVer401.PlanarTrace

/-! Actual baseline traces of the same two-sided Cartesian support potential.
The smooth source trace is obtained by restricting its constructed raw chart;
the gradient trace is the actual horizontal projection of the central frame.
No exit, visibility lift or independently prescribed trace is assumed here. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency true

def identityBandCentralSourceTrace {T : ℝ} (d : PeriodicRuledFrame T) (s : ℝ) : Coord :=
  gnomonicInverse (d.n s)

def identityBandCentralGradientTrace {T : ℝ} (d : PeriodicRuledFrame T) (s : ℝ) : Coord :=
  identityBandPlanarHorizontalCLM (d.γ s)

def identityBandCentralValueTrace {T : ℝ} (d : PeriodicRuledFrame T)
    (G : Coord → ℝ) (s : ℝ) : ℝ := G (identityBandCentralSourceTrace d s)

theorem identityBandCentralSourceTrace_eq_raw {T : ℝ} (d : PeriodicRuledFrame T)
    (s : ℝ) :
    identityBandCentralSourceTrace d s = identityBandCentralCoordinates d (![s, 0] : Coord) := by
  change gnomonicInverse (d.n s) = gnomonicInverse (d.rawGaussMap (![s, 0] : Coord))
  rw [show d.rawGaussMap (![s, 0] : Coord) = d.n s from
    ruledNormal_zero (d.T s) (d.n s) (d.k s) (d.τ s)]

theorem identityBandCentralSourceTrace_periodic {T : ℝ} (d : PeriodicRuledFrame T) :
    Function.Periodic (identityBandCentralSourceTrace d) T := by
  intro s
  dsimp [identityBandCentralSourceTrace]
  rw [d.period_n s]

theorem identityBandCentralGradientTrace_contDiff {T : ℝ} (d : PeriodicRuledFrame T) :
    ContDiff ℝ ∞ (identityBandCentralGradientTrace d) :=
  identityBandPlanarHorizontalCLM.contDiff.comp d.smooth_γ

theorem identityBandCentralGradientTrace_periodic {T : ℝ} (d : PeriodicRuledFrame T) :
    Function.Periodic (identityBandCentralGradientTrace d) T := by
  intro s
  dsimp [identityBandCentralGradientTrace]
  rw [d.period_γ s]

theorem identityBandCentralGradientTrace_hasDerivAt {T : ℝ} (d : PeriodicRuledFrame T)
    (s : ℝ) : HasDerivAt (identityBandCentralGradientTrace d)
      (identityBandPlanarHorizontalCLM (d.T s)) s :=
  identityBandPlanarHorizontalCLM.hasFDerivAt.comp_hasDerivAt s (d.deriv_γ s)

theorem identityBandCentralSourceTrace_contDiff {T w : ℝ} (d : PeriodicRuledFrame T)
    (hw : 0 < w)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w)) :
    ContDiff ℝ ∞ (identityBandCentralSourceTrace d) := by
  have hpath : ContDiff ℝ ∞ (fun s : ℝ => (![s, 0] : Coord)) := by
    let L : ℝ →L[ℝ] Coord := ContinuousLinearMap.toSpanSingleton ℝ (Pi.single 0 1 : Coord)
    have he : (fun s : ℝ => (![s, 0] : Coord)) = L := by
      ext s i
      fin_cases i <;> simp [L]
    rw [he]
    exact L.contDiff
  have hmap : MapsTo (fun s : ℝ => (![s, 0] : Coord)) univ
      (identityBandCentralRawDomain w) := by
    intro s _
    change (0 : ℝ) ∈ Ioo (-w) w
    constructor <;> linarith
  have heq : (identityBandCentralCoordinates d ∘ fun s : ℝ => (![s, 0] : Coord)) =
      identityBandCentralSourceTrace d := by
    funext s
    exact (identityBandCentralSourceTrace_eq_raw d s).symm
  rw [← heq]
  exact contDiffOn_univ.mp (hP.comp hpath.contDiffOn hmap)

theorem identityBandCentralSourceTrace_mapsTo {T w : ℝ} (d : PeriodicRuledFrame T)
    (hw : 0 < w) {U : Set Coord}
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U) :
    MapsTo (identityBandCentralSourceTrace d) univ U := by
  intro s _
  rw [identityBandCentralSourceTrace_eq_raw]
  apply hPU
  change (0 : ℝ) ∈ Ioo (-w) w
  constructor <;> linarith

/-- The actual reconstructed surface fixes the entire central gradient trace. -/
theorem identityBandCentralGradientTrace_eq_gradient {T w : ℝ}
    (d : PeriodicRuledFrame T) (hw : 0 < w) {G : Coord → ℝ}
    (hrec : EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d)
      (ruledMap d.γ d.E) (identityBandCentralRawDomain w)) (s : ℝ) :
    identityBandCentralGradientTrace d s = planarGradient G (identityBandCentralSourceTrace d s) := by
  have hs : (![s, 0] : Coord) ∈ identityBandCentralRawDomain w := by
    change (0 : ℝ) ∈ Ioo (-w) w
    constructor <;> linarith
  have he := hrec hs
  change planarSupportMap G (identityBandCentralCoordinates d (![s, 0] : Coord)) =
    d.γ s + (0 : ℝ) • d.E s at he
  simp only [zero_smul, add_zero] at he
  rw [identityBandCentralSourceTrace_eq_raw]
  ext i
  have hi := congrArg (fun x : Ambient => x (Fin.castSucc i)) he
  fin_cases i <;> simpa [identityBandCentralGradientTrace, identityBandPlanarHorizontalCLM,
    planarSupportMap, planarGradient, ContinuousLinearMap.pi_apply, PiLp.proj_apply] using hi.symm

/-- Smooth periodic actual source, gradient and scalar traces of the SAME
constructed potential, with its actual derivative correspondence and action. -/
theorem identityBandCentralSupport_central_traces {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) {a κ : ℝ → ℝ} {S : ℝ ≃ₜ ℝ}
    {G : Coord → ℝ} {U : Set Coord} (hw : 0 < w)
    (hc : IdentityBandCentralSupportWithPotential d w a κ S G U) :
    ContDiff ℝ ∞ (identityBandCentralSourceTrace d) ∧
      Function.Periodic (identityBandCentralSourceTrace d) T ∧
      MapsTo (identityBandCentralSourceTrace d) univ U ∧
      ContDiff ℝ ∞ (identityBandCentralGradientTrace d) ∧
      Function.Periodic (identityBandCentralGradientTrace d) T ∧
      (∀ s, identityBandCentralGradientTrace d s =
        planarGradient G (identityBandCentralSourceTrace d s)) ∧
      ContDiff ℝ ∞ (identityBandCentralValueTrace d G) ∧
      Function.Periodic (identityBandCentralValueTrace d G) T ∧
      (∀ s, deriv (identityBandCentralGradientTrace d) s =
        planarHessian G (identityBandCentralSourceTrace d s) *ᵥ
          deriv (identityBandCentralSourceTrace d) s) ∧
      (∀ s, deriv (identityBandCentralValueTrace d G) s =
        identityBandCentralGradientTrace d s ⬝ᵥ deriv (identityBandCentralSourceTrace d) s) ∧
      (∫ s in 0..T, identityBandCentralGradientTrace d s ⬝ᵥ
        deriv (identityBandCentralSourceTrace d) s) = 0 := by
  rcases hc with ⟨hU, _hUr, hG, _hcore, hP, hPU, hrec, _⟩
  have hp := identityBandCentralSourceTrace_contDiff d hw hP
  have hperiod := identityBandCentralSourceTrace_periodic d
  have hmap := identityBandCentralSourceTrace_mapsTo d hw hPU
  have hgrad := identityBandCentralGradientTrace_eq_gradient d hw hrec
  have heq : (fun s => planarGradient G (identityBandCentralSourceTrace d s)) =
      identityBandCentralGradientTrace d := by
    funext s
    exact (hgrad s).symm
  have hvalue : ContDiff ℝ ∞ (identityBandCentralValueTrace d G) :=
    contDiffOn_univ.mp (hG.comp hp.contDiffOn hmap)
  have hvalueperiod : Function.Periodic (identityBandCentralValueTrace d G) T := by
    intro s
    dsimp [identityBandCentralValueTrace]
    rw [hperiod s]
  refine ⟨hp, hperiod, hmap, identityBandCentralGradientTrace_contDiff d,
    identityBandCentralGradientTrace_periodic d, hgrad, hvalue, hvalueperiod, ?_, ?_, ?_⟩
  · intro s
    have hd := planarTrace_gradient_deriv hG hU (hmap (mem_univ s))
      (hp.differentiable (by simp) s)
    rw [heq] at hd
    exact hd
  · intro s
    change deriv (fun t => G (identityBandCentralSourceTrace d t)) s = _
    rw [planarTrace_value_deriv hG hU (hmap (mem_univ s))
      (hp.differentiable (by simp) s), ← hgrad s]
  · have hmapperiod : MapsTo (identityBandCentralSourceTrace d) (uIcc 0 T) U :=
      fun s _ => hmap (mem_univ s)
    have hz := planarTrace_periodic_action_zero hG hU hp hmapperiod hperiod
    simpa only [← hgrad] using hz

/-- Exact seed identification from the final frame's retained normal equation.
The two actual parameter changes remain visible in the formula. -/
theorem identityBandCentralSourceTrace_seed {T N : ℝ} (d : PeriodicRuledFrame T)
    (ψ : ℝ → ℝ) (S : ℝ ≃ₜ ℝ)
    (hn : d.n = (corrugatedSeedSphere N ∘ ψ) ∘ S.symm) (s : ℝ) :
    identityBandCentralSourceTrace d s =
      corrugatedComplexCoord (corrugatedSeedBeta N (ψ (S.symm s))) := by
  simp only [identityBandCentralSourceTrace, hn, Function.comp_apply,
    corrugatedSeedSphere, gnomonic_left_inverse]

/-- The corrected balanced partner is exactly the quarter-turn of the actual
central horizontal trace; this uses the retained corrected frame equation. -/
theorem identityBandCentralGradientTrace_balanced_partner {T N ell : ℝ}
    (d : PeriodicRuledFrame T) {ψ a : ℝ → ℝ} (S : ℝ ≃ₜ ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a)
    (hγ : d.γ = corrugatedSeedBalancedSpatial N ψ ell a ∘ S.symm) (s : ℝ) :
    corrugatedSeedBalancedPartner N ψ ell a (S.symm s) =
      Complex.I * (⟨identityBandCentralGradientTrace d s 0,
        identityBandCentralGradientTrace d s 1⟩ : ℂ) := by
  have hhorizontal := corrugatedSeedBalancedSpatial_horizontal N ell hψ ha (S.symm s)
  have hcoord : (⟨identityBandCentralGradientTrace d s 0,
      identityBandCentralGradientTrace d s 1⟩ : ℂ) = corrugatedAmbientHorizontal (d.γ s) := by
    apply Complex.ext <;>
      simp [identityBandCentralGradientTrace, identityBandPlanarHorizontalCLM,
        corrugatedAmbientHorizontal, ContinuousLinearMap.pi_apply, PiLp.proj_apply]
  rw [hcoord, hγ]
  simpa only [corrugatedSeedBalancedPartner, Function.comp_apply, hhorizontal]

end
end TightVer401
