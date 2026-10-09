import TightVer401.PositiveExitConstructionSelectedSourceGeometryPhase
import TightVer401.PositiveExitConstructionSelectedHomotopyFermi
import TightVer401.PositiveExitConstructionSelectedHomotopyJoin
import TightVer401.QuadraticRadialFillingCircle

/-! Actual protected-point avoidance of the SAME explicit Fermi graph
homotopy. The label tube and graph amplitude budget produce avoidance for
every intermediate loop; protected avoidance and final core placement are
not inputs. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The SAME seam-to-graph homotopy stays outside the protected set, by
label separation at every scaled graph height. -/
theorem positiveExitSelected_fermi_homotopy_avoids_protected
    {P : ℝ} [Fact (0 < P)] {G : Coord → ℝ} {U : Set Coord}
    {ζ : ℝ → Ambient} {hp : Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvP : Periodic v P) (δ : ℝ)
    (hstrip : ∀ r ∈ Icc (0 : ℝ) P, |δ * v r| < D.rho)
    {L : Coord → ℝ} {C : Set Coord} {c ε ρ : ℝ}
    (htube : ∀ r x : ℝ, |x| ≤ ρ → |L (positiveExitFermiSource ζ ![r, x]) - c| < ε)
    (hgap : ∀ q ∈ C, ε ≤ |L q - c|)
    (hbudget : ∀ r ∈ Icc (0 : ℝ) P, |δ * v r| ≤ ρ) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ a t, H a t = angularDescentComplex (positiveExitFermiSource ζ
        (![P*(t : ℝ), (a : ℝ)*(δ*v (P*(t : ℝ)))] : Coord))) ∧
      (∀ t, H 0 t = angularDescentComplex (gnomonicInverse (ζ (P*(t : ℝ))))) ∧
      (∀ t, H 1 t = angularDescentComplex (positiveExitFermiSource ζ
        (exitGraphCurve v δ (P*(t : ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      (∀ a t, H a t ∈ angularDescentComplex '' U) ∧
      ∀ a t q, q ∈ C → H a t ≠ angularDescentComplex q := by
  obtain ⟨H, hformula, h0, h1, hclosed, hU⟩ :=
    positiveExit_actual_fermi_graph_source_homotopy D hv hvP δ hstrip
  refine ⟨H, hformula, h0, h1, hclosed, hU, ?_⟩
  intro a t q hq heq
  have hr : P*(t : ℝ) ∈ Icc (0 : ℝ) P :=
    ⟨mul_nonneg (Fact.out : 0 < P).le t.property.1,
      by nlinarith [t.property.2, (Fact.out : 0 < P)]⟩
  have ha : |(a : ℝ)*(δ*v (P*(t : ℝ)))| ≤ |δ*v (P*(t : ℝ))| := by
    rw [abs_mul, abs_of_nonneg a.property.1]
    exact mul_le_of_le_one_left (abs_nonneg _) a.property.2
  have hb := htube (P*(t : ℝ)) ((a : ℝ)*(δ*v (P*(t : ℝ))))
    (ha.trans (hbudget _ hr))
  rw [hformula a t] at heq
  have hpoint := congrArg seamComplexCoord heq
  rw [quadraticRadialFillingCoord_complex, quadraticRadialFillingCoord_complex] at hpoint
  rw [hpoint] at hb
  exact (not_lt_of_ge (hgap q hq)) hb

/-- Reverse that SAME constructed homotopy to run from the actual graph to
its seam, retaining all protected-point avoidance and the original period. -/
theorem positiveExitSelected_graph_to_seam_avoids_protected
    {P : ℝ} [Fact (0 < P)] {G : Coord → ℝ} {U : Set Coord}
    {ζ : ℝ → Ambient} {hp : Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvP : Periodic v P) (δ : ℝ)
    (hstrip : ∀ r ∈ Icc (0 : ℝ) P, |δ * v r| < D.rho)
    {L : Coord → ℝ} {C : Set Coord} {c ε ρ : ℝ}
    (htube : ∀ r x : ℝ, |x| ≤ ρ → |L (positiveExitFermiSource ζ ![r, x]) - c| < ε)
    (hgap : ∀ q ∈ C, ε ≤ |L q - c|)
    (hbudget : ∀ r ∈ Icc (0 : ℝ) P, |δ * v r| ≤ ρ) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ t, H 0 t = angularDescentComplex (positiveExitFermiSource ζ
        (exitGraphCurve v δ (P*(t : ℝ))))) ∧
      (∀ t, H 1 t = angularDescentComplex (gnomonicInverse (ζ (P*(t : ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      (∀ a t, H a t ∈ angularDescentComplex '' U) ∧
      ∀ a t q, q ∈ C → H a t ≠ angularDescentComplex q := by
  obtain ⟨F, _hformula, h0, h1, hclosed, hU, havoid⟩ :=
    positiveExitSelected_fermi_homotopy_avoids_protected D hv hvP δ hstrip htube hgap hbudget
  have hsafe : ∀ a t, F a t ∈ (angularDescentComplex '' U) \ (angularDescentComplex '' C) := by
    intro a t
    refine ⟨hU a t, ?_⟩
    rintro ⟨q, hq, heq⟩
    exact havoid a t q hq heq.symm
  obtain ⟨H, hH0, hH1, hHclosed, hHsafe⟩ :=
    positiveExit_actual_loop_homotopy_symm F hclosed hsafe
  refine ⟨H, ?_, ?_, hHclosed, fun a t => (hHsafe a t).1, ?_⟩
  · intro t
    exact (congrArg (fun f : C(unitInterval, ℂ) => f t) hH0).trans (h1 t)
  · intro t
    exact (congrArg (fun f : C(unitInterval, ℂ) => f t) hH1).trans (h0 t)
  · intro a t q hq heq
    exact (hHsafe a t).2 ⟨q, hq, heq.symm⟩

/-- Clock interpolation stays on the SAME labelled raw leaf, so it too
avoids every protected point with a strict label gap. Its endpoint clock
identities and physical normalization are preserved literally. -/
theorem positiveExitSelected_seam_clock_avoids_protected
    {T P : ℝ} {ξ : ℝ → Ambient} (hξ : ContDiff ℝ ∞ ξ) (hξT : Periodic ξ T)
    (hnorth : ∀ s, 0 < ξ s 2) {U : Set Coord}
    (hsource : ∀ s, gnomonicInverse (ξ s) ∈ U)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) (hψP : ψ P = T)
    {L : Coord → ℝ} {C : Set Coord} {c ε : ℝ} (hε : 0 < ε)
    (hlabel : ∀ s, L (gnomonicInverse (ξ s)) = c)
    (hgap : ∀ q ∈ C, ε ≤ |L q - c|) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ a t, H a t = angularDescentComplex (gnomonicInverse
        (ξ ((1-(a:ℝ))*ψ (P*(t:ℝ)) + (a:ℝ)*(T*(t:ℝ)))))) ∧
      (∀ t, H 0 t = angularDescentComplex (gnomonicInverse (ξ (ψ (P*(t:ℝ)))))) ∧
      (∀ t, H 1 t = angularDescentComplex (gnomonicInverse (ξ (T*(t:ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      (∀ a t, H a t ∈ angularDescentComplex '' U) ∧
      ∀ a t q, q ∈ C → H a t ≠ angularDescentComplex q := by
  obtain ⟨H, hformula, h0, h1, hclosed, hU⟩ :=
    positiveExit_actual_seam_clock_source_homotopy hξ hξT hnorth hsource hψ hψ0 hψP
  refine ⟨H, hformula, h0, h1, hclosed, hU, ?_⟩
  intro a t q hq heq
  rw [hformula a t] at heq
  have hpoint := congrArg seamComplexCoord heq
  rw [quadraticRadialFillingCoord_complex, quadraticRadialFillingCoord_complex] at hpoint
  have hL := hlabel ((1-(a:ℝ))*ψ (P*(t:ℝ)) + (a:ℝ)*(T*(t:ℝ)))
  rw [hpoint] at hL
  have hg := hgap q hq
  rw [hL, sub_self, abs_zero] at hg
  exact (not_le_of_gt hε) hg
end
end TightVer401

