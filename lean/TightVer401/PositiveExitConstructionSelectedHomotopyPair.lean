import TightVer401.PositiveExitConstructionSelectedHomotopyFermi
import TightVer401.PositiveExitConstructionSelectedHomotopyJoin

/-! The literal five-piece source homotopy of the two selected exits. The
clock equations and the same graph strip bounds are retained; no Jordan
fill, nesting, annulus or independent reparametrization is supplied. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

private theorem selectedHomotopyPair_complex_eq :
    positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

private theorem selectedHomotopyPair_clock_endpoints
    {T P : ℝ} (a : ℝ → ℝ) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive a) (hP : P = rawPrimitive a T) :
    S.symm 0 = 0 ∧ S.symm P = T := by
  have hS0 : S 0 = 0 := by rw [hS]; simp [rawPrimitive]
  have hST : S T = P := by rw [hS, hP]
  exact ⟨(congrArg S.symm hS0.symm).trans (S.symm_apply_apply 0),
    (congrArg S.symm hST.symm).trans (S.symm_apply_apply T)⟩

private theorem selectedHomotopyPair_graph_to_flow
    {T delta w P : ℝ} [Fact (0 < T)] [Fact (0 < P)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ q, e q = gnomonicInverse (d.bandGaussMap q))
    (hn : ∀ q : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap q 2)
    (z : Ioo (0 : ℝ) delta) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside z))
    (hP : P = rawPrimitive (positiveExitLeafSpeed d hb hinside z) T)
    {G : Coord → ℝ} {hp : Periodic (positiveExitRawLeaf d hb hinside z ∘ S.symm) P}
    {η ξ σ rhoMax : ℝ}
    (D : PositiveExitActualFermiData G e.target
      (positiveExitRawLeaf d hb hinside z ∘ S.symm) hp η ξ σ rhoMax)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvP : Periodic v P)
    (δ : ℝ) (p : ℝ → Coord)
    (hgraph : ∀ s, p s = positiveExitFermiSource
      (positiveExitRawLeaf d hb hinside z ∘ S.symm) (exitGraphCurve v δ s))
    (hstrip : ∀ s ∈ Icc (0 : ℝ) P, |δ*v s| < D.rho) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ t, H 0 t = positiveExitComplexTrace p (P*(t:ℝ))) ∧
      (∀ t, H 1 t = angularDescentComplex
        (e (positiveExitLeaf d hb hinside z (periodProjection T (T*(t:ℝ)))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      ∀ a t, H a t ∈ angularDescentComplex '' e.target := by
  obtain ⟨F, _hF, hF0, hF1, hFc, hFU⟩ :=
    positiveExit_actual_fermi_graph_source_homotopy D hv hvP δ hstrip
  obtain ⟨R, hR0, hR1, hRc, hRU⟩ :=
    positiveExit_actual_loop_homotopy_symm F hFc hFU
  obtain ⟨hS0, hSP⟩ := selectedHomotopyPair_clock_endpoints
    (positiveExitLeafSpeed d hb hinside z) S hS hP
  have hraw (s : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside z s) =
      e (positiveExitLeaf d hb hinside z (periodProjection T s)) :=
    positiveExitGaussLeaf_cartesian_source d hb e hinside heF z (periodProjection T s)
  have hsource (s : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside z s) ∈ e.target := by
    rw [hraw]
    apply e.mapsTo
    rw [heS]
    exact mem_univ _
  obtain ⟨C, _hC, hC0, hC1, hCc, hCU⟩ :=
    positiveExit_actual_seam_clock_source_homotopy
      (positiveExitRawLeaf_contDiff d hb hinside z)
      (positiveExitRawLeaf_periodic d hb hinside z)
      (fun s => positiveExitGaussLeaf_north d hb hinside z hn (periodProjection T s))
      hsource S.symm.continuous hS0 hSP
  have hjoin : R 1 = C 0 := by
    apply ContinuousMap.ext
    intro t
    calc
      R 1 t = F 0 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hR1
      _ = angularDescentComplex (gnomonicInverse
          ((positiveExitRawLeaf d hb hinside z ∘ S.symm) (P*(t:ℝ)))) := hF0 t
      _ = C 0 t := by simpa only [Function.comp_def] using (hC0 t).symm
  obtain ⟨H, hH0, hH1, hHc, hHU⟩ :=
    positiveExit_actual_loop_homotopy_trans R C hjoin hRc hCc hRU hCU
  refine ⟨H, ?_, ?_, hHc, hHU⟩
  · intro t
    calc
      H 0 t = R 0 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hH0
      _ = F 1 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hR0
      _ = angularDescentComplex (positiveExitFermiSource
          (positiveExitRawLeaf d hb hinside z ∘ S.symm) (exitGraphCurve v δ (P*(t:ℝ)))) := hF1 t
      _ = positiveExitComplexTrace p (P*(t:ℝ)) := by
        rw [← hgraph]
        simp only [positiveExitComplexTrace, Function.comp_def, selectedHomotopyPair_complex_eq]
  · intro t
    calc
      H 1 t = C 1 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hH1
      _ = angularDescentComplex (gnomonicInverse
          (positiveExitRawLeaf d hb hinside z (T*(t:ℝ)))) := hC1 t
      _ = angularDescentComplex
          (e (positiveExitLeaf d hb hinside z (periodProjection T (T*(t:ℝ))))) := by rw [hraw]

/-- Construct the actual graph-to-graph source homotopy from the SAME
selected leaves, clocks, Fermi data, literal profiles and chosen graph
heights. The two physical periods may differ. -/
theorem positiveExit_actual_selected_pair_source_homotopy
    {T delta w P1 P2 : ℝ} [Fact (0 < T)] [Fact (0 < P1)] [Fact (0 < P2)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ q, e q = gnomonicInverse (d.bandGaussMap q))
    (hn : ∀ q : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap q 2)
    (vin vout : Ioo (0 : ℝ) delta) (horder : (vin:ℝ) < (vout:ℝ))
    (S1 S2 : ℝ ≃ₜ ℝ)
    (hS1 : (S1 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vin))
    (hP1 : P1 = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) T)
    (hS2 : (S2 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vout))
    (hP2 : P2 = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) T)
    {G : Coord → ℝ}
    {hp1 : Periodic (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) P1}
    {hp2 : Periodic (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) P2}
    {η1 ξ1 σ1 rhoMax1 η2 ξ2 σ2 rhoMax2 : ℝ}
    (D1 : PositiveExitActualFermiData G e.target
      (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 η1 ξ1 σ1 rhoMax1)
    (D2 : PositiveExitActualFermiData G e.target
      (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 η2 ξ2 σ2 rhoMax2)
    (ε1 ε2 δ1 δ2 : ℝ) (p1 p2 : ℝ → Coord)
    (hgraph1 : let ζ1 := positiveExitRawLeaf d hb hinside vin ∘ S1.symm
      let v1 := exitPositiveGraphProfile P1 (fermiSupportSeamSlope (normalLoopCurvature ζ1)
        (fermiPerturbedSupport ε1 (normalLoopCurvature ζ1) (positiveExitFermiHeight G ζ1)
          (fermiExitCutoff D1.rho D1.rho_pos)))
      ∀ s, p1 s = positiveExitFermiSource ζ1 (exitGraphCurve v1 δ1 s))
    (hgraph2 : let ζ2 := positiveExitRawLeaf d hb hinside vout ∘ S2.symm
      let v2 := exitPositiveGraphProfile P2 (fermiSupportSeamSlope (normalLoopCurvature ζ2)
        (fermiPerturbedSupport ε2 (normalLoopCurvature ζ2) (positiveExitFermiHeight G ζ2)
          (fermiExitCutoff D2.rho D2.rho_pos)))
      ∀ s, p2 s = positiveExitFermiSource ζ2 (exitGraphCurve v2 δ2 s))
    (hstrip1 : let ζ1 := positiveExitRawLeaf d hb hinside vin ∘ S1.symm
      let v1 := exitPositiveGraphProfile P1 (fermiSupportSeamSlope (normalLoopCurvature ζ1)
        (fermiPerturbedSupport ε1 (normalLoopCurvature ζ1) (positiveExitFermiHeight G ζ1)
          (fermiExitCutoff D1.rho D1.rho_pos)))
      ∀ s ∈ Icc (0 : ℝ) P1, |δ1*v1 s| < D1.rho)
    (hstrip2 : let ζ2 := positiveExitRawLeaf d hb hinside vout ∘ S2.symm
      let v2 := exitPositiveGraphProfile P2 (fermiSupportSeamSlope (normalLoopCurvature ζ2)
        (fermiPerturbedSupport ε2 (normalLoopCurvature ζ2) (positiveExitFermiHeight G ζ2)
          (fermiExitCutoff D2.rho D2.rho_pos)))
      ∀ s ∈ Icc (0 : ℝ) P2, |δ2*v2 s| < D2.rho) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ t, H 0 t = positiveExitComplexTrace p1 (P1*(t:ℝ))) ∧
      (∀ t, H 1 t = positiveExitComplexTrace p2 (P2*(t:ℝ))) ∧
      (∀ a, H a 1 = H a 0) ∧
      ∀ a t, H a t ∈ angularDescentComplex '' e.target := by
  obtain ⟨hv1, hv1P⟩ := positiveExit_actual_fermi_profile_smooth_periodic D1 ε1
  obtain ⟨hv2, hv2P⟩ := positiveExit_actual_fermi_profile_smooth_periodic D2 ε2
  obtain ⟨H1, hH10, hH11, hH1c, hH1U⟩ :=
    selectedHomotopyPair_graph_to_flow d hb hinside e heS heF hn vin S1 hS1 hP1
      D1 hv1 hv1P δ1 p1 hgraph1 hstrip1
  obtain ⟨H2, hH20, hH21, hH2c, hH2U⟩ :=
    selectedHomotopyPair_graph_to_flow d hb hinside e heS heF hn vout S2 hS2 hP2
      D2 hv2 hv2P δ2 p2 hgraph2 hstrip2
  obtain ⟨F, hF0, hF1, hFc, hFU⟩ :=
    positiveExit_actual_complete_flow_source_homotopy d hb hinside e heS vin vout horder
  have hj1 : H1 1 = F 0 := by
    apply ContinuousMap.ext
    intro t
    exact (hH11 t).trans (hF0 t).symm
  obtain ⟨A, hA0, hA1, hAc, hAU⟩ :=
    positiveExit_actual_loop_homotopy_trans H1 F hj1 hH1c hFc hH1U hFU
  obtain ⟨R2, hR20, hR21, hR2c, hR2U⟩ :=
    positiveExit_actual_loop_homotopy_symm H2 hH2c hH2U
  have hj2 : A 1 = R2 0 := by
    apply ContinuousMap.ext
    intro t
    calc
      A 1 t = F 1 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hA1
      _ = H2 1 t := (hF1 t).trans (hH21 t).symm
      _ = R2 0 t := (congrArg (fun c : C(unitInterval, ℂ) => c t) hR20).symm
  obtain ⟨H, hH0, hH1, hHc, hHU⟩ :=
    positiveExit_actual_loop_homotopy_trans A R2 hj2 hAc hR2c hAU hR2U
  refine ⟨H, ?_, ?_, hHc, hHU⟩
  · intro t
    calc
      H 0 t = A 0 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hH0
      _ = H1 0 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hA0
      _ = positiveExitComplexTrace p1 (P1*(t:ℝ)) := hH10 t
  · intro t
    calc
      H 1 t = R2 1 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hH1
      _ = H2 0 t := congrArg (fun c : C(unitInterval, ℂ) => c t) hR21
      _ = positiveExitComplexTrace p2 (P2*(t:ℝ)) := hH20 t

end
end TightVer401
