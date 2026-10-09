import TightVer401.PositiveExitConstructionSelectedSourceGeometrySelectedPlacement
import TightVer401.PositiveExitConstructionSelectedSourceGeometryPhase
import TightVer401.VisibleConnectorWitnessAssemblyTopology

/-! Root assembly for the SAME retained selected graphs. Actual raw geometry,
positive Jordan witnesses, protected homotopies and selected nesting are
constructed here; none is an input grant. Tube facts are ordinary first-integral
estimates for the fixed prefix. Final graph amplitudes use one common budget. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- One budget for both fixed profiles, chosen before retaining final traces. -/
theorem positiveExitSelected_exists_common_graph_budget
    {P1 P2 r1 r2 : ℝ} (hP1 : 0 < P1) (hP2 : 0 < P2)
    (hr1 : 0 < r1) (hr2 : 0 < r2) {v1 v2 : ℝ → ℝ}
    (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hv1P : Periodic v1 P1) (hv2P : Periodic v2 P2) :
    ∃ nu > 0, ∀ a1 a2 : ℝ, |a1| < nu → |a2| < nu →
      (∀ s, |a1 * v1 s| < r1) ∧ (∀ s, |a2 * v2 s| < r2) := by
  obtain ⟨n1, hn1, h1⟩ := positiveExitSelected_exists_graph_amplitude_budget hP1 hr1 hv1 hv1P
  obtain ⟨n2, hn2, h2⟩ := positiveExitSelected_exists_graph_amplitude_budget hP2 hr2 hv2 hv2P
  refine ⟨min n1 n2, lt_min hn1 hn2, ?_⟩
  intro a1 a2 ha1 ha2
  exact ⟨h1 a1 (ha1.trans_le (min_le_left _ _)),
    h2 a2 (ha2.trans_le (min_le_right _ _))⟩

/-- Connect the fixed-prefix real estimates and FINAL actual traces directly
to the pair caller's strict source order and protected support placement.
The two graph periods remain their actual selected clocks. -/
theorem positiveExitSelected_actual_traces_source_geometry
    {T delta w P1 P2 : ℝ} [Fact (0 < T)] [Fact (0 < P1)] [Fact (0 < P2)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) delta, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u s ∈ Ioo 0 w)
    (vin vout : Ioo (0 : ℝ) delta) (horder : (vin : ℝ) < (vout : ℝ))
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s)
    (hmargin : ∀ v : Ioo (0 : ℝ) delta,
      (∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0) ∧
      HasPositiveArgumentTurn
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ) (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (S1 S2 : ℝ ≃ₜ ℝ)
    (hS1 : (S1 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vin))
    (hP1 : P1 = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) T)
    (hS2 : (S2 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vout))
    (hP2 : P2 = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) T)
    {G Ge : Coord → ℝ}
    {hp1 : Periodic (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) P1}
    {hp2 : Periodic (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) P2}
    {eta1 xi1 sig1 rm1 eta2 xi2 sig2 rm2 : ℝ}
    (D1 : PositiveExitActualFermiData G e.target
      (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 eta1 xi1 sig1 rm1)
    (D2 : PositiveExitActualFermiData G e.target
      (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 eta2 xi2 sig2 rm2)
    {v1 v2 : ℝ → ℝ} (hv1 : ContDiff ℝ ∞ v1) (hv2 : ContDiff ℝ ∞ v2)
    (hv1P : Periodic v1 P1) (hv2P : Periodic v2 P2)
    (a1 a2 : ℝ) (t1 : PositiveExitTrace Ge e.target P1) (t2 : PositiveExitTrace Ge e.target P2)
    (hgraph1 : ∀ s, t1.p s = positiveExitFermiSource
      (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) (exitGraphCurve v1 a1 s))
    (hgraph2 : ∀ s, t2.p s = positiveExitFermiSource
      (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) (exitGraphCurve v2 a2 s))
    (hstrip1 : ∀ s ∈ Icc (0 : ℝ) P1, |a1 * v1 s| < D1.rho)
    (hstrip2 : ∀ s ∈ Icc (0 : ℝ) P2, |a2 * v2 s| < D2.rho)
    {C K : Set Coord} (hne : C.Nonempty) (hKC : K ⊆ C)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    {eps r1 r2 : ℝ} (heps : 0 < eps)
    (hlabels : ∀ q ∈ C,
      1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 + eps <
        positiveExitCartesianLabel d hb e q ∧
      positiveExitCartesianLabel d hb e q <
        1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0 - eps)
    (htube1 : ∀ s x : ℝ, |x| ≤ r1 →
      |positiveExitCartesianLabel d hb e (positiveExitFermiSource
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) ![s, x]) -
        (1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0)| < eps)
    (htube2 : ∀ s x : ℝ, |x| ≤ r2 →
      |positiveExitCartesianLabel d hb e (positiveExitFermiSource
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) ![s, x]) -
        (1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0)| < eps)
    (hbudget1 : ∀ s, |a1 * v1 s| ≤ r1) (hbudget2 : ∀ s, |a2 * v2 s| ≤ r2) :
    ∃ HpPlus HpMinus HgPlus HgMinus : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace HpPlus (fun s => positiveExitComplexTrace t2.p (P2*s)) ∧
      DualRadialCompletionPositiveTrace HpMinus (fun s => positiveExitComplexTrace t1.p (P1*s)) ∧
      DualRadialCompletionPositiveTrace HgPlus (fun s => positiveExitComplexTrace t2.gamma (P2*s)) ∧
      DualRadialCompletionPositiveTrace HgMinus (fun s => positiveExitComplexTrace t1.gamma (P1*s)) ∧
      (0 : ℂ) ∈ jordanInterior HpPlus ∧ (0 : ℂ) ∈ jordanInterior HpMinus ∧
      (0 : ℂ) ∈ jordanInterior HgPlus ∧ (0 : ℂ) ∈ jordanInterior HgMinus ∧
      closure (jordanInterior HpMinus) ⊆ jordanInterior HpPlus ∧
      K ⊆ annularCoordJordanInterior HpPlus HpMinus := by
  obtain ⟨Ro, Ri, hro, hri, _, _, _, _, _, hrawImage, _⟩ :=
    positiveExitSelected_exists_raw_source_construction d hb hinside vin vout horder
      hNi hnorth horient hmargin e heF
  have hrawC : C ⊆ annularCoordJordanInterior Ro Ri := by
    rw [← hrawImage]
    apply positiveExit_selectedSourceGeometry_core_in_flowCore d hb hinside e heS vin vout hprotect
    intro q hq
    obtain ⟨hl, hu⟩ := hlabels q hq
    constructor <;> linarith
  have hgap1 : ∀ q ∈ C, eps ≤ |positiveExitCartesianLabel d hb e q -
      (1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0)| := by
    intro q hq
    have h := (hlabels q hq).2
    rw [abs_of_neg (by linarith)]
    linarith
  have hgap2 : ∀ q ∈ C, eps ≤ |positiveExitCartesianLabel d hb e q -
      (1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0)| := by
    intro q hq
    have h := (hlabels q hq).1
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨Inner, hi0, hi1, hic, _, hia⟩ :=
    positiveExitSelected_graph_to_raw_avoids_protected d hb hinside e heS heF hnorth
      vin S1 hS1 hP1 D1 hv1 hv1P a1 hstrip1 heps htube1 hgap1
      (fun s _ => hbudget1 s)
  obtain ⟨Outer, ho0, ho1, hoc, _, hoa⟩ :=
    positiveExitSelected_graph_to_raw_avoids_protected d hb hinside e heS heF hnorth
      vout S2 hS2 hP2 D2 hv2 hv2P a2 hstrip2 heps htube2 hgap2
      (fun s _ => hbudget2 s)
  obtain ⟨Hi, Gi, hpi, hgi, hiOrigin, giOrigin, _, _⟩ :=
    dualRadialCompletionExitApplicationPeriod_positive_traces t1
  obtain ⟨Ho, Go, hpo, hgo, hoOrigin, goOrigin, _, _⟩ :=
    dualRadialCompletionExitApplicationPeriod_positive_traces t2
  have hsep : eps + eps < |(1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) -
      (1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0)| := by
    obtain ⟨q, hq⟩ := hne
    obtain ⟨hl, hu⟩ := hlabels q hq
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hcoords : Disjoint (range t1.p) (range t2.p) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨s, hs⟩ ⟨r, hr⟩
    have h1 := htube1 s (a1 * v1 s) (hbudget1 s)
    have h2 := htube2 r (a2 * v2 r) (hbudget2 r)
    have hg1 : positiveExitFermiSource (positiveExitRawLeaf d hb hinside vin ∘ S1.symm)
      (![s, a1 * v1 s] : Coord) = q := by simpa [exitGraphCurve] using (hgraph1 s).symm.trans hs
    have hg2 : positiveExitFermiSource (positiveExitRawLeaf d hb hinside vout ∘ S2.symm)
      (![r, a2 * v2 r] : Coord) = q := by simpa [exitGraphCurve] using (hgraph2 r).symm.trans hr
    rw [hg1] at h1
    rw [hg2] at h2
    have htri := abs_sub_le
      (1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0)
      (positiveExitCartesianLabel d hb e q)
      (1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0)
    rw [abs_sub_comm _ (positiveExitCartesianLabel d hb e q)] at htri
    exact (not_lt_of_ge htri) ((add_lt_add h1 h2).trans hsep)
  have hdis : Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)) := by
    apply Set.disjoint_left.mpr
    intro z hzo hzi
    rw [← (visibleConnectorWitnessAssemblyTopology_positiveJordan hpo).boundary] at hzo
    rw [← (visibleConnectorWitnessAssemblyTopology_positiveJordan hpi).boundary] at hzi
    obtain ⟨s, _, hs⟩ := hzo
    obtain ⟨r, _, hr⟩ := hzi
    have heq : t1.p (P1*r) = t2.p (P2*s) := by
      have hh : positiveExitComplexPoint (t1.p (P1*r)) = positiveExitComplexPoint (t2.p (P2*s)) :=
        hr.trans hs.symm
      ext i
      fin_cases i
      · exact congrArg Complex.re hh
      · exact congrArg Complex.im hh
    exact Set.disjoint_left.mp hcoords (mem_range_self (P1*r))
      (heq.symm ▸ mem_range_self (P2*s))
  have hi0' : ∀ t, Inner 0 t = positiveExitComplexTrace t1.p (P1*(t:ℝ)) := by
    intro t
    rw [hi0 t]
    change angularDescentComplex _ = positiveExitComplexPoint (t1.p (P1*(t:ℝ)))
    rw [hgraph1]
    apply Complex.ext <;> simp [angularDescentComplex, positiveExitComplexPoint]
  have ho0' : ∀ t, Outer 0 t = positiveExitComplexTrace t2.p (P2*(t:ℝ)) := by
    intro t
    rw [ho0 t]
    change angularDescentComplex _ = positiveExitComplexPoint (t2.p (P2*(t:ℝ)))
    rw [hgraph2]
    apply Complex.ext <;> simp [angularDescentComplex, positiveExitComplexPoint]
  obtain ⟨hselectedC, hnested⟩ := positiveExitSelected_protected_placement_and_nesting
    hro hri (visibleConnectorWitnessAssemblyTopology_positiveJordan hpo)
    (visibleConnectorWitnessAssemblyTopology_positiveJordan hpi) hne hrawC
    Outer Inner ho0' ho1 hi0' hi1 hoc hic hoa hia hdis hoOrigin hiOrigin
  exact ⟨Ho, Hi, Go, Gi, hpo, hpi, hgo, hgi, hoOrigin, hiOrigin, goOrigin, giOrigin,
    hnested, hKC.trans hselectedC⟩

end
end TightVer401

