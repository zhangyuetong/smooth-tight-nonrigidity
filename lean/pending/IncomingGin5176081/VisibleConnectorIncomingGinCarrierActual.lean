import TightVer401.VisibleConnectorIncomingGinCarrier

/-! Exact application of the actual Gin strip threshold to the SAME displaced
inverse and Cartesian source inverse.  The raw carrier and literal closed-band
coverage are ordinary outputs of the Cartesian potential application.  The
negative side's containment and the new fixed carrier are conclusions. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem visibleConnectorIncomingGinCarrier_actual_fixed_carrier
    {L R eta : ℝ} [hL : Fact (0 < L)]
    {Gin : Coord → ℝ} {GinU : Set Coord} {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen GinU) (hGin : ContDiffOn ℝ ∞ Gin GinU)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ GinU)
    (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (haxisTarget : ∀ s, (0, p s) ∈ e.target)
    (hheight0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0) :
    ∃ delta > 0, ∀ rho, |rho| < delta →
      let pc := fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)
      let wc := fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)
      let a := fun s => visibleConnectorDisplacedRealPhase e p (rho, s)
      let b := fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2
      ∀ d : ℝ → ℝ,
      ∀ E : OpenPartialHomeomorph Coord Coord,
      ∀ Vraw : Set Coord,
      Periodic (visibleConnectorRebasedSource pc wc a b) L →
      Periodic (visibleConnectorRebasedRuling wc a d) L →
      Periodic d L → (∀ s, 0 < d s) →
      (E : Coord → Coord) = visibleConnectorCartesianSource L
        (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1) →
      {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source →
      IsOpen Vraw →
      ContDiffOn ℝ ∞ (visibleConnectorIncomingGinGlobalHeight L b d E) Vraw →
      (∀ s u, 0 ≤ u → u ≤ 1 →
        visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
          (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ Vraw) →
      let B := visibleConnectorIncomingGinGlobalHeight L b d E
      let V := visibleConnectorIncomingGinCarrier Vraw GinU B
      IsOpen V ∧ V ⊆ Vraw ∧ ContDiffOn ℝ ∞ B V ∧
        (∀ s u, 0 ≤ u → u ≤ 1 →
          visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
            (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ V) ∧
        V ∩ {y | B y < 0} ⊆ GinU := by
  obtain ⟨delta, hd, hstrip⟩ := visibleConnectorIncomingGinCarrier_actual_inverse_negative_strip
    hR hU hGin hp hw0 hpL hw0L hpU hgamma hmargin hw0same e haxisTarget hheight0
  refine ⟨delta, hd, ?_⟩
  intro rho hρ
  dsimp only
  intro d E Vraw hpcL hwcL hdL hdpos hE hclosed hVraw hB hraw
  let pc := fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)
  let a := fun s => visibleConnectorDisplacedRealPhase e p (rho, s)
  let b := fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2
  let B := visibleConnectorIncomingGinGlobalHeight L b d E
  let V := visibleConnectorIncomingGinCarrier Vraw GinU B
  have hbL : Periodic b L := by
    intro s
    simp only [b, visibleConnectorDisplacedNativeSolution, hpL s]
  have hnegativeStrip (s t : ℝ) (ht : t ∈ Icc (b s) 0) :
      pc (a s) + t • wc (a s) ∈ GinU := by
    simpa only [pc, wc, a, visibleConnectorGinDisplacedPosition,
      visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one]
      using (hstrip rho s t hρ ht).2
  have hcover : ∀ s u, 0 ≤ u → u ≤ 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ V :=
    visibleConnectorIncomingGinCarrier_covers_closed_band hL.out hpcL hwcL hbL hdL hdpos
      E hE hclosed hraw hnegativeStrip
  exact ⟨visibleConnectorIncomingGinCarrier_isOpen hVraw hU hB.continuousOn,
    inter_subset_left, visibleConnectorIncomingGinCarrier_contDiffOn hB,
    hcover, visibleConnectorIncomingGinCarrier_negative_subset Vraw GinU B⟩

end
end TightVer401
