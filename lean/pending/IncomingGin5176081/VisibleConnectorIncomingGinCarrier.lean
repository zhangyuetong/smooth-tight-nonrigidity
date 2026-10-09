import TightVer401.VisibleConnectorIncomingGinCarrierAnalytic
import TightVer401.VisibleConnectorIncomingGinGlobalSide

/-! The actual incoming-domain threshold and a fixed carrier for the SAME
closed rebased band.  The threshold uses the height of the already constructed
native inverse.  The Gin ruling is used only on the constructed Omega_vis.
There is no inverse, side classification, full scalar germ, smoothing, or
annulus-order construction in the premises or conclusions. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual inverse height is continuous on its actual target preimage,
without extending the local inverse or the Gin ruling. -/
theorem visibleConnectorIncomingGinCarrier_native_height_continuous {L : ℝ}
    {p : ℝ → Coord} (hp : Continuous p)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord)) :
    IsOpen (visibleConnectorDisplacedNativeSolutionDomain e p) ∧
      ContinuousOn (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
        (visibleConnectorDisplacedNativeSolutionDomain e p) := by
  have hj : Continuous (fun z : ℝ × ℝ => (z.1, p z.2)) :=
    continuous_fst.prodMk (hp.comp continuous_snd)
  refine ⟨e.open_target.preimage hj, ?_⟩
  exact (e.continuousOn_symm.comp hj.continuousOn (fun _ hz => hz)).snd.snd

/-- A single actual small-displacement threshold contains the full negative
height strip at the SAME real phase selected by the actual inverse.  The
central inverse-height identity and central target membership are ordinary
outputs of the displaced-seam constructor; they grant no side or germ. -/
theorem visibleConnectorIncomingGinCarrier_actual_inverse_negative_strip
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
    ∃ delta > 0, ∀ rho s t, |rho| < delta →
      t ∈ Icc ((visibleConnectorDisplacedNativeSolution e p (rho, s)).2) 0 →
      (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) ∈
        visibleConnectorGinDisplacedVisibilityDomain Gin GinU R p w0 ∧
      visibleConnectorDisplacedPhi p w0 (visibleConnectorGinDisplacedRuling Gin R eta p w0)
        rho (![visibleConnectorDisplacedRealPhase e p (rho, s), t] : Coord) ∈ GinU := by
  obtain ⟨_, _, _, hOmega, _, haxis, hw, _, _, hwL, hOmegaL, _, _⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  obtain ⟨hD, hb⟩ := visibleConnectorIncomingGinCarrier_native_height_continuous hp.continuous e
  have hbaxis (s : ℝ) : (0, s) ∈ visibleConnectorDisplacedNativeSolutionDomain e p := haxisTarget s
  have hbL (rho : ℝ) : Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L := by
    intro s
    simp only [visibleConnectorDisplacedNativeSolution, hpL s]
  obtain ⟨delta, hd, hstrip⟩ := visibleConnectorIncomingGinCarrier_exists_negative_strip hL.out
    hp.continuous hw0.continuous hpL hw0L hwL hOmega hw.continuousOn haxis hOmegaL
    hU hpU hD hb hbaxis hheight0 hbL
  refine ⟨delta, hd, ?_⟩
  intro rho s t hρ ht
  simpa only [visibleConnectorDisplacedPhi, Matrix.cons_val_zero, Matrix.cons_val_one]
    using hstrip rho s (visibleConnectorDisplacedRealPhase e p (rho, s)) t hρ ht

/-- A literal negative point of the rebased band lies in the closed incoming
height strip.  This statement keeps the phase and old ruling unchanged. -/
theorem visibleConnectorIncomingGinCarrier_rebased_negative
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ} {GinU : Set Coord}
    (hd : ∀ s, 0 < d s)
    (hstrip : ∀ s t, t ∈ Icc (b s) 0 → pc (a s) + t • wc (a s) ∈ GinU)
    (s u : ℝ) (hu : 0 ≤ u) (hnegative : b s + u * d s ≤ 0) :
    visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
      (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ GinU := by
  rw [visibleConnector_rebase_source]
  apply hstrip s (b s + u * d s)
  exact ⟨le_add_of_nonneg_right (mul_nonneg hu (hd s).le), hnegative⟩

/-- The fixed carrier retains both sides of the whole closed band while
requiring Gin only on the actual negative-height side. -/
def visibleConnectorIncomingGinCarrier (Vraw GinU : Set Coord) (B : Coord → ℝ) : Set Coord :=
  Vraw ∩ (GinU ∪ {y | 0 < B y})

theorem visibleConnectorIncomingGinCarrier_isOpen {Vraw GinU : Set Coord} {B : Coord → ℝ}
    (hV : IsOpen Vraw) (hU : IsOpen GinU) (hB : ContinuousOn B Vraw) :
    IsOpen (visibleConnectorIncomingGinCarrier Vraw GinU B) := by
  change IsOpen (Vraw ∩ (GinU ∪ B ⁻¹' Ioi 0))
  rw [inter_union_distrib_left]
  exact (hV.inter hU).union (hB.isOpen_inter_preimage hV isOpen_Ioi)

theorem visibleConnectorIncomingGinCarrier_negative_subset (Vraw GinU : Set Coord)
    (B : Coord → ℝ) :
    visibleConnectorIncomingGinCarrier Vraw GinU B ∩ {y | B y < 0} ⊆ GinU := by
  intro y hy
  rcases hy.1.2 with hGin | hpos
  · exact hGin
  · exact False.elim (lt_asymm hpos hy.2)

theorem visibleConnectorIncomingGinCarrier_contDiffOn {Vraw GinU : Set Coord} {B : Coord → ℝ}
    (hB : ContDiffOn ℝ ∞ B Vraw) :
    ContDiffOn ℝ ∞ B (visibleConnectorIncomingGinCarrier Vraw GinU B) :=
  hB.mono inter_subset_left

/-- Whole-band coverage uses the literal pullback of the SAME inverse height,
not a granted carrier or a side-classification package. -/
theorem visibleConnectorIncomingGinCarrier_covers_closed_band {L : ℝ} (hL : 0 < L)
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ} {Vraw GinU : Set Coord}
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hd : ∀ s, 0 < d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (hraw : ∀ s u, 0 ≤ u → u ≤ 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) ![s, u] ∈ Vraw)
    (hstrip : ∀ s t, t ∈ Icc (b s) 0 → pc (a s) + t • wc (a s) ∈ GinU) :
    ∀ s u, 0 ≤ u → u ≤ 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) ![s, u] ∈
          visibleConnectorIncomingGinCarrier Vraw GinU
            (visibleConnectorIncomingGinGlobalHeight L b d E) := by
  intro s u hu0 hu1
  refine ⟨hraw s u hu0 hu1, ?_⟩
  have hheight := (visibleConnectorIncomingGinGlobalHeight_closed_band hL hpL hwL hbL hdL
    E hE hclosed s u hu0 hu1).2
  rcases le_or_gt (b s + u * d s) 0 with hnegative | hpositive
  · exact Or.inl (visibleConnectorIncomingGinCarrier_rebased_negative hd hstrip s u hu0 hnegative)
  · exact Or.inr (hheight.symm ▸ hpositive)

end
end TightVer401
