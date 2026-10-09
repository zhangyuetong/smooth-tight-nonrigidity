import TightVer401.PositiveExitConstructionSelectedSourceGeometrySelectedAvoidance
import TightVer401.PositiveExitConstructionSelectedHomotopyPair

/-! Actual protected-point-avoiding homotopy from the SAME selected graph
through its arclength seam and clock interpolation to its normalized raw leaf.
The label tube supplies Fermi avoidance and the exact raw first integral
supplies clock avoidance. No final protected placement or nesting is assumed. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- One actual graph-to-raw family avoiding EVERY protected point, with the
SAME physical period, selected leaf, clock, graph profile and native inverse. -/
theorem positiveExitSelected_graph_to_raw_avoids_protected
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
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvP : Periodic v P) (δ : ℝ)
    (hstrip : ∀ s ∈ Icc (0 : ℝ) P, |δ*v s| < D.rho)
    {C : Set Coord} {ε ρ : ℝ} (hε : 0 < ε)
    (htube : ∀ r x : ℝ, |x| ≤ ρ →
      |positiveExitCartesianLabel d hb e
          (positiveExitFermiSource (positiveExitRawLeaf d hb hinside z ∘ S.symm) ![r, x]) -
        (1 / (ruledRho d.τ 0 * (z : ℝ)) - ruledOmega d.k d.τ 0)| < ε)
    (hgap : ∀ q ∈ C, ε ≤ |positiveExitCartesianLabel d hb e q -
      (1 / (ruledRho d.τ 0 * (z : ℝ)) - ruledOmega d.k d.τ 0)|)
    (hbudget : ∀ r ∈ Icc (0 : ℝ) P, |δ*v r| ≤ ρ) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ t, H 0 t = angularDescentComplex (positiveExitFermiSource
        (positiveExitRawLeaf d hb hinside z ∘ S.symm) (exitGraphCurve v δ (P*(t:ℝ))))) ∧
      (∀ t, H 1 t = angularDescentComplex
        (gnomonicInverse (positiveExitRawLeaf d hb hinside z (T*(t:ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      (∀ a t, H a t ∈ angularDescentComplex '' e.target) ∧
      ∀ a t q, q ∈ C → H a t ≠ angularDescentComplex q := by
  obtain ⟨F, hF0, hF1, hFc, hFU, hFAvoid⟩ :=
    positiveExitSelected_graph_to_seam_avoids_protected D hv hvP δ hstrip htube hgap hbudget
  have hS0 : S 0 = 0 := by rw [hS]; simp [rawPrimitive]
  have hST : S T = P := by rw [hS, hP]
  have hψ0 : S.symm 0 = 0 :=
    (congrArg S.symm hS0.symm).trans (S.symm_apply_apply 0)
  have hψP : S.symm P = T :=
    (congrArg S.symm hST.symm).trans (S.symm_apply_apply T)
  have hraw (s : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside z s) =
      e (positiveExitLeaf d hb hinside z (periodProjection T s)) :=
    positiveExitGaussLeaf_cartesian_source d hb e hinside heF z (periodProjection T s)
  have hsource (s : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside z s) ∈ e.target := by
    rw [hraw]
    exact e.mapsTo (by rw [heS]; exact mem_univ _)
  have hlabel (s : ℝ) :
      positiveExitCartesianLabel d hb e (gnomonicInverse (positiveExitRawLeaf d hb hinside z s)) =
        1 / (ruledRho d.τ 0 * (z : ℝ)) - ruledOmega d.k d.τ 0 := by
    rw [hraw]
    change positiveExitLevel d hb
      (e.symm (e (positiveExitLeaf d hb hinside z (periodProjection T s)))) = _
    rw [e.left_inv (by rw [heS]; exact mem_univ _)]
    exact positiveExitLevel_identityFlowBandInclusion d hb hinside (periodProjection T s, z)
  obtain ⟨K, _hKformula, hK0, hK1, hKc, hKU, hKAvoid⟩ :=
    positiveExitSelected_seam_clock_avoids_protected
      (positiveExitRawLeaf_contDiff d hb hinside z)
      (positiveExitRawLeaf_periodic d hb hinside z)
      (fun s => positiveExitGaussLeaf_north d hb hinside z hn (periodProjection T s))
      hsource S.symm.continuous hψ0 hψP hε hlabel hgap
  have hjoin : F 1 = K 0 := by
    apply ContinuousMap.ext
    intro t
    exact (hF1 t).trans (by simpa only [Function.comp_apply] using (hK0 t).symm)
  let Safe : Set ℂ := (angularDescentComplex '' e.target) \ (angularDescentComplex '' C)
  have hFSafe : ∀ a t, F a t ∈ Safe := by
    intro a t
    refine ⟨hFU a t, ?_⟩
    rintro ⟨q, hq, heq⟩
    exact hFAvoid a t q hq heq.symm
  have hKSafe : ∀ a t, K a t ∈ Safe := by
    intro a t
    refine ⟨hKU a t, ?_⟩
    rintro ⟨q, hq, heq⟩
    exact hKAvoid a t q hq heq.symm
  obtain ⟨H, hH0, hH1, hHc, hHSafe⟩ :=
    positiveExit_actual_loop_homotopy_trans F K hjoin hFc hKc hFSafe hKSafe
  refine ⟨H, ?_, ?_, hHc, fun a t => (hHSafe a t).1, ?_⟩
  · intro t
    exact (congrArg (fun f : C(unitInterval, ℂ) => f t) hH0).trans (hF0 t)
  · intro t
    exact (congrArg (fun f : C(unitInterval, ℂ) => f t) hH1).trans (hK1 t)
  · intro a t q hq heq
    exact (hHSafe a t).2 ⟨q, hq, heq.symm⟩

end
end TightVer401
