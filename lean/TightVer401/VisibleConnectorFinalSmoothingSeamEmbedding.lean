import TightVer401.VisibleConnectorFinalSmoothingHeightDerivatives
import TightVer401.VisibleConnectorSourceInverseNativeChartsClosed

/-! The displaced zero seam is embedded by the SAME Cartesian raw source
inverse on the full closed band. It is NOT identified with the original
negative-height incoming boundary. No seam embedding is an input. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Matrix

private theorem finalSmoothingEmbedding_clock {L : ℝ} (hL : 0 < L) (s : ℝ) :
    visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
  unfold visibleConnectorPhysicalParameter
  field_simp [hL.ne', Real.two_pi_pos.ne']

/-- Literal SAME descended source on the entire physical parameter band. -/
theorem visibleConnectorFinalSmoothing_source_parameter
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord}
    (hp : Periodic p L) (hw : Periodic w L)
    (s u : ℝ) (hu : 0 < 1 + u) :
    visibleConnectorCartesianSource L p w (fun _ => 1)
      (saddlePolarChart ![1 + u, 2 * Real.pi * s / L]) =
        visibleConnectorSource p w ![s, u] := by
  rw [visibleConnectorCartesianSource_polar hp hw (fun _ => rfl)
    (show 0 < (![1 + u, 2 * Real.pi * s / L] : Coord) 0 from hu)]
  simp [visibleConnectorPolarSource, visibleConnectorSource, finalSmoothingEmbedding_clock hL]

/-- Global seam embedding comes from closed-source injectivity of the SAME E.
The zero graph is strictly between the original negative lower graph and the
positive terminal graph. -/
theorem visibleConnectorFinalSmoothing_seam_injective
    {L : ℝ} [hL : Fact (0 < L)] {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hw : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hc : Periodic (pc ∘ a) L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source) :
    Injective hc.lift := by
  have hu (s : ℝ) : -b s / d s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨(div_pos (neg_pos.mpr (hb s)) (hd s)).le, ?_⟩
    exact ((div_lt_one (hd s)).mpr (by linarith [ht s])).le
  let liftPoint (s : ℝ) : AddCircle L × Icc (0 : ℝ) 1 :=
    (periodProjection L s, ⟨-b s / d s, hu s⟩)
  let chart := visibleConnectorSourceInverse_native_round_closure L
  have hSource (s : ℝ) : E (chart (liftPoint s)) = pc (a s) := by
    rw [visibleConnectorSourceInverse_native_round_closure_apply,
      visibleConnectorSourceInverse_native_round_representative, hE,
      visibleConnectorFinalSmoothing_source_parameter hL.out hp hw s (-b s / d s)
        (by linarith [(hu s).1])]
    rw [visibleConnector_rebase_source]
    have hz : b s + (-b s / d s) * d s = 0 := by
      field_simp [(hd s).ne']
      ring
    simp [visibleConnectorSource, hz]
  intro q r heq
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective r
  have he : pc (a s) = pc (a t) := by
    simpa only [Periodic.lift_coe, Function.comp_apply] using heq
  have hPhysical : (chart (liftPoint s) : Coord) = chart (liftPoint t) :=
    E.injOn (hclosed (chart (liftPoint s)).property)
      (hclosed (chart (liftPoint t)).property) ((hSource s).trans (he.trans (hSource t).symm))
  have hNative : liftPoint s = liftPoint t := chart.injective (Subtype.ext hPhysical)
  exact congrArg Prod.fst hNative

/-- The ENTIRE Cartesian target's zero-height locus is exactly the displaced
seam. No local normal tube or granted only-zero-height condition is used. -/
theorem visibleConnectorFinalSmoothing_height_zero_set
    {L : ℝ} (hL : 0 < L) {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hw : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source) :
    {y | y ∈ E.target ∧ visibleConnectorFinalSmoothingHeight L b d E y = 0} =
      range (pc ∘ a) := by
  apply Subset.antisymm
  · intro y hy
    exact visibleConnectorFinalSmoothingHeight_zero_range E hE hy.1 hy.2
  · rintro y ⟨s, rfl⟩
    have hf := visibleConnectorFinalSmoothingHeight_rebased_band hL
      hp hw hbL hdL hb hd ht E hE hclosed s
    exact ⟨hf.2.2.2.2.1, hf.2.2.2.2.2.1⟩
/-- Actual regular embedded complex seam for the relative-smoothing consumer.
Only ordinary ruling coefficients and the SAME raw inverse are supplied. -/
theorem visibleConnectorFinalSmoothing_seam_geometry
    {L : ℝ} [hL : Fact (0 < L)] {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hpSmooth : ContDiff ℝ ∞ pc) (hwSmooth : ContDiff ℝ ∞ wc)
    (ha : ContDiff ℝ ∞ a)
    (hp : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hw : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hc : Periodic (pc ∘ a) L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (hphase : ∀ s, 0 < deriv a s) (hA : ∀ s, 0 < visibleConnectorA pc wc (a s))
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source) :
    let gamma := fun s => seamComplexCoord.symm ((pc ∘ a) s)
    ContDiff ℝ ∞ gamma ∧ (∀ s, deriv gamma s ≠ 0) ∧
      ∃ hperiod : Periodic gamma L, Injective hperiod.lift := by
  let gamma := fun s => seamComplexCoord.symm ((pc ∘ a) s)
  have hSmooth : ContDiff ℝ ∞ (pc ∘ a) := hpSmooth.comp ha
  have hDeriv (s : ℝ) : deriv gamma s = seamComplexCoord.symm (deriv (pc ∘ a) s) :=
    (seamComplexCoord.symm.hasFDerivAt.comp_hasDerivAt s
      (hSmooth.differentiable (by simp) s).hasDerivAt).deriv
  have hperiod : Periodic gamma L := by
    intro s
    change seamComplexCoord.symm ((pc ∘ a) (s + L)) = seamComplexCoord.symm ((pc ∘ a) s)
    rw [hc s]
  refine ⟨seamComplexCoord.symm.contDiff.comp hSmooth, ?_, hperiod, ?_⟩
  · intro s hz
    have hv : deriv (pc ∘ a) s = 0 := seamComplexCoord.symm.injective (by
      rw [← hDeriv s, hz]
      simp)
    have hdet := visibleConnectorFinalSmoothingHeight_seam_determinant
      hpSmooth hwSmooth ha hphase hA s
    rw [hv] at hdet
    simpa [visibleConnectorDet] using hdet
  · have hi := visibleConnectorFinalSmoothing_seam_injective hp hw hc hb hd ht E hE hclosed
    intro q r he
    apply hi
    apply seamComplexCoord.symm.injective
    have hLift (q : AddCircle L) : hperiod.lift q = seamComplexCoord.symm (hc.lift q) := by
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
      simp only [Periodic.lift_coe]
      rfl
    rw [← hLift q, ← hLift r]
    exact he

end
end TightVer401


