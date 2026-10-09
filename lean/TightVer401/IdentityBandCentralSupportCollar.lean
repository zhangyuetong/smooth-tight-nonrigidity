import TightVer401.ThinBandRuledNorth
import TightVer401.ThinBandRuledHorizontal
import TightVer401.NormalLoopEmbeddingPeriod

/-! A simultaneous actual two-sided collar for Gauss and horizontal maps.
This is a geometric gate, not an inverse atlas or a support potential.
No preselected bending is declared to survive a reduction in width. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Gauss and horizontal maps on one closed strip, together
with closed- and open-strip horizontal embedding. -/
def IdentityBandTwoSidedCollar {L : ℝ} (d : PeriodicRuledFrame L) (δ : ℝ) : Prop :=
  Set.InjOn d.fullGaussMap (univ ×ˢ Icc (-δ) δ) ∧
    (∀ p ∈ (univ ×ˢ Icc (-δ) δ : Set (AddCircle L × ℝ)),
      0 < d.fullGaussMap p 2) ∧
    Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.fullBandMap)
      (univ ×ˢ Icc (-δ) δ) ∧
    Topology.IsEmbedding
      (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Icc (-δ) δ) =>
        corrugatedAmbientHorizontalCLM (d.fullBandMap p)) ∧
    Topology.IsEmbedding
      (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-δ) δ) =>
        corrugatedAmbientHorizontalCLM (d.fullBandMap p))

/-- Actual central injectivity and northern normals give one simultaneous
collar, bounded by any requested positive old width. Protected bending must
be chosen after this width or accompanied by a proved support containment. -/
theorem identityBand_exists_twoSided_collar {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L)
    (hGauss : Function.Injective d.period_n.lift)
    (hnorth : ∀ r, 0 < d.n r 2)
    (hHorizontal : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift))
    {oldw : ℝ} (holdw : 0 < oldw) :
    ∃ δ > 0, δ ≤ oldw ∧ IdentityBandTwoSidedCollar d δ := by
  obtain ⟨δG, hδG, hGi⟩ := periodicRuledFrame_exists_thin_Gauss_injective d hGauss
  obtain ⟨δN, hδN, hN⟩ := periodicRuledFrame_exists_northern_strip d hnorth
  let F : AddCircle L × ℝ → ℂ := corrugatedAmbientHorizontalCLM ∘ d.fullBandMap
  have hc : Continuous F := corrugatedAmbientHorizontalCLM.continuous.comp
    (periodicRuledFrame_fullBandMap_continuous d)
  have hic : Function.Injective (fun q : AddCircle L => F (q, (0 : ℝ))) := by
    intro q r he
    apply hHorizontal
    simpa only [F, Function.comp_apply, PeriodicRuledFrame.fullBandMap,
      zero_smul, add_zero] using he
  obtain ⟨δH, hδH, hHi, hHe⟩ := exists_thinBand_embedding hc hic
    (periodicRuledFrame_horizontal_locally_injective d (fun r => (hnorth r).ne'))
  let δ : ℝ := min oldw (min δG (min δN δH))
  have hδ : 0 < δ := lt_min holdw (lt_min hδG (lt_min hδN hδH))
  have hGle : δ ≤ δG := (min_le_right oldw _).trans (min_le_left δG _)
  have hNle : δ ≤ δN :=
    ((min_le_right oldw _).trans (min_le_right δG _)).trans (min_le_left δN δH)
  have hHle : δ ≤ δH :=
    ((min_le_right oldw _).trans (min_le_right δG _)).trans (min_le_right δN δH)
  have hsub (b : ℝ) (hb : δ ≤ b) :
      (univ ×ˢ Icc (-δ) δ : Set (AddCircle L × ℝ)) ⊆ univ ×ˢ Icc (-b) b := by
    intro p hp
    exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2.trans hb⟩⟩
  have hFi : Set.InjOn F (univ ×ˢ Icc (-δ) δ) := hHi.mono (hsub δH hHle)
  let K : Set (AddCircle L × ℝ) := univ ×ˢ Icc (-δ) δ
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hiK : Function.Injective (fun p : ↥K => F p) := by
    intro p q he
    exact Subtype.ext (hFi p.property q.property he)
  have hclosed : Topology.IsEmbedding (fun p : ↥K => F p) :=
    ((hc.comp continuous_subtype_val).isClosedEmbedding hiK).isEmbedding
  have hsubOpen : (univ ×ˢ Ioo (-δ) δ : Set (AddCircle L × ℝ)) ⊆
      univ ×ˢ Ioo (-δH) δH := by
    intro p hp
    exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2.trans_le hHle⟩⟩
  have hopen := hHe.comp (Topology.IsEmbedding.inclusion hsubOpen)
  exact ⟨δ, hδ, min_le_left oldw _,
    hGi.mono (hsub δG hGle), fun p hp => hN p (hsub δN hNle hp),
    hFi, hclosed, hopen⟩

/-- A raw fundamental-interval version of the same geometric gate. The
native central hypotheses are derived through the actual periodic lifts. -/
theorem identityBand_exists_twoSided_collar_of_central_injOn
    {L : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    (hGauss : Set.InjOn d.n (Ico 0 L))
    (hnorth : ∀ r, 0 < d.n r 2)
    (hHorizontal : Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.γ) (Ico 0 L))
    {oldw : ℝ} (holdw : 0 < oldw) :
    ∃ δ > 0, δ ≤ oldw ∧ IdentityBandTwoSidedCollar d δ := by
  have hp : Function.Periodic (corrugatedAmbientHorizontalCLM ∘ d.γ) L := by
    intro r
    change corrugatedAmbientHorizontalCLM (d.γ (r + L)) = corrugatedAmbientHorizontalCLM (d.γ r)
    rw [d.period_γ r]
  have hlift : hp.lift = corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift := by
    funext q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [Function.comp_apply, Function.Periodic.lift_coe]
  have hiH : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift) := by
    rw [← hlift]
    exact periodicCurve_lift_injective hp hHorizontal
  exact identityBand_exists_twoSided_collar d
    (periodicCurve_lift_injective d.period_n hGauss) hnorth hiH holdw

end
end TightVer401
