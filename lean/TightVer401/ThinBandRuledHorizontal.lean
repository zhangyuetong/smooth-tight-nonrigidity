import TightVer401.ThinBandRuledEmbedding
import TightVer401.CorrugatedSeedFrameHorizontal

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem corrugatedAmbientHorizontal_plane_zero {v n : Ambient}
    (hv : corrugatedAmbientHorizontalCLM v = 0)
    (horth : inner ℝ v n = 0) (hn : n 2 ≠ 0) : v = 0 := by
  have hh : corrugatedAmbientHorizontal v = 0 :=
    (corrugatedAmbientHorizontalCLM_apply v).symm.trans hv
  have h0 : v 0 = 0 := congrArg Complex.re hh
  have h1 : v 1 = 0 := congrArg Complex.im hh
  have h2 : v 2 = 0 := by
    have he : v 2 * n 2 = 0 := by
      simpa [PiLp.inner_apply, Fin.sum_univ_succ, h0, h1, mul_comm] using horth
    exact (mul_eq_zero.mp he).resolve_right hn
  ext i
  fin_cases i <;> assumption

theorem periodicRuledFrame_horizontal_central_differential_injective
    {L : ℝ} (d : PeriodicRuledFrame L) (r : ℝ) (hn : d.n r 2 ≠ 0) :
    Function.Injective (fderiv ℝ (corrugatedAmbientHorizontalCLM ∘ ruledMap d.γ d.E)
      (![r, 0] : Coord)) := by
  let p : Coord := ![r, 0]
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hc := corrugatedAmbientHorizontalCLM.hasFDerivAt.comp p
    (hX.differentiable (by simp) p).hasFDerivAt
  have hd := ruled_differential_injective (d.deriv_γ (p 0)) (d.deriv_E (p 0))
    (d.orthonormal r) (d.torsion_ne_zero r)
  intro v w he
  change fderiv ℝ (corrugatedAmbientHorizontalCLM ∘ ruledMap d.γ d.E) p v =
    fderiv ℝ (corrugatedAmbientHorizontalCLM ∘ ruledMap d.γ d.E) p w at he
  rw [hc.fderiv] at he
  change corrugatedAmbientHorizontalCLM (fderiv ℝ (ruledMap d.γ d.E) p v) =
    corrugatedAmbientHorizontalCLM (fderiv ℝ (ruledMap d.γ d.E) p w) at he
  have hz : corrugatedAmbientHorizontalCLM (fderiv ℝ (ruledMap d.γ d.E) p (v - w)) = 0 := by
    rw [map_sub, map_sub, he, sub_self]
  have horth : inner ℝ (fderiv ℝ (ruledMap d.γ d.E) p (v - w)) (d.n r) = 0 := by
    have ho := (ruled_isUnitNormal (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal r) (d.torsion_ne_zero r)).2 (v - w)
    simpa only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ruledNormal, ruledEnergy, mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, one_pow, Real.sqrt_one, zero_div, neg_zero, zero_smul,
      one_div, inv_one, one_smul, zero_add] using ho
  have hzero := corrugatedAmbientHorizontal_plane_zero hz horth hn
  have hdf : fderiv ℝ (ruledMap d.γ d.E) p v = fderiv ℝ (ruledMap d.γ d.E) p w := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  exact hd hdf

theorem periodicRuledFrame_horizontal_locally_injective {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hn : ∀ r, d.n r 2 ≠ 0) (q : AddCircle L) :
    ∃ U ∈ 𝓝 (q, (0 : ℝ)),
      Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.fullBandMap) U := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ U ∈ 𝓝 (periodProjection L r, (0 : ℝ)),
    Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.fullBandMap) U
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hp := corrugatedAmbientHorizontalCLM.contDiff.comp hX
  have hl := exists_local_injOn_of_injective_strictFDeriv
    (hp.hasStrictFDerivAt (x := (![r, 0] : Coord)) (by simp))
    (periodicRuledFrame_horizontal_central_differential_injective d r (hn r))
  have ht := local_injOn_transport_chart (g := corrugatedAmbientHorizontalCLM ∘ d.fullBandMap)
    (ruledCircleChart_center_source L r)
    (fun p _ => congrArg corrugatedAmbientHorizontalCLM (ruledCircleChart_fullBandMap d r p)) hl
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using ht

theorem periodicRuledFrame_exists_thin_horizontal_embedding {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hn : ∀ r, d.n r 2 ≠ 0)
    (hi : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift)) :
    ∃ δ > 0, Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := δ)) := by
  let F : AddCircle L × ℝ → ℂ := fun p => corrugatedAmbientHorizontalCLM (d.fullBandMap p)
  have hc : Continuous F := corrugatedAmbientHorizontalCLM.continuous.comp
    (periodicRuledFrame_fullBandMap_continuous d)
  have hic : Function.Injective (fun q : AddCircle L => F (q, (0 : ℝ))) := by
    intro q r he
    apply hi
    simpa only [F, Function.comp_apply, PeriodicRuledFrame.fullBandMap, zero_smul, add_zero] using he
  obtain ⟨δ, hδ, _, hemb⟩ := exists_thinBand_embedding (F := F) hc hic
    (periodicRuledFrame_horizontal_locally_injective d hn)
  let S : Set (AddCircle L × ℝ) := univ ×ˢ Ioo (-δ) δ
  let ι : AddCircle L × Ioo (0 : ℝ) δ → AddCircle L × ℝ := fun p => (p.1, p.2)
  have hι : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have hmem (p : AddCircle L × Ioo (0 : ℝ) δ) : ι p ∈ S :=
    ⟨mem_univ _, ⟨by linarith [p.2.property.1], p.2.property.2⟩⟩
  have hcι : Topology.IsEmbedding (fun p : AddCircle L × Ioo (0 : ℝ) δ =>
      (⟨ι p, hmem p⟩ : S)) := hι.codRestrict S hmem
  have ht : Topology.IsEmbedding ((fun p : S => F p) ∘
      (fun p : AddCircle L × Ioo (0 : ℝ) δ => (⟨ι p, hmem p⟩ : S))) := hemb.comp hcι
  exact ⟨δ, hδ, ht⟩

end
end TightVer401
