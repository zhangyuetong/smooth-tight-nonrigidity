import TightVer401.PositiveExitConstructionActualPatch
import TightVer401.PositiveExitConstructionEmbedding

/-! Actual compact-support embedding threshold consumed BEFORE the exit
amplitude is chosen. The Fermi data and null geometry belong to the original G;
the baseline Hbase may be G, or the already embedded G plus the first change.
This permits sequential amplitude selection for the same two-exit construction.
No inverse or combined Hessian assertion is inferred without its own proof. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Consume the constructed actual Fermi data of the original G and choose
the SAME weighted exit change below both the caller's bound and the actual
baseline-gradient embedding threshold. The fixed unit change and compact
support strip are proved regular before selecting the perturbation size. -/
theorem positiveExit_actual_embedded_patch_with_bound {P : ℝ} [Fact (0 < P)]
    {G Hbase : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hdetorig : ∀ y ∈ U, (planarHessian G y).det < 0)
    (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0)
    (havoid : ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
      positiveExitFermiSource ζ (![r,t] : Coord) ∉ C)
    (hHbase : ContDiffOn ℝ ∞ Hbase U)
    (hemb : Topology.IsEmbedding (fun y : U => planarGradient Hbase y.val))
    (hdetbase : ∀ y ∈ U, (planarHessian Hbase y).det ≠ 0)
    {ξCaller : ℝ} (hξCaller : 0 < ξCaller) :
    ∃ B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D,
      |B.epsilon| < ξCaller ∧
      Topology.IsEmbedding
        (fun y : U => planarGradient (fun q => Hbase q + B.change q) y.val) := by
  let J := positiveExitActualUnitChange D
  let K := positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube
  have hJ : ContDiff ℝ ∞ J := positiveExitActualUnitChange_contDiff D
  have hK : IsCompact K := positiveExitFermiPatchStrip_compact D.fermi_chart
    D.rho_lt_tube D.fermi_chart_smooth
  have hKU : K ⊆ U := positiveExit_actual_fermi_strip_in_U D
  have hsupport : tsupport J ⊆ K := positiveExitActualUnitChange_tsupport D
  obtain ⟨δEmbed,hδEmbed,hEmbedding⟩ := positiveExit_actual_gradient_embedding_threshold
    hU hHbase hJ hemb hdetbase hK hKU hsupport
  obtain ⟨B,hsmall⟩ := positiveExit_actual_cartesian_patch_with_bound D hG hU hdetorig
    hη hξ hσ havoid (lt_min hξCaller hδEmbed)
  refine ⟨B,hsmall.trans_le (min_le_left _ _),?_⟩
  have hchange : B.change = (fun y => B.epsilon * J y) :=
    positiveExit_actual_cartesian_change_eq_scalar D B
  have hpotential : (fun q => Hbase q + B.change q) =
      (fun q => Hbase q + B.epsilon * J q) := by
    funext q
    change Hbase q + B.change q = Hbase q + B.epsilon * J q
    exact congrArg (fun a : ℝ => Hbase q + a) (congrFun hchange q)
  rw [hpotential]
  exact hEmbedding B.epsilon (hsmall.trans_le (min_le_right _ _))

/-- Construct the selected leaf's collar and protected strip before choosing
the exit amplitude. The actual baseline gradient embedding threshold then
selects the single perturbation. Hbase may be the original G or G plus an
already chosen disjoint change; the leaf, tensor and return belong to G. -/
theorem positiveExit_selected_leaf_actual_embedded_cartesian_patch
    {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ)
    (hNi : Function.Injective (d.bandGaussMap (b := w)))
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ t, ambientCross (d.T t) (d.E t) = d.n t)
    (hτ : ∀ t, d.τ t < 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (G : Coord → ℝ) (hG : ContDiffOn ℝ ∞ G e.target)
    (hrec : ∀ p, planarSupportMap G (e p) = d.bandMap p)
    (hdet : ∀ y ∈ e.target, (planarHessian G y).det < 0)
    (C : Set Coord) (hC : IsCompact C)
    (hdisjoint : ∀ t, gnomonicInverse (positiveExitRawLeaf d hb hinside v t) ∉ C)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    (Hbase : Coord → ℝ) (hHbase : ContDiffOn ℝ ∞ Hbase e.target)
    (hemb : Topology.IsEmbedding (fun y : e.target => planarGradient Hbase y.val))
    (hdetbase : ∀ y ∈ e.target, (planarHessian Hbase y).det ≠ 0)
    {η ξ σ ξCaller : ℝ} (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0)
    (hξCaller : 0 < ξCaller) :
    ∃ S : ℝ ≃ₜ ℝ, ∃ P : ℝ, ∃ hP : 0 < P, ∃ ρMax : ℝ, ∃ hρMax : 0 < ρMax,
      ∃ hp : Function.Periodic (positiveExitRawLeaf d hb hinside v ∘ S.symm) P,
      letI : Fact (0 < P) := ⟨hP⟩
      ∃ D : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside v ∘ S.symm) hp η ξ σ ρMax,
      ∃ B : PositiveExitActualCartesianPatch G e.target C
        (positiveExitRawLeaf d hb hinside v ∘ S.symm) hp η ξ σ ρMax D,
        |B.epsilon| < ξCaller ∧
        Topology.IsEmbedding (fun y : e.target =>
          planarGradient (fun z => Hbase z + B.change z) y.val) ∧
        (∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
          positiveExitFermiSource (positiveExitRawLeaf d hb hinside v ∘ S.symm)
            (![r,t] : Coord) ∉ C) ∧
        IsInfinitesimalBendingOn (planarSupportMap (fun z => G z + B.change z))
          (Y ∘ e.symm) e.target ∧
        (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v) ∧
        P = rawPrimitive (positiveExitLeafSpeed d hb hinside v) T := by
  obtain ⟨S0, P0, hP0, hS0, hLength0, hSsmooth0, hshift0, hp0, hζ0, hiζ0,
    hunit0, hnorth0, hspeed0⟩ := positiveExitLeaf_exists_unitSpeed d hb hinside v hNi hbandNorth
  have hdisjoint0 (r : ℝ) : gnomonicInverse
      ((positiveExitRawLeaf d hb hinside v ∘ S0.symm) r) ∉ C := hdisjoint (S0.symm r)
  obtain ⟨ρMax, hρMax, havoid⟩ := positiveExitFermi_exists_protected_cutoff hP0
    hζ0 hp0 hnorth0 hC.isClosed hdisjoint0
  obtain ⟨S, P, hP, hS, hLength, hSsmooth, hshift, hp, ⟨D⟩⟩ :=
    positiveExit_selected_leaf_actual_fermi d hb hinside v hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet hη hξ hσ hρMax
  have hSS : S = S0 := by
    ext s
    exact congrFun (hS.trans hS0.symm) s
  have hPP : P = P0 := hLength.trans hLength0.symm
  subst S
  letI : Fact (0 < P) := ⟨hP⟩
  have havoidP : ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
      positiveExitFermiSource (positiveExitRawLeaf d hb hinside v ∘ S0.symm) (![r,t] : Coord) ∉ C := by
    intro r hr t ht
    have hr0 : r ∈ Icc (0 : ℝ) P0 := by rw [← hPP]; exact hr
    exact havoid r hr0 t ht
  obtain ⟨B,hsmall,hEmbedding⟩ := positiveExit_actual_embedded_patch_with_bound D hG
    e.open_target hdet hη hξ hσ havoidP hHbase hemb hdetbase hξCaller
  have hBending : IsInfinitesimalBendingOn
      (planarSupportMap (fun z => G z + B.change z)) (Y ∘ e.symm) e.target := by
    refine ⟨hbend.1, ?_⟩
    intro y hy i j
    by_cases hs : e.symm y ∈ tsupport Y
    · have hyC : y ∈ C := hsupport ⟨e.symm y, hs, e.right_inv hy⟩
      have hg := B.protected_germ y hyC
      have hm : planarSupportMap (fun z => G z + B.change z) =ᶠ[𝓝 y] planarSupportMap G := by
        filter_upwards [hg, hg.eventuallyEq_nhds] with z hz hzg
        unfold planarSupportMap
        simp only [coordPartial, hzg.fderiv_eq (𝕜 := ℝ), hz]
      have hd := hm.fderiv_eq (𝕜 := ℝ)
      simpa only [strain, coordPartial, hd] using hbend.2 y hy i j
    · have hi : ContinuousAt e.symm y :=
        (heI.continuousOn y hy).continuousAt (e.open_target.mem_nhds hy)
      have hz : (Y ∘ e.symm) =ᶠ[𝓝 y] (fun _ => 0) := by
        filter_upwards [hi.preimage_mem_nhds ((isClosed_tsupport Y).isOpen_compl.mem_nhds hs)] with z hz
        change Y (e.symm z) = 0
        by_contra hn
        exact hz (subset_tsupport Y hn)
      have hd : fderiv ℝ (Y ∘ e.symm) y = 0 :=
        (hz.fderiv_eq (𝕜 := ℝ)).trans (hasFDerivAt_const (c := (0 : Ambient)) y).fderiv
      simp only [strain, coordPartial, hd, ContinuousLinearMap.zero_apply,
        inner_zero_left, inner_zero_right, add_zero]
  exact ⟨S0,P,hP,ρMax,hρMax,hp,D,B,hsmall,hEmbedding,havoidP,hBending,hS0,hLength⟩

end
end TightVer401
