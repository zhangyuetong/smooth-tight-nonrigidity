import TightVer401.PositiveExitConstructionSelectedHomotopy
import TightVer401.PositiveExitConstructionSelectedClock

/-! Literal source homotopies of the actual selected positive graph, its
arclength seam and the SAME complete-flow family. The compact strip and
ordinary clock equations give domain membership for every intermediate
loop. No annular chart, inverse or Jordan nesting is supplied. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Periodicity is derived for the literal perturbed profile of this SAME
constructed actual Fermi height, independently of any homotopy input. -/
theorem positiveExit_actual_fermi_profile_smooth_periodic
    {P : ℝ} [Fact (0 < P)] {G : Coord → ℝ} {U : Set Coord}
    {ζ : ℝ → Ambient} {hp : Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) (ε : ℝ) :
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
      (fermiPerturbedSupport ε (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
        (fermiExitCutoff D.rho D.rho_pos)))
    ContDiff ℝ ∞ v ∧ Periodic v P := by
  dsimp only
  let κ := normalLoopCurvature ζ
  let H := positiveExitFermiHeight G ζ
  let χ := fermiExitCutoff D.rho D.rho_pos
  let Hε := fermiPerturbedSupport ε κ H χ
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth D.zeta_smooth).2
  have hκP : Periodic κ P := (normalLoop_actual_periodic D.zeta_smooth hp).2
  have hχ : ContDiff ℝ ∞ χ := fermiExitCutoff_contDiff D.rho D.rho_pos
  have hχ0 : χ 0=1 := fermiExitCutoff_zero D.rho D.rho_pos
  have hac := fermiSeam_coefficients_smooth hκ D.W_open D.height_smooth D.scale_nonzero D.seam_in_W
  have haP := (fermiSeam_coefficients_periodic hκP D.height_periodic).1
  have hHε : ContDiffOn ℝ ∞ Hε D.W :=
    D.height_smooth.add (fermiSeamPerturbation_contDiff hac.1 hκ hχ ε).contDiffOn
  have hHεP : FermiPeriodic P Hε := by
    intro q
    exact congrArg₂ (·+·) (D.height_periodic q) (fermiSeamPerturbation_periodic haP hκP ε q)
  have hposε (r) : 0 < fermiSeamMixed κ Hε r := by
    have hj := fermiSeamPerturbation_preserves_support_seam hac.1 hκ hχ hχ0
      D.W_open D.height_smooth ε (D.seam_in_W r)
    have heq : fermiSeamMixed κ Hε r = fermiSeamMixed κ H r := hj.2.1
    rw [heq]
    exact D.actual_mixed_positive r
  have hacε := fermiSeam_coefficients_smooth hκ D.W_open hHε D.scale_nonzero D.seam_in_W
  have hacεP := fermiSeam_coefficients_periodic hκP hHεP
  have hb : ContDiff ℝ ∞ (fermiSupportSeamSlope κ Hε) :=
    fermiSeamSlopeCoefficient_contDiff hacε.1 hκ hacε.2 hposε
  have hbP : Periodic (fermiSupportSeamSlope κ Hε) P :=
    fermiSeamSlopeCoefficient_periodic hacε.1 hacεP.1 hκP hacεP.2
  exact ⟨exitPositiveGraphProfile_contDiff hb,
    exitPositiveGraphProfile_periodic (Fact.out : 0 < P) hb hbP⟩

/-- The actual graph is homotopic to its SAME seam within the literal
constructed compact Fermi strip. The height bound is the ordinary bound
returned for this actual graph by the smooth positive-graph producer. -/
theorem positiveExit_actual_fermi_graph_source_homotopy
    {P : ℝ} [Fact (0 < P)] {G : Coord → ℝ} {U : Set Coord}
    {ζ : ℝ → Ambient} {hp : Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hvP : Periodic v P) (δ : ℝ)
    (hstrip : ∀ r ∈ Icc (0 : ℝ) P, |δ * v r| < D.rho) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ a t, H a t = angularDescentComplex (positiveExitFermiSource ζ
        (![P*(t : ℝ), (a : ℝ)*(δ*v (P*(t : ℝ)))] : Coord))) ∧
      (∀ t, H 0 t = angularDescentComplex (gnomonicInverse (ζ (P*(t : ℝ))))) ∧
      (∀ t, H 1 t = angularDescentComplex (positiveExitFermiSource ζ
        (exitGraphCurve v δ (P*(t : ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      ∀ a t, H a t ∈ angularDescentComplex '' U := by
  let q : unitInterval × unitInterval → Coord := fun p =>
    ![P*(p.2 : ℝ), (p.1 : ℝ)*(δ*v (P*(p.2 : ℝ)))]
  have cq0 : Continuous (fun p : unitInterval × unitInterval => P*(p.2 : ℝ)) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  have cq1 : Continuous (fun p : unitInterval × unitInterval =>
      (p.1 : ℝ)*(δ*v (P*(p.2 : ℝ)))) :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.mul (hv.continuous.comp cq0))
  have cq : Continuous q := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : unitInterval × unitInterval => P*(p.2 : ℝ))
      exact cq0
    · change Continuous (fun p : unitInterval × unitInterval => (p.1 : ℝ)*(δ*v (P*(p.2 : ℝ))))
      exact cq1
  have hqW (p : unitInterval × unitInterval) : q p ∈ D.W := by
    have hr : P*(p.2 : ℝ) ∈ Icc (0 : ℝ) P :=
      ⟨mul_nonneg (Fact.out : 0 < P).le p.2.property.1,
        by nlinarith [p.2.property.2, (Fact.out : 0 < P)]⟩
    have ha : |(p.1 : ℝ)*(δ*v (P*(p.2 : ℝ)))| ≤ |δ*v (P*(p.2 : ℝ))| := by
      rw [abs_mul, abs_of_nonneg p.1.property.1]
      exact mul_le_of_le_one_left (abs_nonneg _) p.1.property.2
    exact D.K_in_W (D.complete_change_strip _ hr _ (ha.trans (hstrip _ hr).le))
  let F : unitInterval × unitInterval → ℂ :=
    fun p => angularDescentComplex (positiveExitFermiSource ζ (q p))
  have cF : Continuous F := angularDescentComplex_contDiff.continuous.comp
    ((positiveExitFermiSource_contDiffOn D.zeta_smooth D.fermi_north).continuousOn.comp_continuous
      cq (fun p => hqW p))
  let H : C(unitInterval, C(unitInterval, ℂ)) :=
    ⟨fun a => ⟨fun t => F (a,t), cF.comp (continuous_const.prodMk continuous_id)⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact cF⟩
  refine ⟨H, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro t
    change angularDescentComplex (positiveExitFermiSource ζ
      (![P*(t:ℝ),0*(δ*v (P*(t:ℝ)))] : Coord)) = _
    simp [positiveExitFermiSource,fermiNormalMap]
  · intro t
    change angularDescentComplex (positiveExitFermiSource ζ
      (![P*(t:ℝ),1*(δ*v (P*(t:ℝ)))] : Coord)) = _
    simp only [one_mul,exitGraphCurve]
  · intro a
    have hv0 : v P = v 0 := by simpa only [zero_add] using hvP 0
    change angularDescentComplex (positiveExitFermiSource ζ (![P*1, (a:ℝ)*(δ*v (P*1))] : Coord)) =
      angularDescentComplex (positiveExitFermiSource ζ (![P*0, (a:ℝ)*(δ*v (P*0))] : Coord))
    rw [mul_one, mul_zero, hv0]
    apply congrArg angularDescentComplex
    have heq : (![P,(a:ℝ)*(δ*v 0)] : Coord) =
        (![0,(a:ℝ)*(δ*v 0)] : Coord) + Pi.single 0 P := by
      ext i
      fin_cases i <;> simp
    rw [heq]
    exact positiveExitFermiSource_periodic D.zeta_smooth hp _
  · intro a t
    exact ⟨positiveExitFermiSource ζ (q (a,t)), D.source_in_U (hqW (a,t)), rfl⟩

/-- Endpoint-preserving interpolation from the SAME actual arclength clock
to the physical clock. Every intermediate loop lies on this actual complete
leaf, including both endpoints of the full period. -/
theorem positiveExit_actual_seam_clock_source_homotopy
    {T P : ℝ} {ξ : ℝ → Ambient} (hξ : ContDiff ℝ ∞ ξ) (hξT : Periodic ξ T)
    (hnorth : ∀ s, 0 < ξ s 2) {U : Set Coord}
    (hsource : ∀ s, gnomonicInverse (ξ s) ∈ U)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) (hψP : ψ P = T) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ a t, H a t = angularDescentComplex (gnomonicInverse
        (ξ ((1-(a:ℝ))*ψ (P*(t:ℝ)) + (a:ℝ)*(T*(t:ℝ)))))) ∧
      (∀ t, H 0 t = angularDescentComplex (gnomonicInverse (ξ (ψ (P*(t:ℝ)))))) ∧
      (∀ t, H 1 t = angularDescentComplex (gnomonicInverse (ξ (T*(t:ℝ))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      ∀ a t, H a t ∈ angularDescentComplex '' U := by
  let c : unitInterval × unitInterval → ℝ := fun p =>
    (1-(p.1:ℝ))*ψ (P*(p.2:ℝ)) + (p.1:ℝ)*(T*(p.2:ℝ))
  have ca : Continuous (fun p : unitInterval × unitInterval => (p.1:ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ct : Continuous (fun p : unitInterval × unitInterval => (p.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have cc : Continuous c :=
    ((continuous_const.sub ca).mul (hψ.comp (continuous_const.mul ct))).add
      (ca.mul (continuous_const.mul ct))
  have csource : Continuous (gnomonicInverse ∘ ξ) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (gnomonicInverse_contDiffAt (hnorth s).ne').continuousAt.comp hξ.continuous.continuousAt
  let F : unitInterval × unitInterval → ℂ :=
    fun p => angularDescentComplex (gnomonicInverse (ξ (c p)))
  have cF : Continuous F := angularDescentComplex_contDiff.continuous.comp (csource.comp cc)
  let H : C(unitInterval, C(unitInterval, ℂ)) :=
    ⟨fun a => ⟨fun t => F (a,t), cF.comp (continuous_const.prodMk continuous_id)⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact cF⟩
  refine ⟨H, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro t
    change angularDescentComplex (gnomonicInverse (ξ ((1-0)*ψ (P*(t:ℝ))+0*(T*(t:ℝ))))) = _
    simp
  · intro t
    change angularDescentComplex (gnomonicInverse (ξ ((1-1)*ψ (P*(t:ℝ))+1*(T*(t:ℝ))))) = _
    simp
  · intro a
    have h1 : c (a,1)=T := by
      change (1-(a:ℝ))*ψ (P*1)+(a:ℝ)*(T*1)=T
      rw [mul_one,mul_one,hψP]
      ring
    have h0 : c (a,0)=0 := by
      change (1-(a:ℝ))*ψ (P*0)+(a:ℝ)*(T*0)=0
      rw [mul_zero,mul_zero,hψ0,mul_zero,mul_zero,add_zero]
    have he : ξ T = ξ 0 := by simpa only [zero_add] using hξT 0
    change angularDescentComplex (gnomonicInverse (ξ (c (a,1)))) =
      angularDescentComplex (gnomonicInverse (ξ (c (a,0))))
    rw [h1,h0,he]
  · intro a t
    exact ⟨gnomonicInverse (ξ (c (a,t))), hsource _, rfl⟩

/-- Actual complete-flow interpolation between the selected ordered initial
values, in the SAME original source chart. No positive graph or homotopy
witness is supplied. -/
theorem positiveExit_actual_complete_flow_source_homotopy
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (he : e.source=univ) (vin vout : Ioo (0 : ℝ) δ) (horder : (vin:ℝ)<(vout:ℝ)) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      (∀ t, H 0 t = angularDescentComplex
        (e (positiveExitLeaf d hb hinside vin (periodProjection T (T*(t:ℝ)))))) ∧
      (∀ t, H 1 t = angularDescentComplex
        (e (positiveExitLeaf d hb hinside vout (periodProjection T (T*(t:ℝ)))))) ∧
      (∀ a, H a 1 = H a 0) ∧
      ∀ a t, H a t ∈ angularDescentComplex '' e.target := by
  let z (a : unitInterval) : Ioo (0 : ℝ) δ :=
    ⟨(vin:ℝ)+(a:ℝ)*((vout:ℝ)-(vin:ℝ)), by
      have hlow : (vin:ℝ) ≤ (vin:ℝ)+(a:ℝ)*((vout:ℝ)-(vin:ℝ)) := by
        linarith [mul_nonneg a.property.1 (sub_nonneg.mpr horder.le)]
      have hhigh : (vin:ℝ)+(a:ℝ)*((vout:ℝ)-(vin:ℝ)) ≤ (vout:ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr a.property.2) (sub_nonneg.mpr horder.le)]
      exact ⟨vin.property.1.trans_le hlow, hhigh.trans_lt vout.property.2⟩⟩
  have cz : Continuous z := (continuous_const.add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _
  have cz0 : z 0=vin := by apply Subtype.ext; simp [z]
  have cz1 : z 1=vout := by apply Subtype.ext; simp [z]
  let Q : unitInterval × unitInterval → AddCircle T × Ioo (0 : ℝ) δ := fun p =>
    (periodProjection T (T*(p.2:ℝ)),z p.1)
  have cQ : Continuous Q :=
    ((periodProjection_contMDiff T).continuous.comp
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).prodMk
      (cz.comp continuous_fst)
  have cflow : Continuous (identityFlowBandInclusion d hb 0 hinside) :=
    (identityFlowBandInclusion_contMDiff d hb 0
      (fun u hu t => positiveExit_trajectory_denominator_ne_zero d hinside hu t) hinside).continuous
  have ce : Continuous e := continuousOn_univ.mp (he ▸ e.continuousOn)
  let F : unitInterval × unitInterval → ℂ := fun p =>
    angularDescentComplex (e (identityFlowBandInclusion d hb 0 hinside (Q p)))
  have cF : Continuous F := angularDescentComplex_contDiff.continuous.comp (ce.comp (cflow.comp cQ))
  let H : C(unitInterval, C(unitInterval, ℂ)) :=
    ⟨fun a => ⟨fun t => F (a,t), cF.comp (continuous_const.prodMk continuous_id)⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact cF⟩
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro t
    change angularDescentComplex (e (identityFlowBandInclusion d hb 0 hinside
      (periodProjection T (T*(t:ℝ)),z 0))) = _
    rw [cz0]
    rfl
  · intro t
    change angularDescentComplex (e (identityFlowBandInclusion d hb 0 hinside
      (periodProjection T (T*(t:ℝ)),z 1))) = _
    rw [cz1]
    rfl
  · intro a
    have hp : periodProjection T T=periodProjection T 0 := by
      change (T : AddCircle T) = ((0 : ℝ) : AddCircle T)
      simpa only [zero_add] using (AddCircle.coe_add_period (p := T) (0:ℝ))
    change angularDescentComplex (e (identityFlowBandInclusion d hb 0 hinside
      (periodProjection T (T*1),z a))) =
      angularDescentComplex (e (identityFlowBandInclusion d hb 0 hinside
        (periodProjection T (T*0),z a)))
    rw [mul_one,mul_zero,hp]
  · intro a t
    refine ⟨e (identityFlowBandInclusion d hb 0 hinside (Q (a,t))), ?_, rfl⟩
    apply e.mapsTo
    rw [he]
    exact mem_univ _

end
end TightVer401
