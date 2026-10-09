import TightVer401.AnnularDegreeCount
import TightVer401.AnnularDegreeDisks
import TightVer401.AnnularDegreeJordan
import TightVer401.AnnularDegreeAngularForm
import TightVer401.AnnularDegreeLocalOrientation
import TightVer401.AnnularDegreeGreen

/-!
The signed-preimage formula for an actual smooth map of an actual nested
Jordan annulus. Finite actual fibers, inverse charts, disjoint excision disks,
the closed angular pullback, and the local Jacobian contributions are all
derived here. No degree identity, global injectivity, or target image is an
input. Smoothness near the compact source permits boundary rank degeneration.
-/
namespace TightVer401
noncomputable section
open Set Function Filter Metric MeasureTheory
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual regular complex derivative represented as a linear equivalence. -/
def annularComplexRegularCoordinateEquiv (F : ℂ → ℂ) (x : ℂ)
    (hi : Injective (fderiv ℝ F x)) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ F x)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))

theorem annular_complexJacobian_differential_injective {F : ℂ → ℂ} {x : ℂ}
    (hJ : (fderiv ℝ F x).det ≠ 0) : Injective (fderiv ℝ F x) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hJ (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

theorem annular_complexRegularCoordinateEquiv_hasFDerivAt {F : ℂ → ℂ} {x : ℂ}
    (hd : DifferentiableAt ℝ F x) (hi : Injective (fderiv ℝ F x)) :
    HasFDerivAt F (annularComplexRegularCoordinateEquiv F x hi : ℂ →L[ℝ] ℂ) x := by
  simpa only [annularComplexRegularCoordinateEquiv, ContinuousLinearEquiv.coe_ofBijective]
    using hd.hasFDerivAt

/-- The existing inverse-function proof in actual complex coordinates. -/
theorem annular_complex_exists_smooth_local_inverse {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) {x : ℂ} (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧ e.source ⊆ U ∧ (e : ℂ → ℂ) = F ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hFx := hF.contDiffAt (hU.mem_nhds hx)
  have hi := annular_complexJacobian_differential_injective (hJ x hx)
  have hd := annular_complexRegularCoordinateEquiv_hasFDerivAt
    (hFx.differentiableAt (by simp)) hi
  let e₀ := hFx.toOpenPartialHomeomorph F hd (by simp)
  let e := e₀.restrOpen U hU
  have heF : (e : ℂ → ℂ) = F := rfl
  refine ⟨e, ⟨hFx.mem_toOpenPartialHomeomorph_source hd (by simp), hx⟩,
    (fun z hz => hz.2), heF, ?_⟩
  intro y hy
  have hx' : e.symm y ∈ U := (e.map_target hy).2
  have hFx' := hF.contDiffAt (hU.mem_nhds hx')
  have hi' := annular_complexJacobian_differential_injective (hJ _ hx')
  have hd' := annular_complexRegularCoordinateEquiv_hasFDerivAt
    (hFx'.differentiableAt (by simp)) hi'
  exact (e.contDiffAt_symm hy
    (f₀' := annularComplexRegularCoordinateEquiv F (e.symm y) hi')
    (by rw [heF]; exact hd') (by rw [heF]; exact hFx')).contDiffWithinAt

/-- Compact actual fibers are finite once all their points lie in the actual
regular source. Interior placement is supplied by boundary avoidance later. -/
theorem annular_complex_fiber_finite {F : ℂ → ℂ} {K U : Set ℂ} {y : ℂ}
    (hK : IsCompact K) (hFc : ContinuousOn F K) (hU : IsOpen U)
    (hFs : ContDiffOn ℝ ∞ F U) (hJ : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0)
    (hSU : {x | x ∈ K ∧ F x = y} ⊆ U) : {x | x ∈ K ∧ F x = y}.Finite := by
  let S : Set ℂ := {x | x ∈ K ∧ F x = y}
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpre : IsClosed ((K.domRestrict F) ⁻¹' {y}) :=
    isClosed_singleton.preimage hFc.domRestrict
  have hS : IsCompact S := by
    convert hpre.isCompact.image continuous_subtype_val using 1
    ext x
    simp [S, and_comm]
  have hl : IsLocalHomeomorphOn F S := by
    intro x hx
    obtain ⟨e, he, _, heF, _⟩ := annular_complex_exists_smooth_local_inverse hU hFs hJ (hSU hx)
    exact ⟨e, he, heF.symm⟩
  have hd : IsDiscrete (F '' S) :=
    ((finite_singleton y).subset (by
      rintro z ⟨x, hx, rfl⟩
      exact hx.2)).isDiscrete
  exact hS.finite (hl.isDiscrete_of_image hd)

/-- Off the two boundary images, every actual source preimage is interior. -/
theorem annular_complex_fiber_subset_jordanInterior
    {F : ℂ → ℂ} {Houter Hinner : ℂ ≃ₜ ℂ} {y : ℂ}
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter)
    (hy : y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner))) :
    {x | x ∈ annularJordanClosure Houter Hinner ∧ F x = y} ⊆
      annularJordanInterior Houter Hinner := by
  intro x hx
  by_contra hi
  apply hy
  refine ⟨x, ?_, hx.2⟩
  rw [← frontier_annularJordanInterior Houter Hinner hnested,
    (annularJordanInterior_isOpen Houter Hinner).frontier_eq,
    closure_annularJordanInterior Houter Hinner hnested]
  exact ⟨hx.1, hi⟩

/-- The two source orientation signs are chosen before the map and target.
For every actual map, the resulting boundary angular sum is the common
actual Jacobian sign times the number of actual interior preimages. -/
theorem annular_complex_boundary_preimage_formula_with_orientation
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter) :
    ∃ εouter εinner : ℝ, |εouter| = 1 ∧ |εinner| = 1 ∧
      (∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        εouter * planarFormIntegral P Q γouter =
          ∫ z in jordanInterior Houter, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) ∧
      (∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        εinner * planarFormIntegral P Q γinner =
          ∫ z in jordanInterior Hinner, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) ∧
      ∀ (F : ℂ → ℂ) (O : Set ℂ), IsOpen O → ContDiffOn ℝ ∞ F O →
        annularJordanClosure Houter Hinner ⊆ O →
        ∀ (s : ℝ), |s| = 1 →
          (∀ z ∈ annularJordanInterior Houter Hinner, 0 < s * (fderiv ℝ F z).det) →
          ∀ (y : ℂ),
            y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner)) →
            εouter * planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
              εinner * planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner =
              s * ({x | x ∈ annularJordanClosure Houter Hinner ∧ F x = y}.ncard : ℝ) := by
  classical
  obtain ⟨εouter, εinner, hεouter, hεinner, hgreenOuter, hgreenInner, hGreen⟩ :=
    annular_boundary_green_excision_with_orientation houter hinner hnested
  refine ⟨εouter, εinner, hεouter, hεinner, hgreenOuter, hgreenInner, ?_⟩
  intro F O hO hF hKO s hs hJ y hy
  let K := annularJordanClosure Houter Hinner
  let U := annularJordanInterior Houter Hinner
  let S : Set ℂ := {x | x ∈ K ∧ F x = y}
  have hU : IsOpen U := annularJordanInterior_isOpen Houter Hinner
  have hUK : U ⊆ K := annularJordanInterior_subset_closure Houter Hinner
  have hFs : ContDiffOn ℝ ∞ F U := hF.mono (hUK.trans hKO)
  have hJne : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0 := by
    intro x hx heq
    have h := hJ x hx
    rw [heq, mul_zero] at h
    exact (lt_irrefl 0) h
  have hSU : S ⊆ U := annular_complex_fiber_subset_jordanInterior hnested hy
  have hS : S.Finite := annular_complex_fiber_finite
    (annularJordanClosure_isCompact Houter Hinner) (hF.continuousOn.mono hKO)
    hU hFs hJne hSU
  letI := hS.fintype
  have hlocal : ∀ x ∈ S, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧ (e : ℂ → ℂ) = F := by
    intro x hx
    obtain ⟨e, he, _, heF, _⟩ := annular_complex_exists_smooth_local_inverse hU hFs hJne (hSU hx)
    exact ⟨e, he, heF⟩
  obtain ⟨e, rS, heF, hrS, hdS, hdisks, _⟩ :=
    annular_exists_disjoint_local_inverse_disks hS hU hSU hlocal
  let n := Fintype.card S
  let index : Fin n ≃ S := (Fintype.equivFin S).symm
  let c : Fin n → ℂ := fun i => (index i : ℂ)
  let r : Fin n → ℝ := fun i => rS (index i)
  have hr : ∀ i, 0 < r i := fun i => hrS (index i)
  have hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)) := by
    intro i j hij
    exact hdS (fun he => hij (index.injective he))
  have hin : ∀ i, closedBall (c i) (r i) ⊆ U := fun i => (hdisks (index i)).1
  let A : Set ℂ := O ∩ {x | F x ≠ y}
  have hA : IsOpen A := hF.continuousOn.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  have hFA : ContDiffOn ℝ ∞ F A := hF.mono inter_subset_left
  have hAvoid : ∀ x ∈ A, F x ≠ y := fun _ hx => hx.2
  have hcore : annularGreenCore Houter Hinner c r ⊆ A := by
    intro x hx
    refine ⟨hKO hx.1, ?_⟩
    intro hxy
    let p : S := ⟨x, ⟨hx.1, hxy⟩⟩
    let i := index.symm p
    apply hx.2
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have hc : c i = x := by
      dsimp only [c, i]
      rw [index.apply_symm_apply]
    rw [hc]
    exact mem_ball_self (hr i)
  have hcontribution (i : Fin n) :
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y)
        (unitCircleParam (c i) (r i)) = s := by
    have hsrcE : closedBall (c i) (r i) ⊆ (e (index i)).source := (hdisks (index i)).2.1
    obtain ⟨v, hv, hproj, hturn, _⟩ := annular_local_circle_argument_sign
      hU hFs (e (index i)) (heF (index i)) (c i) (hr i) hsrcE (hin i)
      s hs (fun z hz => hJ z (hin i hz))
    have hcy : F (c i) = y := (index i).property.2
    have hcircle (t : ℝ) : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) := by
      simpa only [unitCircleParam, abs_of_pos (hr i)] using
        circleMap_mem_sphere' (c i) (r i) (2 * Real.pi * t)
    have hcurveA : ∀ t, unitCircleParam (c i) (r i) t ∈ A := by
      intro t
      have hball := sphere_subset_closedBall (hcircle t)
      refine ⟨hKO (hUK (hin i hball)), ?_⟩
      intro htarget
      have heq : unitCircleParam (c i) (r i) t = c i :=
        (hdisks (index i)).2.2 hball (mem_closedBall_self (hr i).le) (htarget.trans hcy.symm)
      have hbad := hcircle t
      rw [heq, mem_sphere, dist_self] at hbad
      exact (hr i).ne' hbad.symm
    have hprojY : ∀ t, (v t : UnitAddCircle) =
        normalizedArgument (F (unitCircleParam (c i) (r i) t) - y) := by
      intro t
      simpa only [hcy] using hproj t
    exact (annularAngularForm_integral_eq_lift hA hFA hAvoid
      (contDiff_unitCircleParam (c i) (r i)) hcurveA v hv.continuous hprojY).trans hturn
  have hformula := hGreen n c r hr hd hin A hA hcore
    (annularAngularFormP F y) (annularAngularFormQ F y)
    (annularAngularFormP_contDiffOn hA hFA hAvoid)
    (annularAngularFormQ_contDiffOn hA hFA hAvoid)
    (fun z hz => annularAngularForm_closed hA hFA hAvoid hz)
  rw [hformula]
  simp only [hcontribution, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [mul_comm]
  congr 1
  exact_mod_cast Set.fintypeCard_eq_ncard S


theorem annular_complex_boundary_preimage_formula
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter) :
    ∃ εouter εinner : ℝ, |εouter| = 1 ∧ |εinner| = 1 ∧
      ∀ (F : ℂ → ℂ) (O : Set ℂ), IsOpen O → ContDiffOn ℝ ∞ F O →
        annularJordanClosure Houter Hinner ⊆ O →
        ∀ (s : ℝ), |s| = 1 →
          (∀ z ∈ annularJordanInterior Houter Hinner, 0 < s * (fderiv ℝ F z).det) →
          ∀ (y : ℂ),
            y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner)) →
            εouter * planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
              εinner * planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner =
              s * ({x | x ∈ annularJordanClosure Houter Hinner ∧ F x = y}.ncard : ℝ) := by
  obtain ⟨εouter, εinner, hεouter, hεinner, _, _, hformula⟩ :=
    annular_complex_boundary_preimage_formula_with_orientation houter hinner hnested
  exact ⟨εouter, εinner, hεouter, hεinner, hformula⟩

/-- Every orientation selected by the ordinary Green identity equals the
actual normalized-argument turn of its source contour about an interior point. -/
theorem annular_source_orientation_eq_argument_integral
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (ε : ℝ)
    (hgreen : ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
      ε * planarFormIntegral P Q γ =
        ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) :
    ε = circleFormIntegral (fun _ => 1) (centeredArgument (H 0)) γ := by
  obtain ⟨ε', _, hgreen', hargument⟩ := annular_jordan_green_and_argument H γ hγ
  have hi : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (jordanInterior H) :=
    ((continuous_const.continuousOn).integrableOn_compact
      (isCompact_closure_jordanInterior H)).mono_set subset_closure
  have hpos : 0 < ∫ z in jordanInterior H, (1 : ℝ) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun _ => zero_le_one) hi).2
    have hsupp : support (fun _ : ℂ => (1 : ℝ)) = univ := by
      ext z
      simp [Function.support]
    rw [hsupp, univ_inter]
    exact (jordanInterior_isOpen H).measure_pos volume
      (isConnected_jordanInterior H).nonempty
  have hg := hgreen (fun _ => 0) Complex.re contDiff_const Complex.reCLM.contDiff
  have hg' := hgreen' (fun _ => 0) Complex.re contDiff_const Complex.reCLM.contDiff
  have hcurl : (fun z : ℂ => (fderiv ℝ Complex.re z) 1 -
      (fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z) Complex.I) = (fun _ => (1 : ℝ)) := by
    funext z
    change (fderiv ℝ (Complex.reCLM : ℂ → ℝ) z) 1 -
      (fderiv ℝ (Function.const ℂ (0 : ℝ)) z) Complex.I = 1
    rw [Complex.reCLM.hasFDerivAt.fderiv, fderiv_const]
    simp
  have hIne : planarFormIntegral (fun _ => 0) Complex.re γ ≠ 0 := by
    intro heq
    rw [hcurl, heq, mul_zero] at hg
    exact (ne_of_gt hpos) hg.symm
  have heps : ε = ε' := mul_right_cancel₀ hIne (hg.trans hg'.symm)
  have hcenter : H 0 ∈ jordanInterior H :=
    ⟨0, mem_ball_self zero_lt_one, rfl⟩
  obtain ⟨v, hv, hproj, hturn⟩ := hargument (H 0) hcenter
  have havoid : ∀ t, γ t ∈ {z : ℂ | z ≠ H 0} := by
    intro t heq
    have ht := hγ.mem_frontier t
    rw [(jordanInterior_isOpen H).frontier_eq] at ht
    exact ht.2 (heq ▸ hcenter)
  have hform := circleFormIntegral_constant_weight
    (isOpen_ne_fun continuous_id continuous_const) (smoothCircleOn_centeredArgument (H 0))
    (fun _ => 1) γ hγ.smooth havoid v hv.continuous hproj 1 (fun _ _ => rfl)
  have hform' : circleFormIntegral (fun _ => 1) (centeredArgument (H 0)) γ = ε' := by
    simpa only [one_mul, hturn] using hform
  exact heps.trans hform'.symm

/-- With actual positively oriented source contours, the boundary winding
sum counts all actual preimages with the actual constant Jacobian sign. -/
theorem annular_complex_positive_boundary_preimage_formula
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter)
    (hpositiveOuter : circleFormIntegral (fun _ => 1) (centeredArgument (Houter 0)) γouter = 1)
    (hpositiveInner : circleFormIntegral (fun _ => 1) (centeredArgument (Hinner 0)) γinner = 1)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : annularJordanClosure Houter Hinner ⊆ O)
    (s : ℝ) (hs : |s| = 1)
    (hJ : ∀ z ∈ annularJordanInterior Houter Hinner, 0 < s * (fderiv ℝ F z).det)
    (y : ℂ)
    (hy : y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner))) :
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner =
      s * ({x | x ∈ annularJordanClosure Houter Hinner ∧ F x = y}.ncard : ℝ) := by
  obtain ⟨εouter, εinner, _, _, hgreenOuter, hgreenInner, hformula⟩ :=
    annular_complex_boundary_preimage_formula_with_orientation houter hinner hnested
  have heOuter : εouter = 1 :=
    (annular_source_orientation_eq_argument_integral houter εouter hgreenOuter).trans hpositiveOuter
  have heInner : εinner = 1 :=
    (annular_source_orientation_eq_argument_integral hinner εinner hgreenInner).trans hpositiveInner
  simpa only [heOuter, heInner, one_mul] using hformula F O hO hF hKO s hs hJ y hy

end
end TightVer401

