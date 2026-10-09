import TightVer401.AnnularDegreeCriterion

/-! Ordinary positive source/target loops and their literal actual map
identity construct one actual boundary homeomorphism and raw disk winding +1.
This supplies individual degree inputs; it grants no annular inverse/image. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem gradientInverseBoundary_representative {Hs : ℂ ≃ₜ ℂ}
    {gamma : ℝ → ℂ} (hgamma : RegularJordanParametrization Hs gamma)
    {z : ℂ} (hz : z ∈ frontier (jordanInterior Hs)) :
    ∃ t ∈ Ico (0 : ℝ) 1, gamma t = z := by
  obtain ⟨t, ht, htz⟩ := hgamma.boundary.symm ▸ hz
  by_cases ht1 : t < 1
  · exact ⟨t, ⟨ht.1, ht1⟩, htz⟩
  have htEq : t = 1 := le_antisymm ht.2 (le_of_not_gt ht1)
  refine ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
  have hp : gamma 1 = gamma 0 := by simpa only [zero_add] using hgamma.periodic 0
  exact hp.symm.trans (htEq ▸ htz)

/-- The SAME actual boundary restriction is a homeomorphism, derived from
ordinary loop embeddings and literal pointwise trace identity. -/
theorem visibleConnectorGradientInverseApplication_boundary_homeomorph
    {f : ℂ → ℂ} {O : Set ℂ} {Hs Ht : ℂ ≃ₜ ℂ} {gamma eta : ℝ → ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hSource : PositiveJordanParametrization Hs gamma)
    (hTarget : PositiveJordanParametrization Ht eta)
    (hBoundary : frontier (jordanInterior Hs) ⊆ O)
    (hTrace : ∀ t, f (gamma t) = eta t) :
    ∃ B : frontier (jordanInterior Hs) ≃ₜ frontier (jordanInterior Ht),
      ∀ z, (B z : ℂ) = f z := by
  have hgamma := hSource.toRegular
  have heta := hTarget.toRegular
  have hMaps : MapsTo f (frontier (jordanInterior Hs))
      (frontier (jordanInterior Ht)) := by
    intro z hz
    obtain ⟨t, _, htz⟩ := gradientInverseBoundary_representative hgamma hz
    rw [← htz, hTrace]
    exact heta.mem_frontier t
  have hInj : InjOn f (frontier (jordanInterior Hs)) := by
    intro z hz w hw he
    obtain ⟨t, ht, htz⟩ := gradientInverseBoundary_representative hgamma hz
    obtain ⟨s, hs, hsw⟩ := gradientInverseBoundary_representative hgamma hw
    have he' : eta t = eta s := by rw [← hTrace, ← hTrace, htz, hsw]; exact he
    exact htz.symm.trans ((congrArg gamma (heta.injective ht hs he')).trans hsw)
  have hSurj : SurjOn f (frontier (jordanInterior Hs))
      (frontier (jordanInterior Ht)) := by
    intro y hy
    obtain ⟨t, _, hty⟩ := heta.boundary.symm ▸ hy
    exact ⟨gamma t, hgamma.mem_frontier t, (hTrace t).trans hty⟩
  let g : frontier (jordanInterior Hs) → frontier (jordanInterior Ht) :=
    fun z => ⟨f z, hMaps z.property⟩
  have hg : Bijective g := by
    constructor
    · intro z w he
      exact Subtype.ext (hInj z.property w.property (congrArg Subtype.val he))
    · intro y
      obtain ⟨z, hz, hzy⟩ := hSurj y.property
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  let B := Equiv.ofBijective g hg
  have hB : Continuous B := (hf.continuousOn.mono hBoundary).domRestrict.subtype_mk _
  let : CompactSpace (frontier (jordanInterior Hs)) :=
    isCompact_iff_compactSpace.mp (annular_jordan_frontier_isCompact Hs)
  exact ⟨hB.homeoOfEquivCompactToT2, fun _ => rfl⟩

/-- Positive actual target orientation gives raw angular integral +1,
including when the parent degree application swaps boundary components. -/
theorem visibleConnectorGradientInverseApplication_boundary_winding
    {f : ℂ → ℂ} {O : Set ℂ} {Hs Ht : ℂ ≃ₜ ℂ} {gamma eta : ℝ → ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hSource : PositiveJordanParametrization Hs gamma)
    (hTarget : PositiveJordanParametrization Ht eta)
    (hBoundary : frontier (jordanInterior Hs) ⊆ O)
    (hTrace : ∀ t, f (gamma t) = eta t) :
    planarFormIntegral (annularAngularFormP f (Ht 0))
      (annularAngularFormQ f (Ht 0)) gamma = 1 := by
  have hCenter : Ht 0 ∈ jordanInterior Ht := ⟨0, mem_ball_self zero_lt_one, rfl⟩
  have hAvoid : ∀ t, f (gamma t) ≠ Ht 0 := by
    intro t he
    rw [hTrace] at he
    have ht := hTarget.toRegular.mem_frontier t
    rw [frontier, (jordanInterior_isOpen Ht).interior_eq] at ht
    exact ht.2 (he.symm ▸ hCenter)
  obtain ⟨u, hu, hturn⟩ := hTarget.positive (Ht 0) hCenter
  have hgammaO : ∀ t, gamma t ∈ O :=
    fun t => hBoundary (hSource.toRegular.mem_frontier t)
  rw [annularAngularForm_integral_eq_pathIncrement hO hf hSource.smooth hgammaO (Ht 0) hAvoid]
  unfold pathArgumentIncrement
  rw [circlePathIncrement_eq_lift _ u (fun t => by
    change (u t : UnitAddCircle) = normalizedArgument (f (gamma t) - Ht 0)
    rw [hTrace]
    exact hu t), hturn]
  ring

/-- Both individual ordinary boundary inputs needed by the actual degree
producer, constructed together from the SAME literal trace data. -/
theorem visibleConnectorGradientInverseApplication_ordinary_boundary
    {f : ℂ → ℂ} {O : Set ℂ} {Hs Ht : ℂ ≃ₜ ℂ} {gamma eta : ℝ → ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hSource : PositiveJordanParametrization Hs gamma)
    (hTarget : PositiveJordanParametrization Ht eta)
    (hBoundary : frontier (jordanInterior Hs) ⊆ O)
    (hTrace : ∀ t, f (gamma t) = eta t) :
    ∃ B : frontier (jordanInterior Hs) ≃ₜ frontier (jordanInterior Ht),
      (∀ z, (B z : ℂ) = f z) ∧
      planarFormIntegral (annularAngularFormP f (Ht 0))
        (annularAngularFormQ f (Ht 0)) gamma = 1 := by
  obtain ⟨B, hB⟩ := visibleConnectorGradientInverseApplication_boundary_homeomorph
    hO hf hSource hTarget hBoundary hTrace
  exact ⟨B, hB, visibleConnectorGradientInverseApplication_boundary_winding
    hO hf hSource hTarget hBoundary hTrace⟩

end
end TightVer401
