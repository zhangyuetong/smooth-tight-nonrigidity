import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof

/-! Annular excision for an actual closed planar one-form. The two source
boundaries are arbitrary regular Jordan circuits. The signs are obtained
from the proved pinned Green formulas before the holes or form are chosen.
No degree, image, or injectivity conclusion is an input. -/
namespace TightVer401
noncomputable section
open Set Function Metric MeasureTheory
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff BigOperators

/-- The closed source annulus after removing finitely many open round
disks, retaining every boundary on which the form will be integrated. -/
def annularGreenCore (Houter Hinner : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ) : Set ℂ :=
  (closure (jordanInterior Houter) \ jordanInterior Hinner) \ ⋃ i, ball (c i) (r i)

theorem annularGreenCore_isClosed (Houter Hinner : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ) :
    IsClosed (annularGreenCore Houter Hinner c r) :=
  (isClosed_closure.sdiff (jordanInterior_isOpen Hinner)).sdiff
    (isOpen_iUnion fun _ => isOpen_ball)

/-- The boundary sum of a closed form equals the sum on the positively
traversed small disks. Smoothness is required only on a neighborhood of
the retained punctured annulus; the form need not exist in the inner disk
or at the removed centers. Both signs are uniform over holes and forms. -/
theorem annular_boundary_green_excision_with_orientation
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
      ∀ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        Pairwise (Disjoint on fun i => closedBall (c i) (r i)) →
        (∀ i, closedBall (c i) (r i) ⊆
          jordanInterior Houter \ closure (jordanInterior Hinner)) →
        ∀ (O : Set ℂ), IsOpen O → annularGreenCore Houter Hinner c r ⊆ O →
        ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ ∞ P O → ContDiffOn ℝ ∞ Q O →
        (∀ z ∈ O, (fderiv ℝ Q z) 1 = (fderiv ℝ P z) Complex.I) →
        εouter * planarFormIntegral P Q γouter -
          εinner * planarFormIntegral P Q γinner =
          ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) := by
  classical
  obtain ⟨εouter, hεouter, hgreenOuter⟩ :=
    unorientedFiniteCircleGreenFormula Houter γouter houter
  obtain ⟨εinner, hεinner, hgreenInner⟩ := regular_jordan_green hinner
  refine ⟨εouter, εinner, hεouter, hεinner, ?_, hgreenInner, ?_⟩
  · intro P Q hP hQ
    simpa using hgreenOuter 0 (Fin.elim0) (Fin.elim0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) univ isOpen_univ (subset_univ _)
      P Q hP.contDiffOn hQ.contDiffOn
  intro n c r hr hd hin O hO hsub P Q hP hQ hclosed
  let A := annularGreenCore Houter Hinner c r
  have hA : IsClosed A := annularGreenCore_isClosed Houter Hinner c r
  obtain ⟨p, hp, hep, _⟩ := exists_smooth_collar_extension hO hA hsub hP 0
  obtain ⟨q, hq, heq, _⟩ := exists_smooth_collar_extension hO hA hsub hQ 0
  have hinOuter (i : Fin n) : closedBall (c i) (r i) ⊆ jordanInterior Houter :=
    fun z hz => (hin i hz).1
  have houterA (t : ℝ) : γouter t ∈ A := by
    have ht := jordan_boundary_mem_finite_hole_core houter c r hinOuter t
    refine ⟨⟨ht.1, ?_⟩, ht.2⟩
    intro hi
    exact (houter.mem_frontier t).2
      ((jordanInterior_isOpen Houter).interior_eq.symm ▸
        hnested (subset_closure hi))
  have hinnerA (t : ℝ) : γinner t ∈ A := by
    have ht := hinner.mem_frontier t
    refine ⟨⟨subset_closure (hnested ht.1), ?_⟩, ?_⟩
    · exact fun hi => ht.2 ((jordanInterior_isOpen Hinner).interior_eq.symm ▸ hi)
    · intro hm
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact (hin i (ball_subset_closedBall hi)).2 ht.1
  have hcircleA (i : Fin n) (t : ℝ) : unitCircleParam (c i) (r i) t ∈ A := by
    have ht := circle_mem_finite_hole_core Houter c r hr hd hinOuter i t
    have hs : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) := by
      simpa only [unitCircleParam, abs_of_pos (hr i)] using
        circleMap_mem_sphere' (c i) (r i) (2 * Real.pi * t)
    refine ⟨⟨ht.1, ?_⟩, ht.2⟩
    exact fun hi => (hin i (sphere_subset_closedBall hs)).2 (subset_closure hi)
  have htrace (γ : ℝ → ℂ) (hγA : ∀ t, γ t ∈ A) :
      planarFormIntegral p q γ = planarFormIntegral P Q γ := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hep.self_of_nhdsSet (hγA t), heq.self_of_nhdsSet (hγA t)]
  have hOuterTrace := htrace γouter houterA
  have hInnerTrace := htrace γinner hinnerA
  have hCircleTrace : (∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i))) =
      ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact htrace _ (hcircleA i)
  let curl : ℂ → ℝ := fun z => (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I
  let B : Set ℂ := jordanInterior Houter \ ⋃ i, closedBall (c i) (r i)
  have hB : MeasurableSet B := (jordanInterior_isOpen Houter).measurableSet.diff
    (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  have hinnerB : jordanInterior Hinner ⊆ B := by
    intro z hz
    refine ⟨hnested (subset_closure hz), ?_⟩
    intro hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    exact (hin i hi).2 (subset_closure hz)
  have hcurl : ∀ z ∈ B \ jordanInterior Hinner, curl z = 0 := by
    intro z hz
    have hzA : z ∈ A := by
      refine ⟨⟨subset_closure hz.1.1, hz.2⟩, ?_⟩
      intro hm
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact hz.1.2 (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)
    have hepz := hep.filter_mono (nhds_le_nhdsSet hzA)
    have heqz := heq.filter_mono (nhds_le_nhdsSet hzA)
    dsimp only [curl]
    rw [hepz.fderiv_eq, heqz.fderiv_eq]
    exact sub_eq_zero.mpr (hclosed z (hsub hzA))
  have harea : (∫ z in B, curl z) = ∫ z in jordanInterior Hinner, curl z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB hinnerB hcurl
  have ho := hgreenOuter n c r hr hd hinOuter univ isOpen_univ
    (subset_univ _) p q hp.contDiffOn hq.contDiffOn
  have hi := hgreenInner p q hp hq
  change εouter * planarFormIntegral p q γouter -
    ∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i)) = ∫ z in B, curl z at ho
  change εinner * planarFormIntegral p q γinner =
    ∫ z in jordanInterior Hinner, curl z at hi
  rw [harea, ← hi, hOuterTrace, hInnerTrace, hCircleTrace] at ho
  linarith

/-- Excision-only interface; the stronger export also retains source orientation. -/
theorem annular_boundary_green_excision
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter) :
    ∃ εouter εinner : ℝ, |εouter| = 1 ∧ |εinner| = 1 ∧
      ∀ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        Pairwise (Disjoint on fun i => closedBall (c i) (r i)) →
        (∀ i, closedBall (c i) (r i) ⊆
          jordanInterior Houter \ closure (jordanInterior Hinner)) →
        ∀ (O : Set ℂ), IsOpen O → annularGreenCore Houter Hinner c r ⊆ O →
        ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ ∞ P O → ContDiffOn ℝ ∞ Q O →
        (∀ z ∈ O, (fderiv ℝ Q z) 1 = (fderiv ℝ P z) Complex.I) →
        εouter * planarFormIntegral P Q γouter -
          εinner * planarFormIntegral P Q γinner =
          ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) := by
  obtain ⟨εo, εi, ho, hi, _, _, h⟩ :=
    annular_boundary_green_excision_with_orientation houter hinner hnested
  exact ⟨εo, εi, ho, hi, h⟩

end
end TightVer401
