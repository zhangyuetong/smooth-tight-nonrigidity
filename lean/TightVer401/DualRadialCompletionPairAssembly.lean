import TightVer401.DualRadialCompletionAssembly
import TightVer401.QuadraticRadialFillingBoundary
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Compact

/-! Final internal assembly of two actual local branches and the retained
potential. Producer invocations constructing those branches remain external
caller obligations; this is not an inhabitant of the public completion claim. -/
namespace TightVer401
noncomputable section
open Set Filter Function Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem pairAssembly_norm_le_radius (p : Coord) : ‖p‖ ≤ planarRadius p := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact quadraticRadialFilling_abs_coord_le_radius p i

/-- Nested source regions and their genuine incoming neighborhoods derive
the cover, all overlaps and the protected old-potential neighborhood. The
same scalar patch then supplies both ends and its actual gradient inverse. -/
theorem exists_dualRadialCompletion_pair_assembly
    (hDegree : DualRadialCompletionCircularDegreeClaim)
    {G Fi Fo : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    {I O Ui Uo Nin Nout K : Set Coord}
    (hI : IsOpen I) (hO : IsOpen O) (hIO : closure I ⊆ O) (h0I : (0 : Coord) ∈ I)
    (hCompactO : IsCompact (closure O))
    (hBand : closure O \ I ⊆ e0.source)
    (hG : ContDiffOn ℝ ∞ G e0.source)
    (hnG : ∀ p ∈ e0.source, (planarHessian G p).det < 0)
    (_hUi : IsOpen Ui) (_hUo : IsOpen Uo)
    (hNin : IsOpen Nin) (hNout : IsOpen Nout)
    (_hNinSource : Nin ⊆ e0.source) (_hNoutSource : Nout ⊆ e0.source)
    (hFrontierI : frontier I ⊆ Nin) (hFrontierO : frontier O ⊆ Nout)
    (hUi : (I ∩ {p : Coord | 0 < planarRadius p}) ∪ Nin ⊆ Ui)
    (hUo : ((closure O)ᶜ ∩ {p : Coord | 0 < planarRadius p}) ∪ Nout ⊆ Uo)
    (hFi : ContDiffOn ℝ ∞ Fi Ui) (hFo : ContDiffOn ℝ ∞ Fo Uo)
    (hnFi : ∀ p ∈ Ui, (planarHessian Fi p).det < 0)
    (hnFo : ∀ p ∈ Uo, (planarHessian Fo p).det < 0)
    (hInEq : EqOn Fi G Nin) (hOutEq : EqOn Fo G Nout)
    (_hK : IsCompact K) (hK : K ⊆ O \ closure I)
    {RN mu A B d0 dInfinity epsilon0 L0 : ℝ}
    (hA : 0 < A) (hAR : A < RN) (hmu : 0 < mu) (hB : 0 < B) (hepsilon0 : 0 < epsilon0)
    (hInner : EqOn Fi (fun p => RN*planarRadius p-mu*planarRadius p^2/2+d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon0})
    (hOuter : EqOn Fo (fun p => A*planarRadius p-B/planarRadius p+dInfinity)
      {p | L0 < planarRadius p}) :
    ∃ (epsilon L : ℝ) (F : Coord → ℝ) (W : Set Coord)
      (e : OpenPartialHomeomorph Coord Coord),
      0 < epsilon ∧ epsilon < L ∧
      ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → (planarHessian F p).det < 0) ∧
      IsOpen W ∧ K ⊆ W ∧ W ⊆ e0.source ∧ W ⊆ {p | 0 < planarRadius p} ∧
      EqOn F G W ∧ (∀ p ∈ W, F =ᶠ[𝓝 p] G) ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        F p = RN*planarRadius p-mu*planarRadius p^2/2+d0) ∧
      (∀ p, L < planarRadius p → F p = A*planarRadius p-B/planarRadius p+dInfinity) ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        F =ᶠ[𝓝 p] (fun q => RN*planarRadius q-mu*planarRadius q^2/2+d0)) ∧
      (∀ p, L < planarRadius p →
        F =ᶠ[𝓝 p] (fun q => A*planarRadius q-B/planarRadius q+dInfinity)) ∧
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (e : Coord → Coord) = planarGradient F ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let P : Set Coord := {p | 0 < planarRadius p}
  let U0 := (I ∩ P) ∪ (Nin ∩ O ∩ P)
  let U1 := e0.source ∩ O ∩ (closure I)ᶜ ∩ P
  let U2 := ((closure O)ᶜ ∩ P) ∪ (Nout ∩ (closure I)ᶜ ∩ P)
  have hP : IsOpen P := isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  have hU0 : IsOpen U0 := (hI.inter hP).union ((hNin.inter hO).inter hP)
  have hU1 : IsOpen U1 := ((e0.open_source.inter hO).inter isClosed_closure.isOpen_compl).inter hP
  have hU2 : IsOpen U2 := (isClosed_closure.isOpen_compl.inter hP).union
    ((hNout.inter isClosed_closure.isOpen_compl).inter hP)
  have hSub0 : U0 ⊆ Ui := by
    intro p hp
    rcases hp with hp | hp
    · exact hUi (Or.inl hp)
    · exact hUi (Or.inr hp.1.1)
  have hSub1 : U1 ⊆ e0.source := fun _ hp => hp.1.1.1
  have hSub2 : U2 ⊆ Uo := by
    intro p hp
    rcases hp with hp | hp
    · exact hUo (Or.inl hp)
    · exact hUo (Or.inr hp.1.1)
  have hcover : P ⊆ U0 ∪ U1 ∪ U2 := by
    intro p hp
    by_cases hpI : p ∈ I
    · exact Or.inl (Or.inl (Or.inl ⟨hpI,hp⟩))
    · by_cases hpClI : p ∈ closure I
      · have hN : p ∈ Nin := hFrontierI ⟨hpClI,by rwa [hI.interior_eq]⟩
        exact Or.inl (Or.inl (Or.inr ⟨⟨hN,hIO hpClI⟩,hp⟩))
      · by_cases hpO : p ∈ O
        · have hpS : p ∈ e0.source := hBand ⟨subset_closure hpO,hpI⟩
          exact Or.inl (Or.inr ⟨⟨⟨hpS,hpO⟩,hpClI⟩,hp⟩)
        · by_cases hpClO : p ∈ closure O
          · have hN : p ∈ Nout := hFrontierO ⟨hpClO,by rwa [hO.interior_eq]⟩
            exact Or.inr (Or.inr ⟨⟨hN,hpClI⟩,hp⟩)
          · exact Or.inr (Or.inl ⟨hpClO,hp⟩)
  have h01 : EqOn Fi G (U0 ∩ U1) := by
    intro p hp
    rcases hp.1 with hpI | hpN
    · exact False.elim (hp.2.1.2 (subset_closure hpI.1))
    · exact hInEq hpN.1.1
  have h02 : EqOn Fi Fo (U0 ∩ U2) := by
    intro p hp
    rcases hp.1 with hpI | hpN
    · rcases hp.2 with hpO | hpOut
      · exact False.elim (hpO.1 (subset_closure (hIO (subset_closure hpI.1))))
      · exact False.elim (hpOut.1.2 (subset_closure hpI.1))
    · rcases hp.2 with hpO | hpOut
      · exact False.elim (hpO.1 (subset_closure hpN.1.2))
      · exact (hInEq hpN.1.1).trans (hOutEq hpOut.1.1).symm
  have h12 : EqOn G Fo (U1 ∩ U2) := by
    intro p hp
    rcases hp.2 with hpO | hpN
    · exact False.elim (hpO.1 (subset_closure hp.1.1.1.2))
    · exact (hOutEq hpN.1.1).symm
  have hKW : K ⊆ U1 := by
    intro p hp
    have hk := hK hp
    have hp0 : p ≠ 0 := by
      intro he
      apply hk.2
      rw [he]
      exact subset_closure h0I
    have hpP : p ∈ P := (norm_pos_iff.mpr hp0).trans_le (pairAssembly_norm_le_radius p)
    exact ⟨⟨⟨hBand ⟨subset_closure hk.1,fun hpi => hk.2 (subset_closure hpi)⟩,hk.1⟩,hk.2⟩,hpP⟩
  obtain ⟨delta,hdelta,hBall⟩ := Metric.isOpen_iff.mp hI 0 h0I
  let m := min delta (min epsilon0 1)
  let epsilon := m/2
  have hm : 0 < m := lt_min hdelta (lt_min hepsilon0 zero_lt_one)
  have hepsilon : 0 < epsilon := half_pos hm
  have hem : epsilon < m := half_lt_self hm
  have hedelta : epsilon < delta := hem.trans_le (min_le_left _ _)
  have heeps : epsilon < epsilon0 := hem.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heone : epsilon < 1 := hem.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Q,hQ⟩ := hCompactO.bddAbove_image quadraticFillerCartesianGradient_radius_continuous.continuousOn
  let T := max Q (max L0 1)
  let L := T+1
  have hTL : T < L := by dsimp [L]; linarith
  have hQL : Q < L := (le_max_left _ _).trans_lt hTL
  have hL0 : L0 < L := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hTL
  have hL1 : 1 < L := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hTL
  have heL : epsilon < L := heone.trans hL1
  have hInnerSet : {p : Coord | 0 < planarRadius p ∧ planarRadius p < epsilon} ⊆ U0 := by
    intro p hp
    have hpBall : p ∈ ball (0 : Coord) delta := by
      rw [mem_ball,dist_zero_right]
      exact (pairAssembly_norm_le_radius p).trans_lt (hp.2.trans hedelta)
    exact Or.inl ⟨hBall hpBall,hp.1⟩
  have hOuterSet : {p : Coord | L < planarRadius p} ⊆ U2 := by
    intro p hp
    have hpCl : p ∉ closure O := by
      intro hpCl
      have hb : planarRadius p ≤ Q := hQ ⟨p,hpCl,rfl⟩
      exact (not_lt_of_ge hb) (hQL.trans hp)
    exact Or.inl ⟨hpCl,zero_lt_one.trans (hL1.trans hp)⟩
  have hInner' : EqOn Fi (fun p => RN*planarRadius p-mu*planarRadius p^2/2+d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon} :=
    fun _ hp => hInner ⟨hp.1,hp.2.trans heeps⟩
  have hOuter' : EqOn Fo (fun p => A*planarRadius p-B/planarRadius p+dInfinity)
      {p | L < planarRadius p} := fun _ hp => hOuter (hL0.trans hp)
  obtain ⟨F,e,hF,hnF,hRetain,hRetainGerm,hIF,hOF,hIG,hOG,hs,ht,hActual,hi⟩ :=
    exists_dualRadialCompletion_assembly_of_circular_degree hDegree hA hAR hmu hB hepsilon
      hU0 hU1 hU2 hcover h01 h02 h12 (hFi.mono hSub0) (hG.mono hSub1) (hFo.mono hSub2)
      (fun p hp => hnFi p (hSub0 hp)) (fun p hp => hnG p (hSub1 hp))
      (fun p hp => hnFo p (hSub2 hp)) hU1 (Subset.rfl : U1 ⊆ U1)
      (fun _ _ => rfl : EqOn G G U1) hInnerSet hOuterSet hInner' hOuter'
  exact ⟨epsilon,L,F,U1,e,hepsilon,heL,hF,hnF,hU1,hKW,hSub1,(fun _ hp => hp.2),
    hRetain,hRetainGerm,(fun p hp he => hIF ⟨hp,he⟩),(fun p hp => hOF hp),hIG,hOG,hs,ht,hActual,hi⟩

end
end TightVer401
