import TightVer401.DualRadialCompletionPatch
import Mathlib.Topology.Order.Compact

/-! Construct the outgoing scalar branch through a retained Jordan cut.
The actual connector and neck supply the two scalar pieces and the open
recovery collar. Their cover and incoming retention are derived here. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem exists_dualRadialCompletion_outer_patch
    {Gin C Tail Literal : Coord → ℝ} {I J UC UT N V : Set Coord}
    (hJ : IsOpen J) (hCompact : IsCompact (closure J)) (h0J : (0 : Coord) ∈ J)
    (hIJ : closure I ⊆ J)
    (hUC : IsOpen UC) (hUT : IsOpen UT) (hN : IsOpen N) (hV : IsOpen V)
    (hConnector : J \ closure I ⊆ UC)
    (hExterior : (closure J)ᶜ ∩ {p : Coord | 0 < planarRadius p} ⊆ UT)
    (hFrontier : frontier J ⊆ V) (hVC : V ⊆ UC) (hVT : V ⊆ UT)
    (hNC : N ⊆ UC) (hIncoming : frontier I ⊆ N)
    (hIncomingPositive : frontier I ⊆ {p : Coord | 0 < planarRadius p})
    (hC : ContDiffOn ℝ ∞ C UC) (hTail : ContDiffOn ℝ ∞ Tail UT)
    (hnC : ∀ p ∈ UC, (planarHessian C p).det < 0)
    (hnTail : ∀ p ∈ UT, (planarHessian Tail p).det < 0)
    (hRecovery : EqOn C Tail V) (hRetained : EqOn C Gin N)
    {T0 : ℝ} (hLiteral : EqOn Tail Literal {p | T0 < planarRadius p}) :
    ∃ (Fo : Coord → ℝ) (Uo Nout : Set Coord) (L : ℝ),
      IsOpen Uo ∧ IsOpen Nout ∧ Nout ⊆ N ∧ frontier I ⊆ Nout ∧
      ((closure I)ᶜ ∩ {p : Coord | 0 < planarRadius p}) ∪ Nout ⊆ Uo ∧
      ContDiffOn ℝ ∞ Fo Uo ∧ (∀ p ∈ Uo, (planarHessian Fo p).det < 0) ∧
      EqOn Fo Gin Nout ∧ 0 < L ∧
      EqOn Fo Literal {p | L < planarRadius p} := by
  let P := {p : Coord | 0 < planarRadius p}
  let U0 := UC ∩ J ∩ P
  let U1 := ((closure J)ᶜ ∩ P) ∪ (V ∩ P)
  let Nout := N ∩ J ∩ P
  let Fo := dualRadialCompletionPatch U0 U1 C Tail Tail
  let Uo := U0 ∪ U1
  have hP : IsOpen P :=
    isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  have hU0 : IsOpen U0 := (hUC.inter hJ).inter hP
  have hU1 : IsOpen U1 :=
    (isClosed_closure.isOpen_compl.inter hP).union (hV.inter hP)
  have hNout : IsOpen Nout := (hN.inter hJ).inter hP
  have hSub1 : U1 ⊆ UT := by
    intro p hp
    rcases hp with hp | hp
    · exact hExterior hp
    · exact hVT hp.1
  have h01 : EqOn C Tail (U0 ∩ U1) := by
    intro p hp
    rcases hp.2 with he | hv
    · exact False.elim (he.1 (subset_closure hp.1.1.2))
    · exact hRecovery hv.1
  have h02 : EqOn C Tail (U0 ∩ (∅ : Set Coord)) := by simp
  have h12 : EqOn Tail Tail (U1 ∩ (∅ : Set Coord)) := fun _ _ => rfl
  obtain ⟨he0, he1, _⟩ := dualRadialCompletionPatch_eqOn h01 h02 h12
  have hCover : ((closure I)ᶜ ∩ P) ∪ Nout ⊆ Uo := by
    intro p hp
    rcases hp with hp | hp
    · by_cases hpJ : p ∈ J
      · exact Or.inl ⟨⟨hConnector ⟨hpJ,hp.1⟩,hpJ⟩,hp.2⟩
      · by_cases hpCl : p ∈ closure J
        · have hpFront : p ∈ frontier J := by
            rw [frontier,hJ.interior_eq]
            exact ⟨hpCl,hpJ⟩
          exact Or.inr (Or.inr ⟨hFrontier hpFront,hp.2⟩)
        · exact Or.inr (Or.inl ⟨hpCl,hp.2⟩)
    · exact Or.inl ⟨⟨hNC hp.1.1,hp.1.2⟩,hp.2⟩
  obtain ⟨pMax,hpMax,hMax⟩ := hCompact.exists_isMaxOn
    ⟨0,subset_closure h0J⟩ quadraticFillerCartesianGradient_radius_continuous.continuousOn
  let L := max (planarRadius pMax) (max T0 0) + 1
  have hL : 0 < L := by
    have hNonnegative : (0 : ℝ) ≤ max (planarRadius pMax) (max T0 0) :=
      (le_max_right T0 0).trans (le_max_right (planarRadius pMax) (max T0 0))
    dsimp [L]
    linarith
  refine ⟨Fo,Uo,Nout,L,hU0.union hU1,hNout,fun _ hp => hp.1.1,?_,hCover,?_,?_,?_,hL,?_⟩
  · intro p hp
    exact ⟨⟨hIncoming hp,hIJ (frontier_subset_closure hp)⟩,hIncomingPositive hp⟩
  · have hSmooth := dualRadialCompletionPatch_contDiffOn hU0 hU1 isOpen_empty
      h01 h02 h12 (hC.mono (fun _ hp => hp.1.1)) (hTail.mono hSub1) (by simp)
    exact hSmooth.mono (fun _ hp => Or.inl hp)
  · intro p hp
    exact dualRadialCompletionPatch_saddle hU0 hU1 isOpen_empty h01 h02 h12
      (fun p hp => hnC p hp.1.1) (fun p hp => hnTail p (hSub1 hp))
      (by simp) p (Or.inl hp)
  · intro p hp
    exact (he0 ⟨⟨hNC hp.1.1,hp.1.2⟩,hp.2⟩).trans (hRetained hp.1.1)
  · intro p hp
    have hpPos : p ∈ P := hL.trans hp
    have hpOutside : p ∉ closure J := by
      intro hpCl
      have hBound := (isMaxOn_iff.mp hMax) p hpCl
      have hLBound : planarRadius pMax < L := by
        dsimp [L]
        linarith [le_max_left (planarRadius pMax) (max T0 0)]
      exact (not_lt_of_ge hBound) (hLBound.trans hp)
    have hT : T0 < planarRadius p := by
      have := (le_max_left T0 0).trans (le_max_right (planarRadius pMax) (max T0 0))
      dsimp [L] at hp
      linarith
    exact (he1 (Or.inl ⟨hpOutside,hpPos⟩)).trans (hLiteral hT)

end
end TightVer401
