import TightVer401.QuadraticRadialFillingGlobalContract
import TightVer401.ComplexCircleDirection
import OAI.Analysis.CircleDomains.Selection.OuterContours
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

/-! A genuine new Jordan filling at a retained cut strictly inside the SAME
actual gradient inverse. The original target hole is retained explicitly.
The nesting is derived from the inverse and the unit turn of the source
circle; no winding or nesting conclusion is supplied as a premise. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

private theorem quadraticRadialFillingRetainedTrace_source_circle
    {S S0 : ℝ} {e : OpenPartialHomeomorph Coord Coord}
    (hS0 : 0 < S0) (hcut : S0 < S)
    (hes : e.source = quadraticRadialFillingPuncturedDisk S) (t : ℝ) :
    saddlePolarChart ![S0,t] ∈ e.source := by
  rw [hes]
  change 0 < planarRadius (saddlePolarChart ![S0,t]) ∧
    planarRadius (saddlePolarChart ![S0,t]) < S
  rw [angularDescent_radius_polar (q := ![S0,t]) hS0]
  exact ⟨hS0,hcut⟩

private theorem quadraticRadialFillingRetainedTrace_source_direction
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    complexCircleDirection (quadraticRadialFillingCircle r t) = Circle.exp t := by
  have hz : quadraticRadialFillingCircle r t ≠ 0 := circleMap_ne_center hr.ne'
  apply complexCircleDirection_eq_of_exp hz
  simp [quadraticRadialFillingCircle, norm_circleMap_zero, abs_of_pos hr,
    circleMap_zero, Complex.real_smul, hr.ne']

/-- The actual inverse forbids filling a genuine retained gradient loop by a
closed disk lying wholly inside its own target. The source's actual angle
would then extend over a contractible disk, contradicting its single turn. -/
theorem quadraticRadialFillingRetainedTrace_closedDisk_not_subset_target
    {H : Coord → ℝ} {S S0 : ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph Coord Coord} {Γ0 : ℂ ≃ₜ ℂ}
    (hS0 : 0 < S0) (hcut : S0 < S)
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hDiskV : quadraticRadialFillingPuncturedDisk S ⊆ V)
    (hes : e.source = quadraticRadialFillingPuncturedDisk S)
    (he : (e : Coord → Coord) = planarGradient H)
    (hboundary : range (quadraticRadialFillingGradientComplexTrace H S0) =
      Γ0 '' sphere (0 : ℂ) 1) :
    ¬ Γ0 '' closedBall (0 : ℂ) 1 ⊆ seamComplexCoord ⁻¹' e.target := by
  classical
  intro hsub
  let D : Set ℂ := closedBall (0 : ℂ) 1
  letI : ContractibleSpace D := (convex_closedBall (0 : ℂ) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  letI : LocallyPathConnectedSpace D :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  have hCircle (t : ℝ) := quadraticRadialFillingRetainedTrace_source_circle hS0 hcut hes t
  have hCircleV : {x : Coord | planarRadius x = S0} ⊆ V := by
    intro x hx
    apply hDiskV
    change 0 < planarRadius x ∧ planarRadius x < S
    rw [hx]
    exact ⟨hS0,hcut⟩
  let η := quadraticRadialFillingGradientComplexTrace H S0
  have hη : Continuous η :=
    (quadraticRadialFillingGradientComplexTrace_contDiff hS0 hV hH hCircleV).continuous
  have htarget (z : D) : seamComplexCoord (Γ0 z) ∈ e.target :=
    hsub ⟨z,z.property,rfl⟩
  let g : D → ℂ := fun z => angularDescentComplex (e.symm (seamComplexCoord (Γ0 z)))
  have hg : Continuous g := angularDescentComplex_contDiff.continuous.comp
    (e.continuousOn_symm.comp_continuous
      (seamComplexCoord.continuous.comp (Γ0.continuous.comp continuous_subtype_val)) htarget)
  have hgnz (z : D) : g z ≠ 0 := by
    have hx := e.map_target (htarget z)
    rw [hes] at hx
    have hp : 0 < planarRadius (e.symm (seamComplexCoord (Γ0 z))) := hx.1
    intro hz
    have hn : ‖g z‖ = 0 := by rw [hz,norm_zero]
    change ‖angularDescentComplex (e.symm (seamComplexCoord (Γ0 z)))‖ = 0 at hn
    rw [angularDescentComplex_norm] at hn
    exact (ne_of_gt hp) hn
  let F : C(D, Circle) := ⟨fun z => complexCircleDirection (g z),
    complexCircleDirection_continuousOn.comp_continuous hg (fun z => hgnz z)⟩
  have hcMem (t : ℝ) : Γ0.symm (η t) ∈ D := by
    have ht : η t ∈ Γ0 '' sphere (0 : ℂ) 1 := hboundary ▸ mem_range_self t
    obtain ⟨z,hz,heq⟩ := ht
    rw [← heq,Γ0.symm_apply_apply]
    exact sphere_subset_closedBall hz
  let c : ℝ → D := fun t => ⟨Γ0.symm (η t),hcMem t⟩
  have hc : Continuous c := (Γ0.symm.continuous.comp hη).subtype_mk _
  have hproj (t : ℝ) : F (c t) = Circle.exp t := by
    have hinv : e.symm (seamComplexCoord (η t)) = saddlePolarChart ![S0,t] := by
      have hcoord : seamComplexCoord (η t) = e (saddlePolarChart ![S0,t]) := by
        rw [he]
        exact quadraticRadialFillingCoord_complex _
      rw [hcoord]
      exact e.left_inv (hCircle t)
    change complexCircleDirection
      (angularDescentComplex (e.symm (seamComplexCoord (Γ0 (Γ0.symm (η t)))))) = _
    rw [Γ0.apply_symm_apply,hinv,← quadraticRadialFillingCircle_coord,
      quadraticRadialFillingComplex_coord]
    exact quadraticRadialFillingRetainedTrace_source_direction hS0 t
  obtain ⟨u,⟨hu0,hulift⟩,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F (c 0) 0 (hproj 0).symm
  have hcomp : Circle.exp ∘ (u ∘ c) = Circle.exp ∘ (id : ℝ → ℝ) := by
    funext t
    exact (congrFun hulift (c t)).trans (hproj t)
  have heq : u ∘ c = (id : ℝ → ℝ) := Circle.isCoveringMap_exp.eq_of_comp_eq
    (u.continuous.comp hc) continuous_id hcomp 0 hu0
  have hηClosed : η (2 * Real.pi) = η 0 := by
    simpa only [zero_add] using quadraticRadialFillingGradientComplexTrace_periodic H S0 0
  have hcClosed : c (2 * Real.pi) = c 0 := Subtype.ext (congrArg Γ0.symm hηClosed)
  have hturn : 2 * Real.pi = 0 := by
    calc
      2 * Real.pi = u (c (2 * Real.pi)) := (congrFun heq (2 * Real.pi)).symm
      _ = u (c 0) := congrArg u hcClosed
      _ = 0 := congrFun heq 0
  exact Real.two_pi_pos.ne' hturn

/-- A retained cut has its own genuine Jordan filling. Both strict target
nestings follow from the SAME actual gradient inverse; the original filling
is not renamed or replaced. The theorem needs no extra radial sign at S0. -/
theorem quadraticRadialFillingRetainedTrace_exists_filling
    {H : Coord → ℝ} {S S0 L : ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph Coord Coord} (Γ : ℂ ≃ₜ ℂ)
    (hS0 : 0 < S0) (hcut : S0 < S) (hL : 0 < L)
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hDiskV : quadraticRadialFillingPuncturedDisk S ⊆ V)
    (hes : e.source = quadraticRadialFillingPuncturedDisk S)
    (het : e.target = quadraticRadialFillingGlobalGradientTarget Γ L)
    (he : (e : Coord → Coord) = planarGradient H) :
    ∃ Γ0 : ℂ ≃ₜ ℂ,
      range (quadraticRadialFillingGradientComplexTrace H S0) = Γ0 '' sphere (0 : ℂ) 1 ∧
      Γ '' closedBall (0 : ℂ) 1 ⊆ Γ0 '' ball (0 : ℂ) 1 ∧
      Γ0 '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) L := by
  classical
  have hCircleSource : {x : Coord | planarRadius x = S0} ⊆ e.source := by
    intro x hx
    rw [hes]
    change 0 < planarRadius x ∧ planarRadius x < S
    rw [hx]
    exact ⟨hS0,hcut⟩
  have hCircleV : {x : Coord | planarRadius x = S0} ⊆ V := by
    intro x hx
    apply hDiskV
    rw [← hes]
    exact hCircleSource hx
  have hinj : InjOn (planarGradient H) e.source := by rw [← he]; exact e.injOn
  obtain ⟨Γ0,hboundary⟩ := quadraticRadialFillingGradientComplexTrace_exists_filling
    hS0 hV hH hCircleV hCircleSource hinj
  have htraceTarget (t : ℝ) : quadraticRadialFillingGradientComplexTrace H S0 t ∈
      ball (0 : ℂ) L \ Γ '' closedBall (0 : ℂ) 1 := by
    have hp := quadraticRadialFillingRetainedTrace_source_circle hS0 hcut hes t
    have ht := e.map_source hp
    rw [het] at ht
    obtain ⟨z,hz,hez⟩ := ht
    have hze : z = quadraticRadialFillingGradientComplexTrace H S0 t := by
      apply seamComplexCoord.injective
      rw [hez,he]
      exact (quadraticRadialFillingCoord_complex _).symm
    exact hze ▸ hz
  have hfront : frontier (jordanInterior Γ0) ⊆
      ball (0 : ℂ) L \ closure (jordanInterior Γ) := by
    rw [frontier_jordanInterior,← hboundary,closure_jordanInterior]
    rintro z ⟨t,rfl⟩
    exact htraceTarget t
  have hbound : closure (jordanInterior Γ0) ⊆ ball (0 : ℂ) L := by
    have h := closed_jordanInterior_subset_of_frontier_subset Γ0 (roundDiskChart L hL)
      (by rw [roundDiskChart_interior]; exact fun z hz => (hfront hz).1)
    rwa [roundDiskChart_interior] at h
  have hdisj : Disjoint (frontier (jordanInterior Γ)) (frontier (jordanInterior Γ0)) := by
    apply Set.disjoint_left.mpr
    intro z hz hz0
    exact (hfront hz0).2 (frontier_subset_closure hz)
  have hnested : closure (jordanInterior Γ) ⊆ jordanInterior Γ0 := by
    rcases disjoint_or_nested_jordanInteriors Γ Γ0 hdisj with hd | hn | hr
    · exfalso
      apply quadraticRadialFillingRetainedTrace_closedDisk_not_subset_target
        hS0 hcut hV hH hDiskV hes he hboundary
      rw [← closure_jordanInterior]
      intro z hz
      rw [het]
      exact ⟨z,⟨hbound hz,fun hzg => Set.disjoint_left.mp hd (by rwa [closure_jordanInterior]) hz⟩,rfl⟩
    · exact hn
    · exfalso
      have hb : Γ0 (1 : ℂ) ∈ frontier (jordanInterior Γ0) := by
        rw [frontier_jordanInterior]
        exact ⟨1,by simp,rfl⟩
      exact (hfront hb).2 (subset_closure (hr (frontier_subset_closure hb)))
  refine ⟨Γ0,hboundary,?_,?_⟩
  · have hGammaClosure : closure (Γ '' ball (0 : ℂ) 1) =
        Γ '' closedBall (0 : ℂ) 1 := by
      rw [← Γ.image_closure, closure_ball _ one_ne_zero]
    change closure (Γ '' ball (0 : ℂ) 1) ⊆ Γ0 '' ball (0 : ℂ) 1 at hnested
    rw [hGammaClosure] at hnested
    exact hnested
  · simpa only [closure_jordanInterior] using hbound

/-- The actual origin remains inside the new retained filling because the
whole original closed disk is strictly inside it. -/
theorem quadraticRadialFillingRetainedTrace_exists_filling_with_origin
    {H : Coord → ℝ} {S S0 L : ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph Coord Coord} (Γ : ℂ ≃ₜ ℂ)
    (hS0 : 0 < S0) (hcut : S0 < S) (hL : 0 < L)
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hDiskV : quadraticRadialFillingPuncturedDisk S ⊆ V)
    (hes : e.source = quadraticRadialFillingPuncturedDisk S)
    (het : e.target = quadraticRadialFillingGlobalGradientTarget Γ L)
    (he : (e : Coord → Coord) = planarGradient H)
    (horigin : (0 : ℂ) ∈ Γ '' ball (0 : ℂ) 1) :
    ∃ Γ0 : ℂ ≃ₜ ℂ,
      range (quadraticRadialFillingGradientComplexTrace H S0) = Γ0 '' sphere (0 : ℂ) 1 ∧
      Γ '' closedBall (0 : ℂ) 1 ⊆ Γ0 '' ball (0 : ℂ) 1 ∧
      Γ0 '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) L ∧
      (0 : ℂ) ∈ Γ0 '' ball (0 : ℂ) 1 := by
  obtain ⟨Γ0,hb,hn,hL0⟩ := quadraticRadialFillingRetainedTrace_exists_filling
    Γ hS0 hcut hL hV hH hDiskV hes het he
  exact ⟨Γ0,hb,hn,hL0,hn (image_mono ball_subset_closedBall horigin)⟩

end
end TightVer401
