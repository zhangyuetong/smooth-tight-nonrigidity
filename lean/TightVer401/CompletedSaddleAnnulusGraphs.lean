import TightVer401.CompletedSaddleAnnulusActualHeight
import TightVer401.RevolutionEndCalculus

/-! Actual upper support graph and its reflection, for the same completed
potential and actual gradient inverse. Boundary parametrization is separate. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusUpperGraph (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ) (y : Coord) : Ambient :=
  WithLp.toLp 2 ![-y 0, -y 1, dInfinity - completedSaddleAnnulusGraphHeight G e y]

def completedSaddleAnnulusLowerGraph (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ) (y : Coord) : Ambient :=
  WithLp.toLp 2 ![-y 0, -y 1, completedSaddleAnnulusGraphHeight G e y - dInfinity]

theorem completedSaddleAnnulusUpperGraph_support {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (dInfinity : ℝ) {y : Coord} (hy : y ∈ e.target) :
    completedSaddleAnnulusUpperGraph G e dInfinity y =
      -planarSupportMap G (e.symm y) + dInfinity • revolutionAxis := by
  have hg : planarGradient G (e.symm y) = y :=
    (heG _ (e.map_target hy)).symm.trans (e.right_inv hy)
  have h0 : coordPartial 0 G (e.symm y) = y 0 := congrFun hg 0
  have h1 : coordPartial 1 G (e.symm y) = y 1 := congrFun hg 1
  rw [completedSaddleAnnulusUpperGraph, completedSaddleAnnulusGraphHeight_support e heG hy]
  ext i
  fin_cases i <;> simp [planarSupportMap, revolutionAxis, h0, h1] <;> ring

theorem completedSaddleAnnulusUpperGraph_injective (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ) :
    Function.Injective (completedSaddleAnnulusUpperGraph G e dInfinity) := by
  intro x y h
  have h0 := congrArg (fun z : Ambient => z 0) h
  have h1 := congrArg (fun z : Ambient => z 1) h
  change -x 0 = -y 0 at h0
  change -x 1 = -y 1 at h1
  ext i
  fin_cases i
  · exact neg_injective h0
  · exact neg_injective h1

theorem completedSaddleAnnulusLowerGraph_injective (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ) :
    Function.Injective (completedSaddleAnnulusLowerGraph G e dInfinity) := by
  intro x y h
  have h0 := congrArg (fun z : Ambient => z 0) h
  have h1 := congrArg (fun z : Ambient => z 1) h
  change -x 0 = -y 0 at h0
  change -x 1 = -y 1 at h1
  ext i
  fin_cases i
  · exact neg_injective h0
  · exact neg_injective h1

theorem completedSaddleAnnulusGraphs_contDiffOn {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (completedSaddleAnnulusUpperGraph G e dInfinity) e.target ∧
    ContDiffOn ℝ ∞ (completedSaddleAnnulusLowerGraph G e dInfinity) e.target := by
  have hz := completedSaddleAnnulusGraphHeight_contDiffOn e hG hi
  have h0 : ContDiffOn ℝ ∞ (fun y : Coord => -y 0) e.target :=
    (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffOn.neg
  have h1 : ContDiffOn ℝ ∞ (fun y : Coord => -y 1) e.target :=
    (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffOn.neg
  constructor
  · apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact contDiffOn_const.sub hz
  · apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact hz.sub contDiffOn_const

theorem completedSaddleAnnulusGraphs_separated_of_scalar_germs
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ B ε L d0 dInfinity : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
    (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity) :
    (∀ y ∈ e.target,
      0 < completedSaddleAnnulusUpperGraph G e dInfinity y 2 ∧
      completedSaddleAnnulusUpperGraph G e dInfinity y 2 < dInfinity - d0 ∧
      -(dInfinity - d0) < completedSaddleAnnulusLowerGraph G e dInfinity y 2 ∧
      completedSaddleAnnulusLowerGraph G e dInfinity y 2 < 0) ∧
    Disjoint (completedSaddleAnnulusUpperGraph G e dInfinity '' e.target)
      (completedSaddleAnnulusLowerGraph G e dInfinity '' e.target) := by
  have h := completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity
  have hb : ∀ y ∈ e.target,
      0 < completedSaddleAnnulusUpperGraph G e dInfinity y 2 ∧
      completedSaddleAnnulusUpperGraph G e dInfinity y 2 < dInfinity - d0 ∧
      -(dInfinity - d0) < completedSaddleAnnulusLowerGraph G e dInfinity y 2 ∧
      completedSaddleAnnulusLowerGraph G e dInfinity y 2 < 0 := by
    intro y hy
    have hyA : y ∈ quadraticRadialFillingOpenAnnulus A RN := by rwa [hTarget] at hy
    have hz := h.2.2.2.1 y hyA
    rw [completedSaddleAnnulusHeightResolved_eq_interior hyA] at hz
    change 0 < dInfinity - completedSaddleAnnulusGraphHeight G e y ∧
      dInfinity - completedSaddleAnnulusGraphHeight G e y < dInfinity - d0 ∧
      -(dInfinity - d0) < completedSaddleAnnulusGraphHeight G e y - dInfinity ∧
      completedSaddleAnnulusGraphHeight G e y - dInfinity < 0
    exact ⟨by linarith [hz.2], by linarith [hz.1], by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨hb, Set.disjoint_left.mpr ?_⟩
  intro z hzU hzL
  obtain ⟨y, hy, rfl⟩ := hzU
  obtain ⟨x, hx, he⟩ := hzL
  have he2 := congrArg (fun z : Ambient => z 2) he
  have hpos := (hb y hy).1
  have hneg := (hb x hx).2.2.2
  linarith

private theorem completedSaddleAnnulusGraph_differential_injective
    {F : Coord → Ambient} {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hHorizontal : ∀ y ∈ U, ∀ i : Fin 2, F y i.castSucc = -y i)
    {y : Coord} (hy : y ∈ U) : Function.Injective (fderiv ℝ F y) := by
  have hd := ((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hproj (i : Fin 2) :
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i.castSucc).comp (fderiv ℝ F y) =
        -(ContinuousLinearMap.proj (R := ℝ) i : Coord →L[ℝ] ℝ) := by
    have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i.castSucc).hasFDerivAt.comp
      y hd.hasFDerivAt
    have he : (fun x => F x i.castSucc) =ᶠ[𝓝 y] (fun x => -x i) := by
      filter_upwards [hU.mem_nhds hy] with x hx
      exact hHorizontal x hx i
    have hn := ((ContinuousLinearMap.proj (R := ℝ) i : Coord →L[ℝ] ℝ).hasFDerivAt (x := y)).neg
    exact hc.unique (hn.congr_of_eventuallyEq he)
  intro v w hvw
  ext i
  have h := congrArg (fun z : Ambient => z i.castSucc) hvw
  have hv := congrArg (fun d : Coord →L[ℝ] ℝ => d v) (hproj i)
  have hw := congrArg (fun d : Coord →L[ℝ] ℝ => d w) (hproj i)
  change fderiv ℝ F y v i.castSucc = -v i at hv
  change fderiv ℝ F y w i.castSucc = -w i at hw
  rw [hv, hw] at h
  exact neg_injective h

theorem completedSaddleAnnulusGraphs_differential_injective {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {y : Coord} (hy : y ∈ e.target) :
    Function.Injective (fderiv ℝ (completedSaddleAnnulusUpperGraph G e dInfinity) y) ∧
    Function.Injective (fderiv ℝ (completedSaddleAnnulusLowerGraph G e dInfinity) y) := by
  have h := completedSaddleAnnulusGraphs_contDiffOn e dInfinity hG hi
  constructor
  · apply completedSaddleAnnulusGraph_differential_injective e.open_target h.1 _ hy
    intro x hx i
    fin_cases i <;> rfl
  · apply completedSaddleAnnulusGraph_differential_injective e.open_target h.2 _ hy
    intro x hx i
    fin_cases i <;> rfl

end
end TightVer401
