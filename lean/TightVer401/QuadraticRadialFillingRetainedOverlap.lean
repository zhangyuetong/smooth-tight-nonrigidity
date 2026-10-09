import TightVer401.QuadraticRadialFillingGlobalContract
import TightVer401.QuadraticRadialFillingExteriorCollar
import TightVer401.QuadraticRadialFillingBoundaryGerms

/-! Actual retained open overlap strictly inside the returned inverse
source. The boundary-S circle is not treated as an interior circle. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The ordinary full radial collar of a cut strictly inside the source. -/
def quadraticRadialFillingRetainedCollar (S0 δ : ℝ) : Set Coord :=
  {x | |planarRadius x-S0| < δ}

theorem quadraticRadialFillingRetainedCollar_isOpen (S0 δ : ℝ) :
    IsOpen (quadraticRadialFillingRetainedCollar S0 δ) :=
  isOpen_lt (quadraticRadialFillingRadius_continuous.sub continuous_const).abs continuous_const

/-- Every point of the retained cut circle lies in its full open collar. -/
theorem quadraticRadialFillingRetainedCollar_polar
    {S0 δ : ℝ} (hS0 : 0 < S0) (hδ : 0 < δ) (θ : ℝ) :
    saddlePolarChart ![S0,θ] ∈ quadraticRadialFillingRetainedCollar S0 δ := by
  change |planarRadius (saddlePolarChart ![S0,θ])-S0| < δ
  rw [angularDescent_radius_polar (show (0:ℝ) < (![S0,θ] : Coord) 0 from hS0)]
  change |S0 - S0| < δ
  simpa only [sub_self, abs_zero] using hδ
/-- Actual scalar germs on a full circle yield one retained open collar
strictly inside the outer cut. Its domain inclusions are ordinary geometry. -/
theorem quadraticRadialFilling_exists_retained_overlap
    {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    {H F : Coord → ℝ} {U D : Set Coord} (hU : IsOpen U) (hD : IsOpen D)
    (hCircleU : quadraticRadialFillingRadiusLevel S ⊆ U)
    (hCircleD : quadraticRadialFillingRadiusLevel S ⊆ D)
    (hOuter : ∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F) :
    ∃ S0 δ : ℝ, R < S0 ∧ S0 < S ∧ 0 < δ ∧
      IsOpen (quadraticRadialFillingRetainedCollar S0 δ) ∧
      quadraticRadialFillingRetainedCollar S0 δ ⊆ (U ∩ D) ∩ quadraticRadialFillingPuncturedDisk S ∧
      EqOn H F (quadraticRadialFillingRetainedCollar S0 δ) ∧
      (∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F) ∧
      EqOn (planarGradient H) (planarGradient F) (quadraticRadialFillingRetainedCollar S0 δ) := by
  have hS : 0 < S := hR.trans hRS
  let E : Set Coord := interior {x : Coord | H x = F x}
  let W : Set Coord := (U ∩ D) ∩ E
  have hW : IsOpen W := (hU.inter hD).inter isOpen_interior
  have hCircleW : quadraticRadialFillingRadiusLevel S ⊆ W := by
    intro x hx
    refine ⟨⟨hCircleU hx,hCircleD hx⟩,?_⟩
    obtain ⟨θ,hθ⟩ := quadraticRadialFilling_radiusLevel_exists_polar hS hx
    apply mem_interior_iff_mem_nhds.mpr
    change H =ᶠ[𝓝 x] F
    rw [← hθ]
    exact hOuter θ
  obtain ⟨ε,hε,_hεS,hCollar⟩ := quadraticRadialFilling_exists_radial_collar hS hW hCircleW
  let κ := min ε ((S-R)/2)
  let S0 := S-κ/2
  let δ := κ/4
  have hκ : 0 < κ := lt_min hε (half_pos (sub_pos.mpr hRS))
  have hκε : κ ≤ ε := min_le_left _ _
  have hκGap : κ ≤ (S-R)/2 := min_le_right _ _
  have hRS0 : R < S0 := by dsimp [S0]; linarith
  have hS0S : S0 < S := by dsimp [S0]; linarith
  have hδ : 0 < δ := div_pos hκ (by norm_num)
  have hData : ∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ,
      x ∈ W ∧ x ∈ quadraticRadialFillingPuncturedDisk S := by
    intro x hx
    change |planarRadius x-S0| < δ at hx
    obtain ⟨hl,hu⟩ := abs_lt.mp hx
    have hxr : R < planarRadius x := by dsimp [S0,δ] at hl hu; linarith
    have hxs : planarRadius x < S := by dsimp [S0,δ] at hl hu; linarith
    have hxε : |planarRadius x-S| < ε := by
      apply abs_lt.mpr
      constructor
      · dsimp [S0,δ] at hl hu
        linarith
      · linarith
    exact ⟨hCollar x hxε,⟨hR.trans hxr,hxs⟩⟩
  have hGerm : ∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F := by
    intro x hx
    filter_upwards [hW.mem_nhds (hData x hx).1] with y hy
    have hyE := hy.2
    change y ∈ interior {z : Coord | H z = F z} at hyE
    have hyEq : y ∈ {z : Coord | H z = F z} := interior_subset hyE
    exact hyEq
  refine ⟨S0,δ,hRS0,hS0S,hδ,quadraticRadialFillingRetainedCollar_isOpen S0 δ,?_,?_,hGerm,?_⟩
  · intro x hx
    exact ⟨(hData x hx).1.1,(hData x hx).2⟩
  · intro x hx
    exact (hGerm x hx).eq_of_nhds
  · intro x hx
    exact quadraticRadialFilling_gradient_eq_of_germ (hGerm x hx)

/-- The existing actual boundary-data output supplies both circle-domain
inclusions through its literal analytic domain definition. -/
theorem quadraticRadialFilling_exists_retained_overlap_of_boundary_data
    {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    {H F : Coord → ℝ} {U : Set Coord} (hU : IsOpen U)
    (hBand : quadraticRadialFillingClosedAnnulus (R/4) S ⊆ quadraticRadialFillingDomain R U)
    (hOuter : ∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F) :
    ∃ S0 δ : ℝ, R < S0 ∧ S0 < S ∧ 0 < δ ∧
      IsOpen (quadraticRadialFillingRetainedCollar S0 δ) ∧
      quadraticRadialFillingRetainedCollar S0 δ ⊆
        (U ∩ quadraticRadialFillingDomain R U) ∩ quadraticRadialFillingPuncturedDisk S ∧
      EqOn H F (quadraticRadialFillingRetainedCollar S0 δ) ∧
      (∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F) ∧
      EqOn (planarGradient H) (planarGradient F) (quadraticRadialFillingRetainedCollar S0 δ) := by
  have hD : IsOpen (quadraticRadialFillingDomain R U) :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
      ((isOpen_lt quadraticRadialFillingRadius_continuous continuous_const).union hU)
  have hCircleD : quadraticRadialFillingRadiusLevel S ⊆ quadraticRadialFillingDomain R U := by
    intro x hx
    apply hBand
    change planarRadius x = S at hx
    change R/4 ≤ planarRadius x ∧ planarRadius x ≤ S
    rw [hx]
    exact ⟨by linarith,le_rfl⟩
  have hCircleU : quadraticRadialFillingRadiusLevel S ⊆ U := by
    intro x hx
    rcases (hCircleD hx).2 with hInner | hU
    · change planarRadius x < R at hInner
      change planarRadius x = S at hx
      rw [hx] at hInner
      exact False.elim (lt_asymm hRS hInner)
    · exact hU
  exact quadraticRadialFilling_exists_retained_overlap hR hRS hU hD hCircleU hCircleD hOuter

/-- For the SAME actual returned inverse, the retained cut's collar lies
inside its actual open source and its map equals the incoming gradient. -/
theorem quadraticRadialFilling_exists_retained_inverse_overlap
    {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    {H F : Coord → ℝ} {U : Set Coord} (hU : IsOpen U)
    (hBand : quadraticRadialFillingClosedAnnulus (R/4) S ⊆ quadraticRadialFillingDomain R U)
    (hOuter : ∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F)
    (e : OpenPartialHomeomorph Coord Coord)
    (hSource : e.source = quadraticRadialFillingPuncturedDisk S)
    (he : (e : Coord → Coord) = planarGradient H) :
    ∃ S0 δ : ℝ, R < S0 ∧ S0 < S ∧ 0 < δ ∧
      IsOpen (quadraticRadialFillingRetainedCollar S0 δ) ∧
      quadraticRadialFillingRetainedCollar S0 δ ⊆
        (U ∩ quadraticRadialFillingDomain R U) ∩ e.source ∧
      EqOn H F (quadraticRadialFillingRetainedCollar S0 δ) ∧
      (∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F) ∧
      EqOn (e : Coord → Coord) (planarGradient F) (quadraticRadialFillingRetainedCollar S0 δ) := by
  obtain ⟨S0,δ,hRS0,hS0S,hδ,hOpen,hSubset,hEq,hGerm,hGrad⟩ :=
    quadraticRadialFilling_exists_retained_overlap_of_boundary_data hR hRS hU hBand hOuter
  refine ⟨S0,δ,hRS0,hS0S,hδ,hOpen,?_,hEq,hGerm,?_⟩
  · rwa [hSource]
  · rw [he]
    exact hGrad

/-- Ordinary analytic smoothness restricts to the derived actual overlap,
without asserting smoothness across the excluded outer boundary. -/
theorem quadraticRadialFillingRetainedCollar_contDiffOn
    {S0 δ : ℝ} {H F : Coord → ℝ} {U D : Set Coord}
    (hH : ContDiffOn ℝ ∞ H D) (hF : ContDiffOn ℝ ∞ F U)
    (hSubset : quadraticRadialFillingRetainedCollar S0 δ ⊆ U ∩ D) :
    ContDiffOn ℝ ∞ H (quadraticRadialFillingRetainedCollar S0 δ) ∧
      ContDiffOn ℝ ∞ F (quadraticRadialFillingRetainedCollar S0 δ) :=
  ⟨hH.mono (fun x hx => (hSubset hx).2),hF.mono (fun x hx => (hSubset hx).1)⟩

end
end TightVer401
