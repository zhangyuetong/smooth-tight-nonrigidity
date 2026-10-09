import TightVer401.RelativeSaddleSmoothing
import TightVer401.QuadraticRadialFillingCircle
import TightVer401.DualRadialQuadraticGerm

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def quadraticRadialFillingDomain (R : ℝ) (U : Set Coord) : Set Coord :=
  {x | 0 < planarRadius x} ∩ ({x | planarRadius x < R} ∪ U)

/-- Apply actual relative smoothing to the incoming exterior and an actual
Cartesian filler, keeping both the exterior and strict inner radial germs.
All hypotheses here concern ordinary functions on their open domains. -/
theorem quadraticRadialFilling_glue {R M : ℝ} (hR : 0 < R)
    {F A : Coord → ℝ} {U Uf N : Set Coord}
    (hU : IsOpen U) (hUf : IsOpen Uf) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hDiskUf : ∀ x : Coord, 0 < planarRadius x → planarRadius x ≤ R → x ∈ Uf)
    (hF : ContDiffOn ℝ ∞ F U) (hA : ContDiffOn ℝ ∞ A Uf)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hnegA : ∀ x ∈ Uf, (planarHessian A x).det < 0)
    (hValue : ∀ θ : ℝ, A (saddlePolarChart ![R,θ]) = F (saddlePolarChart ![R,θ]))
    (hGradient : ∀ θ : ℝ, planarGradient A (saddlePolarChart ![R,θ]) =
      planarGradient F (saddlePolarChart ![R,θ]))
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x ≤ R/2 →
      A x = dualRadialQuadraticPotential R M (-M*R^2/2) x)
    {η : ℝ} (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      ∀ x ∈ quadraticRadialFillingDomain R U,
        |H x - relativeSaddlePiecewise {y | planarRadius y < R} A F x| < η ∧
        ‖planarGradient H x -
          planarGradient (relativeSaddlePiecewise {y | planarRadius y < R} A F) x‖ < η := by
  classical
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let P : Set Coord := {x | planarRadius x < R}
  let V := quadraticRadialFillingDomain R U
  let N' : Set Coord := N ∩ {x | R/2 < planarRadius x}
  have hP : IsOpen P := isOpen_lt quadraticRadialFillingRadius_continuous continuous_const
  have hV : IsOpen V :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter (hP.union hU)
  have hN' : IsOpen N' := hN.inter
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous)
  have hSeamRadius {x : Coord}
      (hx : x ∈ seamNormalSeam (quadraticRadialFillingCircle R)
        (quadraticRadialFillingCircle_periodic R)) : planarRadius x = R := by
    simpa only [quadraticRadialFillingCircle_seam hR, mem_setOf_eq] using hx
  have hSeamPolar {x : Coord}
      (hx : x ∈ seamNormalSeam (quadraticRadialFillingCircle R)
        (quadraticRadialFillingCircle_periodic R)) :
      ∃ θ : ℝ, saddlePolarChart ![R,θ] = x := by
    obtain ⟨q,hq⟩ := hx
    obtain ⟨θ,rfl⟩ := QuotientAddGroup.mk_surjective q
    change seamNormalNative (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) (periodProjection (2 * Real.pi) θ,0) = x at hq
    refine ⟨θ, ?_⟩
    simpa only [seamNormalNative_coe, seamNormalCoordinates_central,
      quadraticRadialFillingCircle_coord] using hq
  have hSeamU : seamNormalSeam (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) ⊆ U := by
    intro x hx
    obtain ⟨θ,rfl⟩ := hSeamPolar hx
    exact hCircleU θ
  have hSeamV : seamNormalSeam (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) ⊆ V :=
    fun x hx => ⟨by change 0 < planarRadius x; rw [hSeamRadius hx]; exact hR,
      Or.inr (hSeamU hx)⟩
  have hSeamUf : seamNormalSeam (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) ⊆ Uf := by
    intro x hx
    apply hDiskUf x
    · rw [hSeamRadius hx]; exact hR
    · rw [hSeamRadius hx]
  have hSeamN' : seamNormalSeam (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) ⊆ N' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · obtain ⟨θ,rfl⟩ := hSeamPolar hx
      exact hCircleN θ
    · change R/2 < planarRadius x
      rw [hSeamRadius hx]
      linarith
  have hPositive : V ∩ interior P ⊆ Uf := by
    intro x hx
    have hp : x ∈ P := interior_subset hx.2
    exact hDiskUf x hx.1.1 (show planarRadius x ≤ R from le_of_lt hp)
  have hNegative : V ∩ interior Pᶜ ⊆ U := by
    intro x hx
    rcases hx.1.2 with hin | hout
    · exact False.elim ((interior_subset hx.2) hin)
    · exact hout
  obtain ⟨H,hH,hNeg,hOld,hPos,hExt,hClose⟩ := exists_relative_saddle_smoothing_on_sides
    (quadraticRadialFillingCircle_contDiff R) (quadraticRadialFillingCircle_periodic R)
    (quadraticRadialFillingCircle_regular hR) (quadraticRadialFillingCircle_lift_injective hR)
    hV hN' hUf hU hSeamV hSeamN' hSeamUf hSeamU
    (fun x hx => quadraticRadialFillingCircle_frontier hR hx.2) hPositive hNegative
    (show (0:ℝ) < 1/2 by norm_num)
    (fun s t ht _ _ => quadraticRadialFillingCircle_normal_side hR s t ht)
    hA hF (fun θ => by rw [quadraticRadialFillingCircle_coord]; exact hValue θ)
    (fun θ => by rw [quadraticRadialFillingCircle_coord]; exact hGradient θ) hnegA hnegF hη
  refine ⟨H,hH,hNeg,?_,?_,hClose⟩
  · intro x hx hr hn
    apply hExt x
    refine ⟨⟨⟨lt_trans hR hr,Or.inr hx⟩,fun h => hn h.1⟩, ?_⟩
    have hg : x ∈ {y : Coord | R < planarRadius y} := hr
    have hsub : {y : Coord | R < planarRadius y} ⊆ Pᶜ := by
      intro y hy
      change ¬ planarRadius y < R
      exact not_lt.mpr (show R ≤ planarRadius y from le_of_lt hy)
    have ho : IsOpen {y : Coord | R < planarRadius y} :=
      isOpen_lt continuous_const quadraticRadialFillingRadius_continuous
    exact interior_mono hsub (ho.interior_eq.symm ▸ hg)
  · intro x hx hr
    have hxp : x ∈ P := lt_trans hr (by linarith)
    have hOldA : H =ᶠ[𝓝 x] A := hPos x
      ⟨⟨⟨hx,Or.inl hxp⟩,fun h => (not_lt.mpr hr.le) h.2⟩, hP.interior_eq.symm ▸ hxp⟩
    have hband : {y : Coord | 0 < planarRadius y ∧ planarRadius y < R/2} ∈ 𝓝 x :=
      ((isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
        (isOpen_lt quadraticRadialFillingRadius_continuous continuous_const)).mem_nhds ⟨hx,hr⟩
    exact hOldA.trans ((show ∀ᶠ y in 𝓝 x,
      0 < planarRadius y ∧ planarRadius y < R/2 from hband).mono
        fun y hy => hInner y hy.1 hy.2.le)

end
end TightVer401
