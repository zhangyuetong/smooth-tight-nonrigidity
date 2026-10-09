import TightVer401.DualRadialCompletionNeckInverse
import TightVer401.DualRadialCompletionGlobalInverse
import TightVer401.DualRadialCompletionNeckLegendre

/-! Actual global neck inverse and the resulting literal Legendre tail. -/
namespace TightVer401
noncomputable section
open Set Filter Function Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The proved neck bijection and actual negative Hessian construct a smooth
inverse for the same pasted potential. -/
theorem exists_dualRadialCompletionNeck_gradient_inverse
    {R M a d b S : ℝ} (hR : 0 < R) (hM : 0 < M) (ha : 0 < a)
    (had : a < d) (hdb : d < b) (hbR : b < R/2) (hRS : R/2 < S)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo a b))
    (hgpos : ∀ r ∈ Ioo a b, 0 < deriv g r)
    (hgneg : ∀ r ∈ Ioo a b, deriv (deriv g) r < 0)
    (hEscape : Tendsto (deriv g) (𝓝[>] a) atTop)
    (hgQuad : EqOn g (dualRadialQuadraticProfile R M (-M*R^2/2)) (Ioo d b))
    {F H : Coord → ℝ}
    (hFNeck : EqOn F (radialPlanarPotential g) {x | a < planarRadius x ∧ planarRadius x < b})
    (hFOld : EqOn F H {x | d < planarRadius x ∧ planarRadius x < S})
    (hHQuad : EqOn H (dualRadialQuadraticPotential R M (-M*R^2/2))
      {x | 0 < planarRadius x ∧ planarRadius x < R/2})
    (hF : ContDiffOn ℝ ∞ F {x | a < planarRadius x ∧ planarRadius x < S})
    (hneg : ∀ x, a < planarRadius x → planarRadius x < S → (planarHessian F x).det < 0)
    (Gamma : ℂ ≃ₜ ℂ) (hGamma0 : (0 : ℂ) ∈ Gamma '' closedBall (0 : ℂ) 1)
    (hGammaBound : ∀ z ∈ Gamma '' closedBall (0 : ℂ) 1, ‖z‖ < M * (R-b))
    (e : OpenPartialHomeomorph Coord Coord)
    (heSource : e.source = {x | 0 < planarRadius x ∧ planarRadius x < S})
    (heTarget : e.target = seamComplexCoord '' (ball (0 : ℂ) (M*R) \ Gamma '' closedBall (0 : ℂ) 1))
    (heGradient : ∀ x ∈ e.source, e x = planarGradient H x) :
    ∃ eN : OpenPartialHomeomorph Coord Coord,
      eN.source = {x | a < planarRadius x ∧ planarRadius x < S} ∧
      eN.target = seamComplexCoord '' (univ \ Gamma '' closedBall (0 : ℂ) 1) ∧
      (eN : Coord → Coord) = planarGradient F ∧ ContDiffOn ℝ ∞ eN.symm eN.target := by
  have hBij := dualRadialCompletionNeck_gradient_bijOn hR hM ha had hdb hbR hRS
    hg hgpos hgneg hEscape hgQuad hFNeck hFOld hHQuad Gamma hGamma0 hGammaBound
    e heSource heTarget heGradient
  have hU : IsOpen {x : Coord | a < planarRadius x ∧ planarRadius x < S} :=
    isOpen_Ioo.preimage quadraticFillerCartesianGradient_radius_continuous
  have hJ : ∀ x ∈ {x : Coord | a < planarRadius x ∧ planarRadius x < S},
      annularJacobian (planarGradient F) x ≠ 0 := by
    intro x hx
    rw [dualRadialCompletion_gradient_jacobian hF hU hx]
    exact (hneg x hx.1 hx.2).ne
  have hUnique : ∀ y ∈ planarGradient F '' {x | a < planarRadius x ∧ planarRadius x < S},
      ∃! x, x ∈ {x | a < planarRadius x ∧ planarRadius x < S} ∧ planarGradient F x = y := by
    rintro y ⟨x,hx,he⟩
    exact ⟨x, ⟨hx,he⟩, fun z hz => hBij.injOn hz.1 hx (hz.2.trans he.symm)⟩
  obtain ⟨eN,hs,ht,hforward,hi⟩ := annular_exists_smooth_image_inverse hU
    (planarGradient_contDiffOn hF hU) hJ hUnique
  exact ⟨eN,hs,ht.trans hBij.image_eq,hforward,hi⟩

private theorem tail_gradient_eq {F H : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hEq : EqOn F H U) {x : Coord} (hx : x ∈ U) :
    planarGradient F x = planarGradient H x := by
  have he : F =ᶠ[𝓝 x] H := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hEq hz
  ext i
  change fderiv ℝ F x (Pi.single i 1) = fderiv ℝ H x (Pi.single i 1)
  rw [he.fderiv_eq]

private theorem tail_complex_coord (y : Coord) : seamComplexCoord (angularDescentComplex y) = y := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply,angularDescentComplex]

private theorem tail_coord_complex (z : ℂ) : angularDescentComplex (seamComplexCoord z) = z := by
  apply Complex.ext <;> simp [seamComplexCoord_apply,angularDescentComplex]

/-- Large actual targets force their actual inverse into the literal neck
collar. Restriction of the same inverse then reuses the proved neck Legendre
formula, giving both the exact tail and its ordinary ambient germ. -/
theorem exists_dualRadialCompletionNeck_legendre_tail
    {R M a b c d S B C : ℝ} (hR : 0 < R) (hM : 0 < M) (ha : 0 < a)
    (hac : a < c) (hcb : c < b) (hdb : d < b) (hB : 0 < B)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo a b))
    (hgpos : ∀ r ∈ Ioo a b, 0 < deriv g r)
    (hgneg : ∀ r ∈ Ioo a b, deriv (deriv g) r < 0)
    {F H : Coord → ℝ}
    (hFg : EqOn F (radialPlanarPotential g) {x | a < planarRadius x ∧ planarRadius x < b})
    (hFH : EqOn F H {x | d < planarRadius x ∧ planarRadius x < S})
    (hLiteral : EqOn F (radialPlanarPotential (dualRadialNeck C B a))
      {x | a < planarRadius x ∧ planarRadius x < c})
    (Gamma : ℂ ≃ₜ ℂ)
    (hGammaBound : ∀ z ∈ Gamma '' closedBall (0 : ℂ) 1, ‖z‖ < M*R)
    (e : OpenPartialHomeomorph Coord Coord)
    (heSource : e.source = {x | 0 < planarRadius x ∧ planarRadius x < S})
    (heTarget : e.target = seamComplexCoord '' (ball (0 : ℂ) (M*R) \ Gamma '' closedBall (0 : ℂ) 1))
    (heGradient : ∀ x ∈ e.source, e x = planarGradient H x)
    (eN : OpenPartialHomeomorph Coord Coord)
    (heNSource : eN.source = {x | a < planarRadius x ∧ planarRadius x < S})
    (heNTarget : eN.target = seamComplexCoord '' (univ \ Gamma '' closedBall (0 : ℂ) 1))
    (heNGradient : (eN : Coord → Coord) = planarGradient F) :
    ∃ T : ℝ, 0 < T ∧
      (∀ y : Coord, T < planarRadius y → y ∈ eN.target ∧ planarRadius (eN.symm y) < c) ∧
      (∀ y : Coord, T < planarRadius y →
        planarLegendre F eN y = a*planarRadius y-B/planarRadius y-C) ∧
      ∀ y : Coord, T < planarRadius y →
        planarLegendre F eN =ᶠ[𝓝 y] (fun z => a*planarRadius z-B/planarRadius z-C) := by
  let c' : ℝ := (a+c)/2
  let T : ℝ := max (M*R) (deriv g c')
  have hac' : a < c' := by dsimp [c']; linarith
  have hc'c : c' < c := by dsimp [c']; linarith
  have hc'b : c' < b := hc'c.trans hcb
  have hT0 : 0 < T := (mul_pos hM hR).trans_le (le_max_left _ _)
  have hD := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hg |>.2
  have hAnti : StrictAntiOn (deriv g) (Ioo a b) :=
    strictAntiOn_of_deriv_neg (convex_Ioo a b) hD.continuousOn
      (fun r hr => hgneg r (interior_subset hr))
  have hRadialOpen (u v : ℝ) : IsOpen {x : Coord | u < planarRadius x ∧ planarRadius x < v} :=
    isOpen_Ioo.preimage quadraticFillerCartesianGradient_radius_continuous
  have hHigh (y : Coord) (hy : T < planarRadius y) :
      y ∈ eN.target ∧ planarRadius (eN.symm y) < c := by
    have hyN : y ∈ eN.target := by
      rw [heNTarget]
      refine ⟨angularDescentComplex y, ⟨mem_univ _, ?_⟩, tail_complex_coord y⟩
      intro hGamma
      have hnorm := hGammaBound _ hGamma
      rw [angularDescentComplex_norm] at hnorm
      exact (not_lt_of_gt ((le_max_left (M*R) (deriv g c')).trans_lt hy)) hnorm
    have hqN := eN.map_target hyN
    have hq : a < planarRadius (eN.symm y) ∧ planarRadius (eN.symm y) < S := by
      rwa [heNSource] at hqN
    have hforward : planarGradient F (eN.symm y) = y := by
      rw [← heNGradient]
      exact eN.right_inv hyN
    refine ⟨hyN, ?_⟩
    by_contra hnot
    have hcq : c ≤ planarRadius (eN.symm y) := le_of_not_gt hnot
    by_cases hqb : planarRadius (eN.symm y) < b
    · have hgrad := tail_gradient_eq (hRadialOpen a b) hFg ⟨hq.1,hqb⟩
      have hqRadial : eN.symm y ∈ radialPlanarDomain (Ioo a b) :=
        ⟨Real.sqrt_pos.mp (ha.trans hq.1),hq.1,hqb⟩
      have hRadius : planarRadius y = deriv g (planarRadius (eN.symm y)) := by
        calc
          planarRadius y = planarRadius (planarGradient F (eN.symm y)) :=
            congrArg planarRadius hforward.symm
          _ = planarRadius (planarGradient (radialPlanarPotential g) (eN.symm y)) :=
            congrArg planarRadius hgrad
          _ = deriv g (planarRadius (eN.symm y)) := by
            rw [radialPlanarGradient_radius hg isOpen_Ioo hqRadial,
              abs_of_pos (hgpos _ ⟨hq.1,hqb⟩)]
      have hslope := hAnti ⟨hac',hc'b⟩ ⟨hq.1,hqb⟩ (hc'c.trans_le hcq)
      have hlow : planarRadius y < T := by
        rw [hRadius]
        exact hslope.trans_le (le_max_right _ _)
      exact (not_lt_of_gt hy) hlow
    · have hgrad := tail_gradient_eq (hRadialOpen d S) hFH
        ⟨hdb.trans_le (le_of_not_gt hqb),hq.2⟩
      have hqE : eN.symm y ∈ e.source := by rw [heSource]; exact ⟨ha.trans hq.1,hq.2⟩
      have hOld := e.map_source hqE
      rw [heTarget] at hOld
      obtain ⟨z, hz, hzy⟩ := hOld
      have hRadius : planarRadius y < M*R := by
        rw [← hforward,hgrad,← heGradient _ hqE,← hzy,← angularDescentComplex_norm,tail_coord_complex]
        simpa only [mem_ball,dist_zero_right] using hz.1
      exact (not_lt_of_gt hy) (hRadius.trans_le (le_max_left _ _))
  let V := radialPlanarDomain (Ioo a c)
  have hV : IsOpen V := radialPlanarDomain_isOpen isOpen_Ioo
  let eC := eN.restrOpen V hV
  have hSourceC : eC.source ⊆ radialPlanarDomain (Ioo a c) := fun _ hx => hx.2
  have hLiteralV : EqOn F (radialPlanarPotential (dualRadialNeck C B a)) V := fun _ hx => hLiteral hx.2
  have hGradientC : ∀ x ∈ eC.source, eC x =
      planarGradient (radialPlanarPotential (dualRadialNeck C B a)) x := by
    intro x hx
    change eN x = _
    rw [heNGradient]
    exact tail_gradient_eq hV hLiteralV hx.2
  have hNeckSmooth : ContDiffOn ℝ ∞ (dualRadialNeck C B a) (Ioo a c) :=
    (dualRadialNeck_contDiffOn C a hB).mono (fun _ hr => hr.1)
  have hTail (y : Coord) (hy : T < planarRadius y) :
      planarLegendre F eN y = a*planarRadius y-B/planarRadius y-C := by
    obtain ⟨hyN,hqc⟩ := hHigh y hy
    have hqN := eN.map_target hyN
    have hq : a < planarRadius (eN.symm y) ∧ planarRadius (eN.symm y) < c := by
      rw [heNSource] at hqN
      exact ⟨hqN.1,hqc⟩
    have hqV : eN.symm y ∈ V := ⟨Real.sqrt_pos.mp (ha.trans hq.1),hq⟩
    have hyC : y ∈ eC.target := ⟨hyN,hqV⟩
    have hDual := dualRadialCompletionNeckLegendre_eqOn ha hB hac hNeckSmooth
      (fun _ _ => rfl) eC hSourceC hGradientC hyC
    have hValue : F (eN.symm y) = radialPlanarPotential (dualRadialNeck C B a) (eN.symm y) := hLiteral hq
    have hSame : planarLegendre F eN y =
        planarLegendre (radialPlanarPotential (dualRadialNeck C B a)) eC y := by
      unfold planarLegendre
      change eN.symm y ⬝ᵥ y-F (eN.symm y) =
        eN.symm y ⬝ᵥ y-radialPlanarPotential (dualRadialNeck C B a) (eN.symm y)
      rw [hValue]
    exact hSame.trans hDual
  refine ⟨T,hT0,hHigh,hTail,?_⟩
  intro y hy
  have hOpen : IsOpen {z : Coord | T < planarRadius z} :=
    isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  filter_upwards [hOpen.mem_nhds hy] with z hz
  exact hTail z hz

end
end TightVer401
