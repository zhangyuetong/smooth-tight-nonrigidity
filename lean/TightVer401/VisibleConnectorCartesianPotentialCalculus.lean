import TightVer401.VisibleConnectorCartesianDescent
import TightVer401.VisibleConnectorRuledHessian

/-! Actual raw Cartesian connector potential through its supplied actual source
inverse. Local ruled potentials identify its derivative germs; the existing
ruled Hessian theorem then gives strict saddle neighborhoods of the closed strip.
No incoming retained potential germ or completed connector is asserted. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar descended through the actual raw Cartesian source inverse. -/
def visibleConnectorCartesianPotential (L : ℝ) (g : ℝ → ℝ)
    (gamma w : ℝ → Coord) (h : ℝ → ℝ) (E : OpenPartialHomeomorph Coord Coord) : Coord → ℝ :=
  visibleConnectorCartesianHeight L g gamma w h ∘ E.symm

/-- Radius corresponding to the physical transverse ruling coordinate. -/
def visibleConnectorCartesianPotentialRadius (h : ℝ → ℝ) (q : Coord) : ℝ :=
  1 + q 1 / h (q 0)

/-- Actual round Cartesian input representing the local physical coordinates. -/
def visibleConnectorCartesianPotentialPhysicalChart (L : ℝ) (h : ℝ → ℝ)
    (q : Coord) : Coord :=
  saddlePolarChart ![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L]

/-- An actual open physical neighborhood selected by source membership and
strict source determinant; it includes the closed strip under the ordinary signs. -/
def visibleConnectorCartesianPotentialRuledDomain (L : ℝ) (p gamma w : ℝ → Coord)
    (h : ℝ → ℝ) (E : OpenPartialHomeomorph Coord Coord) : Set Coord :=
  {q | 0 < visibleConnectorCartesianPotentialRadius h q ∧
    visibleConnectorCartesianPotentialPhysicalChart L h q ∈ E.source ∧
    0 < visibleConnectorDelta p gamma w q}

private theorem cartesianPotential_radius_smooth {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hpos : ∀ s, 0 < h s) :
    ContDiff ℝ ∞ (visibleConnectorCartesianPotentialRadius h) :=
  contDiff_const.add ((contDiff_apply ℝ ℝ 1).div
    (hh.comp (contDiff_apply ℝ ℝ 0)) (fun q => (hpos (q 0)).ne'))

theorem visibleConnectorCartesianPotentialPhysicalChart_contDiff {L : ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hpos : ∀ s, 0 < h s) :
    ContDiff ℝ ∞ (visibleConnectorCartesianPotentialPhysicalChart L h) := by
  have hc : ContDiff ℝ ∞ (fun q : Coord =>
      (![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact cartesianPotential_radius_smooth hh hpos
    · exact (contDiff_const.mul (contDiff_apply ℝ ℝ 0)).div_const L
  exact saddlePolarChart_contDiff.comp hc

private theorem cartesianPotential_physical_clock {L : ℝ} (hL : 0 < L) (s : ℝ) :
    visibleConnectorPhysicalParameter L (2*Real.pi*s/L) = s := by
  unfold visibleConnectorPhysicalParameter
  field_simp [hL.ne', Real.two_pi_pos.ne']

/-- Exact physical pullbacks of both actual descended Cartesian functions. -/
theorem visibleConnectorCartesianPotential_physical_pullbacks
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
    {q : Coord} (hq : 0 < visibleConnectorCartesianPotentialRadius h q) :
    visibleConnectorCartesianSource L p w h (visibleConnectorCartesianPotentialPhysicalChart L h q) =
        visibleConnectorSource p w q ∧
      visibleConnectorCartesianHeight L g gamma w h (visibleConnectorCartesianPotentialPhysicalChart L h q) =
        visibleConnectorHeight g gamma w q := by
  have hr : 0 < (![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L] : Coord) 0 := hq
  have hu : (visibleConnectorCartesianPotentialRadius h q - 1)*h (q 0) = q 1 := by
    simp [visibleConnectorCartesianPotentialRadius, (hpos (q 0)).ne']
  constructor
  · unfold visibleConnectorCartesianPotentialPhysicalChart
    rw [visibleConnectorCartesianSource_polar hpL hwL hhL hr]
    simp only [visibleConnectorPolarSource, Matrix.cons_val_zero, Matrix.cons_val_one,
      cartesianPotential_physical_clock hL, hu, visibleConnectorSource]
  · unfold visibleConnectorCartesianPotentialPhysicalChart
    rw [visibleConnectorCartesianHeight_polar hgL hgammaL hwL hhL hr]
    simp only [visibleConnectorPolarHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      cartesianPotential_physical_clock hL, hu, visibleConnectorHeight]

section ActualInverse
variable {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
variable (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
variable (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
variable (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
variable (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
variable (E : OpenPartialHomeomorph Coord Coord)
variable (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L p w h)
variable (hEs : E.source ⊆ {z : Coord | 0 < planarRadius z})
variable (hi : ContDiffOn ℝ ∞ E.symm E.target)

include hL hp hgamma hw hg hh hpL hgammaL hwL hgL hhL E hEs hi in
/-- Smoothness of the explicit SAME scalar, obtained by composing the actual inverse. -/
theorem visibleConnectorCartesianPotential_contDiffOn :
    ContDiffOn ℝ ∞ (visibleConnectorCartesianPotential L g gamma w h E) E.target := by
  have hH := (visibleConnector_cartesian_descent hL hp hgamma hw hg hh
    hpL hgammaL hwL hgL hhL).2.1
  exact hH.comp hi (fun y hy => hEs (E.map_target hy))

include hL hpL hgammaL hwL hgL hhL hpos E hE in
/-- Literal ruled scalar pullback, derived from the actual source inverse. -/
theorem visibleConnectorCartesianPotential_height_eqOn {V : Set Coord}
    (hpsi : MapsTo (visibleConnectorCartesianPotentialPhysicalChart L h) V E.source)
    (hr : ∀ q ∈ V, 0 < visibleConnectorCartesianPotentialRadius h q) :
    EqOn (visibleConnectorCartesianPotential L g gamma w h E ∘ visibleConnectorSource p w)
      (visibleConnectorHeight g gamma w) V := by
  intro q hq
  obtain ⟨hSource,hHeight⟩ := visibleConnectorCartesianPotential_physical_pullbacks
    hL hpL hgammaL hwL hgL hhL hpos (hr q hq)
  have heq : E (visibleConnectorCartesianPotentialPhysicalChart L h q) =
      visibleConnectorSource p w q := by rw [hE]; exact hSource
  change visibleConnectorCartesianHeight L g gamma w h (E.symm (visibleConnectorSource p w q)) = _
  rw [← heq, E.left_inv (hpsi hq)]
  exact hHeight

include hp hgamma hw hg in
private theorem cartesianPotential_gradient_of_pullback {F : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hrec : EqOn (F ∘ visibleConnectorSource p w) (visibleConnectorHeight g gamma w) V)
    {q : Coord} (hq : q ∈ V) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    planarGradient F (visibleConnectorSource p w q) = visibleConnectorGradient p gamma w q := by
  obtain ⟨eLocal,FLocal,hqLocal,heLocal,_hiLocal,_hFLocal,hrecLocal,hgradLocal⟩ :=
    visibleConnector_exists_local_potential hg hp hgamma hw hvalue q hDelta
  have hyLocal : visibleConnectorSource p w q ∈ eLocal.target := by
    rw [← heLocal]
    exact eLocal.map_source hqLocal
  have hqInv : eLocal.symm (visibleConnectorSource p w q) = q := by
    rw [← heLocal]
    exact eLocal.left_inv hqLocal
  have hnear : ∀ᶠ y in 𝓝 (visibleConnectorSource p w q), eLocal.symm y ∈ V := by
    apply (eLocal.continuousAt_symm hyLocal).eventually
    rw [hqInv]
    exact hV.mem_nhds hq
  have heq : F =ᶠ[𝓝 (visibleConnectorSource p w q)] FLocal := by
    filter_upwards [eLocal.open_target.mem_nhds hyLocal, hnear] with y hy hrV
    have hrLocal : eLocal.symm y ∈ eLocal.source := eLocal.map_target hy
    have hsy : visibleConnectorSource p w (eLocal.symm y) = y := by
      rw [← heLocal]
      exact eLocal.right_inv hy
    calc
      F y = F (visibleConnectorSource p w (eLocal.symm y)) := congrArg F hsy.symm
      _ = visibleConnectorHeight g gamma w (eLocal.symm y) := hrec hrV
      _ = FLocal (visibleConnectorSource p w (eLocal.symm y)) := (hrecLocal hrLocal).symm
      _ = FLocal y := congrArg FLocal hsy
  have hgrad : planarGradient F (visibleConnectorSource p w q) =
      planarGradient FLocal (visibleConnectorSource p w q) := by
    ext i
    unfold planarGradient coordPartial
    rw [heq.fderiv_eq]
  exact hgrad.trans (hgradLocal hqLocal)

include hL hp hgamma hw hg hpL hgammaL hwL hgL hhL hpos E hE in
/-- Actual gradient of the explicit scalar on any actual open physical neighborhood. -/
theorem visibleConnectorCartesianPotential_gradient_eqOn {V : Set Coord} (hV : IsOpen V)
    (hpsi : MapsTo (visibleConnectorCartesianPotentialPhysicalChart L h) V E.source)
    (hr : ∀ q ∈ V, 0 < visibleConnectorCartesianPotentialRadius h q)
    (hDelta : ∀ q ∈ V, visibleConnectorDelta p gamma w q ≠ 0)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s) :
    EqOn (planarGradient (visibleConnectorCartesianPotential L g gamma w h E) ∘
      visibleConnectorSource p w) (visibleConnectorGradient p gamma w) V := by
  have hrec := visibleConnectorCartesianPotential_height_eqOn hL hpL hgammaL hwL hgL hhL
    hpos E hE hpsi hr
  intro q hq
  exact cartesianPotential_gradient_of_pullback hp hgamma hw hg hV hvalue hrec hq (hDelta q hq)

end ActualInverse

private theorem cartesianPotential_delta_continuous {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w) :
    Continuous (visibleConnectorDelta p gamma w) := by
  have hdp := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdg := (contDiff_infty_iff_deriv.mp hgamma).2.continuous
  have hdw := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hwc := hw.continuous
  unfold visibleConnectorDelta visibleConnectorA visibleConnectorC visibleConnectorB
    visibleConnectorDet dotProduct
  simp only [Fin.sum_univ_two]
  fun_prop

/-- Construct actual open saddle neighborhoods of the entire closed physical
strip for the SAME explicit Cartesian scalar. All signs and inverse fields are
ordinary data; the gradient and Hessian conclusions are proved here. -/
theorem visibleConnectorCartesianPotential_closed_strip_calculus
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hA : ∀ s, 0 < visibleConnectorA p w s) (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) → 0 < visibleConnectorDelta p gamma w q)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L p w h)
    (hEs : E.source ⊆ {z : Coord | 0 < planarRadius z})
    (hi : ContDiffOn ℝ ∞ E.symm E.target)
    (hClosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source) :
    ContDiffOn ℝ ∞ (visibleConnectorCartesianPotential L g gamma w h E) E.target ∧
      IsOpen (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      {q : Coord | 0 ≤ q 1 ∧ q 1 ≤ h (q 0)} ⊆
        visibleConnectorCartesianPotentialRuledDomain L p gamma w h E ∧
      EqOn (visibleConnectorCartesianPotential L g gamma w h E ∘ visibleConnectorSource p w)
        (visibleConnectorHeight g gamma w) (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      EqOn (planarGradient (visibleConnectorCartesianPotential L g gamma w h E) ∘ visibleConnectorSource p w)
        (visibleConnectorGradient p gamma w) (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        planarHessian (visibleConnectorCartesianPotential L g gamma w h E) (visibleConnectorSource p w q) *ᵥ w (q 0) =
          (visibleConnectorA p w (q 0)*visibleConnectorB gamma w (q 0) /
            (visibleConnectorDelta p gamma w q)^2) • visibleConnectorJ (w (q 0))) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        (planarHessian (visibleConnectorCartesianPotential L g gamma w h E) (visibleConnectorSource p w q)).det =
          -(visibleConnectorA p w (q 0))^2*(visibleConnectorB gamma w (q 0))^2 /
            (visibleConnectorDelta p gamma w q)^4) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        ∃ N : Set Coord, IsOpen N ∧ visibleConnectorSource p w q ∈ N ∧ N ⊆ E.target ∧
          ∀ y ∈ N, (planarHessian (visibleConnectorCartesianPotential L g gamma w h E) y).det < 0) := by
  let V := visibleConnectorCartesianPotentialRuledDomain L p gamma w h E
  let F := visibleConnectorCartesianPotential L g gamma w h E
  have hF : ContDiffOn ℝ ∞ F E.target := visibleConnectorCartesianPotential_contDiffOn
    hL hp hgamma hw hg hh hpL hgammaL hwL hgL hhL E hEs hi
  have hV : IsOpen V :=
    (isOpen_lt continuous_const (cartesianPotential_radius_smooth hh hpos).continuous).inter
      ((E.open_source.preimage (visibleConnectorCartesianPotentialPhysicalChart_contDiff hh hpos).continuous).inter
        (isOpen_lt continuous_const (cartesianPotential_delta_continuous hp hgamma hw)))
  have hpsi : MapsTo (visibleConnectorCartesianPotentialPhysicalChart L h) V E.source := fun _ hq => hq.2.1
  have hr : ∀ q ∈ V, 0 < visibleConnectorCartesianPotentialRadius h q := fun _ hq => hq.1
  have hd : ∀ q ∈ V, visibleConnectorDelta p gamma w q ≠ 0 := fun _ hq => hq.2.2.ne'
  have hrec := visibleConnectorCartesianPotential_height_eqOn hL hpL hgammaL hwL hgL hhL hpos E hE hpsi hr
  have hgrad := visibleConnectorCartesianPotential_gradient_eqOn hL hp hgamma hw hg
    hpL hgammaL hwL hgL hhL hpos E hE hV hpsi hr hd hvalue
  have hmap : MapsTo (visibleConnectorSource p w) V E.target := by
    intro q hq
    have heq := (visibleConnectorCartesianPotential_physical_pullbacks hL hpL hgammaL hwL hgL hhL hpos (hr q hq)).1
    rw [← heq, ← hE]
    exact E.map_source (hpsi hq)
  have hneg : ∀ q ∈ V, (planarHessian F (visibleConnectorSource p w q)).det < 0 := by
    intro q hq
    exact visibleConnector_actual_hessian_negative hp hgamma hw hF E.open_target hV hmap hgrad
      hq (hd q hq) (hA (q 0)).ne' (hB (q 0)).ne'
  refine ⟨hF,hV,?_,hrec,hgrad,?_,?_,?_⟩
  · intro q hq
    have hquot : 0 ≤ q 1 / h (q 0) ∧ q 1 / h (q 0) ≤ 1 :=
      ⟨div_nonneg hq.1 (hpos (q 0)).le, (div_le_one (hpos (q 0))).mpr hq.2⟩
    have hbound : 1 ≤ visibleConnectorCartesianPotentialRadius h q ∧
        visibleConnectorCartesianPotentialRadius h q ≤ 2 := by
      dsimp [visibleConnectorCartesianPotentialRadius]
      constructor <;> linarith [hquot.1,hquot.2]
    have hrq : 0 < visibleConnectorCartesianPotentialRadius h q := by linarith [hbound.1]
    refine ⟨hrq, hClosed ?_, hDelta q hq.1 hq.2⟩
    change 1 ≤ planarRadius (saddlePolarChart ![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L]) ∧
      planarRadius (saddlePolarChart ![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L]) ≤ 2
    rw [angularDescent_radius_polar (q := ![visibleConnectorCartesianPotentialRadius h q, 2*Real.pi*q 0/L]) hrq]
    exact hbound
  · intro q hq
    exact visibleConnector_actual_hessian_transverse hp hgamma hw hF E.open_target hV hmap hgrad hq (hd q hq)
  · intro q hq
    exact visibleConnector_actual_hessian_determinant hp hgamma hw hF E.open_target hV hmap hgrad hq (hd q hq)
  · intro q hq
    obtain ⟨eLocal,FLocal,hqLocal,heLocal,_hiLocal,_hLocal,_hrecLocal,_hgradLocal⟩ :=
      visibleConnector_exists_local_potential hg hp hgamma hw hvalue q (hd q hq)
    let N := eLocal.target ∩ eLocal.symm ⁻¹' V
    have hN : IsOpen N := eLocal.continuousOn_symm.isOpen_inter_preimage eLocal.open_target hV
    have hyLocal : visibleConnectorSource p w q ∈ eLocal.target := by
      rw [← heLocal]
      exact eLocal.map_source hqLocal
    have hqInv : eLocal.symm (visibleConnectorSource p w q) = q := by
      rw [← heLocal]
      exact eLocal.left_inv hqLocal
    have hsy {y : Coord} (hy : y ∈ N) : visibleConnectorSource p w (eLocal.symm y) = y := by
      rw [← heLocal]
      exact eLocal.right_inv hy.1
    refine ⟨N,hN,⟨hyLocal,by change eLocal.symm (visibleConnectorSource p w q) ∈ V; rw [hqInv]; exact hq⟩,?_,?_⟩
    · intro y hy
      rw [← hsy hy]
      exact hmap hy.2
    · intro y hy
      rw [← hsy hy]
      exact hneg _ hy.2

end
end TightVer401
