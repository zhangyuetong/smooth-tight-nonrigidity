import TightVer401.VisibleConnectorSourceInverseApplication
import TightVer401.VisibleConnectorCartesianPotentialCalculus

/-! Concrete raw Cartesian potential application. Both inverse charts and the
scalar are constructed from ordinary ruling/Jordan data. One actual open saddle
carrier contains the entire closed target band, including both boundary jets. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- Construct the raw source inverse, SAME actual descended potential, open
strict-saddle carrier and boundary first jets. No inverse or scalar conclusion
is an input; the original incoming open potential germ is a separate obligation. -/
theorem visibleConnectorCartesianPotentialApplication_global
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hA : ∀ s, 0 < visibleConnectorA p w s) (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) → 0 < visibleConnectorDelta p gamma w q)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (p (L*t) + h (L*t) • w (L*t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm (p (L*t))))
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi) (G : Coord → ℝ) (U : Set Coord),
      e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (H z : Coord) = visibleConnectorCartesianSource L p w h z) ∧
      visibleConnectorCartesianSource L p w h ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} = annularCoordJordanClosure Ho Hi ∧
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source ∧
      E.source ⊆ {z : Coord | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h) E.source ∧
      (∀ z ∈ E.source, 0 < annularJacobian (visibleConnectorCartesianSource L p w h) z) ∧
      (E : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) ∧
      G = visibleConnectorCartesianPotential L g gamma w h E ∧
      IsOpen U ∧ annularCoordJordanClosure Ho Hi ⊆ U ∧ U ⊆ E.target ∧
      ContDiffOn ℝ ∞ G U ∧ (∀ y ∈ U, (planarHessian G y).det < 0) ∧
      MapsTo (visibleConnectorSource p w) (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) U ∧
      EqOn (G ∘ visibleConnectorSource p w) (visibleConnectorHeight g gamma w)
        (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      EqOn (planarGradient G ∘ visibleConnectorSource p w) (visibleConnectorGradient p gamma w)
        (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        planarHessian G (visibleConnectorSource p w q) *ᵥ w (q 0) =
          (visibleConnectorA p w (q 0)*visibleConnectorB gamma w (q 0) /
            (visibleConnectorDelta p gamma w q)^2) • visibleConnectorJ (w (q 0))) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        (planarHessian G (visibleConnectorSource p w q)).det =
          -(visibleConnectorA p w (q 0))^2*(visibleConnectorB gamma w (q 0))^2 /
            (visibleConnectorDelta p gamma w q)^4) ∧
      (∀ s : ℝ, p s ∈ U ∧ G (p s) = g s ∧ planarGradient G (p s) = gamma s ∧
        p s + h s • w s ∈ U ∧
        G (p s + h s • w s) = g s + h s*(gamma s ⬝ᵥ w s) ∧
        planarGradient G (p s + h s • w s) = visibleConnectorGradient p gamma w ![s,h s]) := by
  obtain ⟨e0,E,H,he0Source,he0Target,he0Actual,hi0,hH,hImage,hKSource,hSourcePositive,
    hSourceSmooth,hJac,hE,hi,hBandTarget,hAgree⟩ :=
    visibleConnectorSourceInverseApplication_global hL hp hw hh hpL hwL hhL hpos gamma
      hDelta hOuter hInner hNested
  let G := visibleConnectorCartesianPotential L g gamma w h E
  let V := visibleConnectorCartesianPotentialRuledDomain L p gamma w h E
  obtain ⟨hG,hV,hStrip,hrec,hgrad,hAction,hDet,hNeighborhood⟩ :=
    visibleConnectorCartesianPotential_closed_strip_calculus hL hp hgamma hw hg hh
      hpL hgammaL hwL hgL hhL hpos hvalue hA hB hDelta E hE hSourcePositive hi hKSource
  have hNeighborhood' : ∀ q : V, ∃ N : Set Coord,
      IsOpen N ∧ visibleConnectorSource p w q ∈ N ∧ N ⊆ E.target ∧
      ∀ y ∈ N, (planarHessian G y).det < 0 := fun q => hNeighborhood q q.property
  choose N hNOpen hNMem hNSub hNNeg using hNeighborhood'
  let U : Set Coord := ⋃ q : V, N q
  have hU : IsOpen U := isOpen_iUnion hNOpen
  have hUTarget : U ⊆ E.target := by
    intro y hy
    obtain ⟨q,hq⟩ := mem_iUnion.mp hy
    exact hNSub q hq
  have hUNeg : ∀ y ∈ U, (planarHessian G y).det < 0 := by
    intro y hy
    obtain ⟨q,hq⟩ := mem_iUnion.mp hy
    exact hNNeg q y hq
  have hSourceU : MapsTo (visibleConnectorSource p w) V U := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,hNMem ⟨q,hq⟩⟩
  have hBandU : annularCoordJordanClosure Ho Hi ⊆ U := by
    rw [← hImage]
    rintro y ⟨z,hz,rfl⟩
    let q : Coord := ![planarRadius z, Complex.arg (angularDescentComplex z)]
    let physical := visibleConnectorSourceInverseClock L h q
    have hr : 0 < q 0 := by
      change 0 < planarRadius z
      linarith [hz.1]
    have hhq := hpos (L*q 1/(2*Real.pi))
    have hu0 : 0 ≤ physical 1 := by
      change 0 ≤ (planarRadius z-1)*h (L*q 1/(2*Real.pi))
      exact mul_nonneg (sub_nonneg.mpr hz.1) hhq.le
    have hu1 : physical 1 ≤ h (physical 0) := by
      change (planarRadius z-1)*h (L*q 1/(2*Real.pi)) ≤ h (L*q 1/(2*Real.pi))
      nlinarith [hz.2]
    have hPhysical : physical ∈ V := hStrip ⟨hu0,hu1⟩
    have hSourcePhysical : visibleConnectorCartesianSource L p w h z =
        visibleConnectorSource p w physical := by
      calc
        visibleConnectorCartesianSource L p w h z =
            visibleConnectorCartesianSource L p w h (saddlePolarChart q) :=
          congrArg (visibleConnectorCartesianSource L p w h)
            (visibleConnectorSourceInverse_polar_representative z).symm
        _ = visibleConnectorPolarSource L p w h q :=
          visibleConnectorCartesianSource_polar hpL hwL hhL hr
        _ = visibleConnectorSource p w physical := rfl
    rw [hSourcePhysical]
    exact hSourceU hPhysical
  have hBoundary : ∀ s : ℝ, p s ∈ U ∧ G (p s) = g s ∧ planarGradient G (p s) = gamma s ∧
      p s + h s • w s ∈ U ∧ G (p s + h s • w s) = g s + h s*(gamma s ⬝ᵥ w s) ∧
      planarGradient G (p s + h s • w s) = visibleConnectorGradient p gamma w ![s,h s] := by
    intro s
    have hs0 : (![s,0] : Coord) ∈ V := hStrip (by
      change (0 : ℝ) ≤ 0 ∧ 0 ≤ h s
      exact ⟨le_rfl,(hpos s).le⟩)
    have hsh : (![s,h s] : Coord) ∈ V := hStrip (by
      change (0 : ℝ) ≤ h s ∧ h s ≤ h s
      exact ⟨(hpos s).le,le_rfl⟩)
    have hpU : p s ∈ U := by
      simpa only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_smul,add_zero] using hSourceU hs0
    have hpVal : G (p s) = g s := by
      simpa only [Function.comp_apply,visibleConnectorSource,visibleConnectorHeight,
        Matrix.cons_val_zero,Matrix.cons_val_one,zero_smul,zero_mul,add_zero] using hrec hs0
    have hpGrad : planarGradient G (p s) = gamma s := by
      simpa only [Function.comp_apply,visibleConnectorSource,visibleConnectorGradient,
        Matrix.cons_val_zero,Matrix.cons_val_one,zero_smul,zero_mul,zero_div,add_zero] using hgrad hs0
    have hTUnion : p s+h s • w s ∈ U := by
      simpa only [visibleConnectorSource,Matrix.cons_val_zero,Matrix.cons_val_one] using hSourceU hsh
    have hTValue : G (p s+h s • w s) = g s+h s*(gamma s ⬝ᵥ w s) := by
      simpa only [Function.comp_apply,visibleConnectorSource,visibleConnectorHeight,
        Matrix.cons_val_zero,Matrix.cons_val_one] using hrec hsh
    have hTGradient : planarGradient G (p s+h s • w s) = visibleConnectorGradient p gamma w ![s,h s] := by
      simpa only [Function.comp_apply,visibleConnectorSource,Matrix.cons_val_zero,Matrix.cons_val_one] using hgrad hsh
    exact ⟨hpU,hpVal,hpGrad,hTUnion,hTValue,hTGradient⟩
  exact ⟨e0,E,H,G,U,he0Source,he0Target,he0Actual,hi0,hH,hImage,hKSource,hSourcePositive,
    hSourceSmooth,hJac,hE,hi,hBandTarget,hAgree,rfl,hU,hBandU,hUTarget,hG.mono hUTarget,
    hUNeg,hSourceU,hrec,hgrad,hAction,hDet,hBoundary⟩

end
end TightVer401
