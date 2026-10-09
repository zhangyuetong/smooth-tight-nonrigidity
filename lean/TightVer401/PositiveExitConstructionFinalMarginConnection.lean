import TightVer401.PositiveExitConstructionVisibleTurnSeed
import TightVer401.PositiveExitConstructionSelectedPatches
import TightVer401.PositiveExitConstructionSeam

/-! Exact coordinate conversion of the final complete-leaf margin into the
selected-patch consumer's raw-leaf convention. The corrected frame, potential,
flow margin and containment proof are retained; no leaf, field or clock is chosen. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The two retained complex-coordinate conventions are literally equal. -/
theorem positiveExitComplexPoint_eq_angularDescentComplex :
    positiveExitComplexPoint = angularDescentComplex := by
  funext p
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

/-- The actual selected raw Gauss leaf is the real representative of the
same identity-flow leaf used by the central-coordinate margin. -/
theorem positiveExit_final_margin_central_coordinates {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (s : ℝ) :
    identityBandCentralCoordinates d
        (![s, principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s] : Coord) =
      gnomonicInverse (positiveExitRawLeaf d hb hinside v s) := by
  rw [positiveExitRawLeaf_eq_raw]
  rfl

/-- Convert the exact final margin exported by the same-seed visible-turn
protected-field producer into the exact `hmargin` of selected visible patches.
This theorem only rewrites coordinates and reorders the retained conclusions. -/
theorem positiveExit_final_margin_selected_raw_leaves {T δ w : ℝ}
    [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w)
    (G : Coord → ℝ)
    (hmargin : ∀ v ∈ Ioo (0 : ℝ) δ,
      let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
      ContDiff ℝ ∞ u ∧ Function.Periodic u T ∧
      HasPositiveArgumentTurn
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) T ∧
      HasPositiveArgumentTurn
        (positiveExitComplexTrace (fun s => planarGradient G
          (identityBandCentralCoordinates d ![s, u s]))) T ∧
      (∀ s, positiveExitComplexPoint (identityBandCentralCoordinates d ![s, u s]) ≠ 0) ∧
      (∀ s, positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, u s])) ≠ 0) ∧
      ComplexVisiblePair (1 / 4)
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s]))
        (fun s => Complex.I * positiveExitComplexPoint
          (planarGradient G (identityBandCentralCoordinates d ![s, u s]))) ∧
      ComplexVisiblePair (4 / 5)
        (corrugatedReverseReflect (positiveExitComplexTrace
          (fun s => planarGradient G (identityBandCentralCoordinates d ![s, u s]))))
        (fun s => Complex.I * corrugatedReverseReflect
          (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) s)) :
    ∀ v : Ioo (0 : ℝ) δ,
      (∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0) ∧
      (∀ s, angularDescentComplex (planarGradient G
        (gnomonicInverse (positiveExitRawLeaf d hb hinside v s))) ≠ 0) ∧
      HasPositiveArgumentTurn
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      HasPositiveArgumentTurn (angularDescentComplex ∘ planarGradient G ∘
        gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      ComplexVisiblePair (1 / 4)
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v)
        (fun s => Complex.I * angularDescentComplex (planarGradient G
          (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)))) ∧
      ComplexVisiblePair (4 / 5)
        (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘
          gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v))
        (fun s => Complex.I * corrugatedReverseReflect
          (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) s) := by
  intro v
  obtain ⟨_, _, hpturn, hgturn, hpne, hgne, hout, href⟩ := hmargin v v.property
  have hcoord := positiveExit_final_margin_central_coordinates d hb hinside v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using hpne
  · simpa only [positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using hgne
  · simpa only [positiveExitComplexTrace, Function.comp_def,
      positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using hpturn
  · simpa only [positiveExitComplexTrace, Function.comp_def,
      positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using hgturn
  · simpa only [positiveExitComplexTrace, Function.comp_def,
      positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using hout
  · simpa only [positiveExitComplexTrace, Function.comp_def,
      positiveExitComplexPoint_eq_angularDescentComplex, hcoord] using href

end
end TightVer401
