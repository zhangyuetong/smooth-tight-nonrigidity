import TightVer401.RuledCentralSupport
import TightVer401.NormalLoopRuledFrame

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- In the actual normal-loop frame the mixed entry is the original speed
a, in the manuscript's ordered spherical basis (ζ_r,P). -/
theorem normalLoop_central_support_tensor {L : ℝ} (d : PeriodicRuledFrame L)
    (ζ : ℝ → Ambient) (a ψ : ℝ → ℝ) (hapos : ∀ r, 0 < a r)
    (hE : d.E = deriv ζ ∘ ψ) (hT : d.T = normalLoopTangent ζ ∘ ψ)
    (hτ : d.τ = normalLoopPhysicalTau a ψ) (s : ℝ) :
    ∃ hw : d.n s ≠ 0, ∃ e : OpenPartialHomeomorph Coord Coord,
      (![s, 0] : Coord) ∈ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q ∈ e.source, d.rawGaussMap q = sphereHemisphere (d.n s) hw (e q)) ∧
      let Q := sphereHemisphere (d.n s) hw
      let g := inducedMetric Q
      let H : Coord → ℝ := fun y => inner ℝ (ruledMap d.γ d.E (e.symm y)) (Q y)
      let V : Fin 2 → Coord := ![
        fderiv ℝ e (![s, 0] : Coord) (a (ψ s) • (Pi.single 0 1 : Coord)),
        fderiv ℝ e (![s, 0] : Coord) (a (ψ s) • (Pi.single 1 1 : Coord))]
      (∀ y ∈ e.target, ruledMap d.γ d.E (e.symm y) = sphereSupportMap g Q H y) ∧
      (∀ i, fderiv ℝ Q (e (![s, 0] : Coord)) (V i) =
        (![deriv ζ (ψ s), normalLoopTangent ζ (ψ s)] : Fin 2 → Ambient) i) ∧
      (fun i j => sphereSupportTensorBilinear g H (e (![s, 0] : Coord)) (V i) (V j)) =
        !![0, a (ψ s); a (ψ s), 0] ∧ 0 < a (ψ s) := by
  have hneg : d.τ s < 0 := by
    rw [hτ]
    exact neg_lt_zero.mpr (inv_pos.mpr (hapos (ψ s)))
  have hc : (-d.τ s)⁻¹ = a (ψ s) := by
    rw [hτ]
    simp [normalLoopPhysicalTau]
  have h := ruled_central_support_tensor d s hneg
  simpa only [hc, hE, hT, Function.comp_apply] using h

end
end TightVer401
