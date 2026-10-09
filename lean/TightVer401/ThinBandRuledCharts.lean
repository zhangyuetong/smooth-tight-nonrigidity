import TightVer401.PeriodicRuledFrame
import TightVer401.ThinBandChartTransport

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def coordPairHomeomorph : Coord ≃ₜ ℝ × ℝ where
  toFun p := (p 0, p 1)
  invFun p := ![p.1, p.2]
  left_inv p := by ext i; fin_cases i <;> rfl
  right_inv p := by rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := by fun_prop

def ruledCircleChart (L r : ℝ) [Fact (0 < L)] :
    OpenPartialHomeomorph Coord (AddCircle L × ℝ) :=
  coordPairHomeomorph.toOpenPartialHomeomorph.trans
    ((AddCircle.openPartialHomeomorphCoe L (r - L / 2)).prod
      (Homeomorph.refl ℝ).toOpenPartialHomeomorph)

theorem ruledCircleChart_apply (L r : ℝ) [Fact (0 < L)] (p : Coord) :
    ruledCircleChart L r p = (periodProjection L (p 0), p 1) := rfl

theorem ruledCircleChart_center_source (L r : ℝ) [hL : Fact (0 < L)] :
    (![r, 0] : Coord) ∈ (ruledCircleChart L r).source := by
  change (![r, 0] : Coord) ∈ coordPairHomeomorph.toOpenPartialHomeomorph.source ∧
    coordPairHomeomorph (![r, 0]) ∈
      ((AddCircle.openPartialHomeomorphCoe L (r - L / 2)).prod
        (Homeomorph.refl ℝ).toOpenPartialHomeomorph).source
  constructor
  · exact mem_univ _
  · change r ∈ Ioo (r - L / 2) (r - L / 2 + L) ∧ (0 : ℝ) ∈ univ
    exact ⟨⟨by linarith [hL.out], by linarith [hL.out]⟩, mem_univ _⟩

def PeriodicRuledFrame.fullBandMap {L : ℝ} (d : PeriodicRuledFrame L) :
    AddCircle L × ℝ → Ambient := fun p =>
  d.period_γ.lift p.1 + p.2 • d.period_E.lift p.1

theorem ruledCircleChart_fullBandMap {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (r : ℝ) (p : Coord) :
    d.fullBandMap (ruledCircleChart L r p) = ruledMap d.γ d.E p := by
  rw [ruledCircleChart_apply]
  change d.period_γ.lift (periodProjection L (p 0)) +
    p 1 • d.period_E.lift (periodProjection L (p 0)) = _
  rw [periodicLift_coe, periodicLift_coe]
  rfl

end
end TightVer401
