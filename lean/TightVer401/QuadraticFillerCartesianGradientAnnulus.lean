import TightVer401.QuadraticFillerCartesianGradientAnnulusAlgebra
import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth

/-! Explicit actual gradient diffeomorphism on the retained strict inner annulus. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The literal inverse realizes the actual filler gradient as an open partial homeomorphism.
This construction uses only the retained inner germ, so angular traces can be arbitrary. -/
def quadraticFillerCartesianGradientEquiv {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) : OpenPartialHomeomorph Coord Coord where
  toFun := planarGradient (quadraticFillerCartesianPotential R M h b)
  invFun := quadraticFillerCartesianGradientInverse R M
  source := quadraticFillerCartesianGradientInner R
  target := quadraticFillerCartesianGradientAnnulus R M
  map_source' := fun p hp => quadraticFillerCartesianGradient_actual_mapsTo hR hM h b hp
  map_target' := fun y hy => quadraticFillerCartesianGradient_inverse_mapsTo hR hM hy
  left_inv' := by
    intro p hp
    rw [quadraticFillerCartesianGradient_actual_eq hR M h b hp]
    exact quadraticFillerCartesianGradient_left_inverse hR hM hp
  right_inv' := by
    intro y hy
    rw [quadraticFillerCartesianGradient_actual_eq hR M h b
      (quadraticFillerCartesianGradient_inverse_mapsTo hR hM hy)]
    exact quadraticFillerCartesianGradient_right_inverse hR hM hy
  open_source := quadraticFillerCartesianGradient_inner_isOpen R
  open_target := quadraticFillerCartesianGradient_annulus_isOpen R M
  continuousOn_toFun := (quadraticFillerCartesianGradient_contDiffOn hR M h b).continuousOn
  continuousOn_invFun := (quadraticFillerCartesianGradient_inverse_contDiffOn hR hM).continuousOn

/-- Actual inner-gradient injectivity, derived from the constructed explicit inverse. -/
theorem quadraticFillerCartesianGradient_injOn {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) :
    InjOn (planarGradient (quadraticFillerCartesianPotential R M h b))
      (quadraticFillerCartesianGradientInner R) :=
  (quadraticFillerCartesianGradientEquiv hR hM h b).injOn

/-- The actual inner gradient has precisely the open annular image MR/2<radius<MR. -/
theorem quadraticFillerCartesianGradient_image {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) :
    planarGradient (quadraticFillerCartesianPotential R M h b) ''
        quadraticFillerCartesianGradientInner R = quadraticFillerCartesianGradientAnnulus R M :=
  (quadraticFillerCartesianGradientEquiv hR hM h b).bijOn.image_eq

/-- Both directions of this actual inner gradient homeomorphism are smooth. -/
theorem quadraticFillerCartesianGradientEquiv_smooth {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianGradientEquiv hR hM h b)
        (quadraticFillerCartesianGradientEquiv hR hM h b).source ∧
      ContDiffOn ℝ ∞ (quadraticFillerCartesianGradientEquiv hR hM h b).symm
        (quadraticFillerCartesianGradientEquiv hR hM h b).target := by
  exact ⟨quadraticFillerCartesianGradient_contDiffOn hR M h b,
    quadraticFillerCartesianGradient_inverse_contDiffOn hR hM⟩

end
end TightVer401
