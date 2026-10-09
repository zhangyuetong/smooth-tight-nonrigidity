import TightVer401.CompletedSaddleAnnulusCylinderEndCollars
import TightVer401.CompletedSaddleAnnulusCylinderInjectivity
import TightVer401.CompletedSaddleAnnulusCylinderCurvature

/-! Actual protected saddle-cylinder input from ordinary same-object scalar
completion data. The radial parameter and positive height are constructed. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual physical horizontal norm is the same actual cylinder radius. -/
theorem completedSaddleAnnulusCylinderMap_horizontal_norm
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) (A RN d0 dInfinity : ℝ)
    (β : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ)
    (hr : 0 < β (completedSaddleAnnulusCylinderPhase p.2)) :
    ‖corrugatedAmbientHorizontalCLM (completedSaddleAnnulusCylinderMap
      G e A RN d0 dInfinity β p)‖ = β (completedSaddleAnnulusCylinderPhase p.2) := by
  have hh : corrugatedAmbientHorizontalCLM (completedSaddleAnnulusCylinderMap
      G e A RN d0 dInfinity β p) =
      -angularDescentComplex (completedSaddleAnnulusCylinderPlanePoint
        (β (completedSaddleAnnulusCylinderPhase p.2)) p.1) := by
    apply Complex.ext <;> simp [corrugatedAmbientHorizontalCLM,
      completedSaddleAnnulusCylinderMap,completedSaddleAnnulusCylinderPlanePoint,
      angularDescentComplex,revolutionAxis,Complex.mul_re,Complex.mul_im]
    all_goals split_ifs <;> simp
  rw [hh,norm_neg,angularDescentComplex_norm,
    completedSaddleAnnulusCylinderPlanePoint_radius hr]

/-- Strict interior horizontal radius is derived from the actual beta order,
including the actual middle phase where the radial derivative vanishes. -/
theorem completedSaddleAnnulusCylinderMap_horizontal_radius_lt
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ univ ×ˢ Ioo (0:ℝ) Real.pi) :
    ‖corrugatedAmbientHorizontalCLM (completedSaddleAnnulusCylinderMap
      G e A RN d0 dInfinity β p)‖ < RN := by
  have hClosed : p.2 ∈ Icc (0:ℝ) Real.pi := Ioo_subset_Icc_self hp.2
  have hRadius := completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hClosed
  rw [completedSaddleAnnulusCylinderMap_horizontal_norm G e A RN d0 dInfinity β p
    (hA.trans_le hRadius.1),← hβRN]
  apply hMono (completedSaddleAnnulusCylinderPhase_mem hClosed)
    (show Real.pi ∈ Icc (Real.pi/2) Real.pi from ⟨by linarith [Real.pi_pos],le_rfl⟩)
  change max p.2 (Real.pi-p.2) < Real.pi
  exact max_lt hp.2.2 (by linarith [hp.2.1])

section ActualData
variable {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
variable {A RN μ B ε L d0 dInfinity : ℝ}
variable (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ)
variable (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
variable (hSource : e.source = {p : Coord | 0 < planarRadius p})
variable (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
variable (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
variable (heG : ∀ p ∈ e.source, e p = planarGradient G p)
variable (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
  G p = RN*planarRadius p-μ*planarRadius p^2/2+d0)
variable (hInfinity : ∀ p : Coord, L < planarRadius p →
  G p = A*planarRadius p-B/planarRadius p+dInfinity)

include e hA hARN hμ hB hε hL hSource hTarget hG hi heG hQuadratic hInfinity in
/-- Positive actual height separation is a consequence of the same completed
potential and gradient inverse, rather than a cylinder-output premise. -/
theorem completedSaddleAnnulusCylinderAssembly_height_pos : 0 < dInfinity-d0 :=
  sub_pos.mpr (completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity).2.2.1

include hA hARN hμ hB hε hL hSource hTarget hG hi heG hQuadratic hInfinity in
/-- Actual graph-height separation throughout the same actual annulus. -/
theorem completedSaddleAnnulusCylinderAssembly_height_bounds :
    ∀ y ∈ quadraticRadialFillingOpenAnnulus A RN,
      d0 < completedSaddleAnnulusGraphHeight G e y ∧
      completedSaddleAnnulusGraphHeight G e y < dInfinity := by
  intro y hy
  have hb := (completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity).2.2.2.1 y hy
  rwa [completedSaddleAnnulusHeightResolved_eq_interior hy] at hb

/-- Construct all actual protected saddle-cylinder fields from the same
ordinary completion data and actual scalar parameter properties. -/
def completedSaddleAnnulusCylinderInput {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hβDerivative : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (hβNorth : β =ᶠ[𝓝 Real.pi]
      (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2))) :
    ProtectedSaddleCylinderInput RN μ (dInfinity-d0) where
  radius_pos := hA.trans hARN
  coefficient_pos := hμ
  height_pos := completedSaddleAnnulusCylinderAssembly_height_pos e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity
  saddle := completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β
  saddle_continuous := completedSaddleAnnulusCylinderMap_continuousOn e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity hβ.continuous hMono hβA hβRN
  saddle_smooth := completedSaddleAnnulusCylinderMap_contMDiffOn e hA hARN hB hL
    hSource hTarget hG hi heG hInfinity hβ hMono hβA hβRN hβNeck
  saddle_immersion := completedSaddleAnnulusCylinderMap_mfderiv_injective e hA hARN hB hL
    hSource hTarget hG hi heG hInfinity hβ hMono hβA hβRN hβDerivative hβNeck
  saddle_injective := completedSaddleAnnulusCylinderMap_injOn e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN
  saddle_radius := fun _ hp =>
    completedSaddleAnnulusCylinderMap_horizontal_radius_lt G e hA hMono hβA hβRN hp
  south_germ := by
    obtain ⟨δ,hδ,hδπ,hCollar⟩ := completedSaddleAnnulusCylinderMap_south_germ e hA hARN hμ hε
      (completedSaddleAnnulusCylinderAssembly_height_pos e hA hARN hμ hB hε hL
        hSource hTarget hG hi heG hQuadratic hInfinity)
      hSource hTarget heG hQuadratic hβNorth
    refine ⟨δ,hδ,hδπ,?_⟩
    intro q u hu
    simpa only [completedSaddleAnnulusSouthCollar,completedSaddleAnnulusSouthTransverse,
      protectedTorusCollarScale,neg_mul] using hCollar q u hu
  north_germ := by
    obtain ⟨δ,hδ,hδπ,hCollar⟩ := completedSaddleAnnulusCylinderMap_north_germ e hA hARN hμ hε
      (completedSaddleAnnulusCylinderAssembly_height_pos e hA hARN hμ hB hε hL
        hSource hTarget hG hi heG hQuadratic hInfinity)
      hSource hTarget heG hQuadratic hβNorth
    refine ⟨δ,hδ,hδπ,?_⟩
    intro q u hu
    simpa only [completedSaddleAnnulusNorthCollar,completedSaddleAnnulusNorthTransverse,
      protectedTorusCollarScale,neg_mul] using hCollar q u hu

theorem completedSaddleAnnulusCylinderInput_saddle {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hβDerivative : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (hβNorth : β =ᶠ[𝓝 Real.pi]
      (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2))) :
    (completedSaddleAnnulusCylinderInput e hA hARN hμ hB hε hL hSource hTarget hG hi heG
      hQuadratic hInfinity hβ hMono hβA hβRN hβDerivative hβNeck hβNorth).saddle =
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β := rfl

include e hA hARN hμ hB hε hL hSource hTarget hG hi heG hQuadratic hInfinity in
/-- Choose the actual scalar radial parameter and assemble the SAME actual
closed saddle-cylinder input. Every witness and its literal map is exposed. -/
theorem exists_completedSaddleAnnulusCylinderInput
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0) :
    d0 < dInfinity ∧ ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧ StrictMonoOn β (Icc (Real.pi/2) Real.pi) ∧
      β (Real.pi/2) = A ∧ β Real.pi = RN ∧
      (∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) ∧
      β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2) ∧
      β =ᶠ[𝓝 Real.pi]
        (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2)) ∧
      ∃ D : ProtectedSaddleCylinderInput RN μ (dInfinity-d0),
        D.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β ∧
        (∀ p ∈ univ ×ˢ Icc (0:ℝ) Real.pi,
          (p.2 < Real.pi/2 → D.saddle p 2 < 0) ∧
          (Real.pi/2 < p.2 → 0 < D.saddle p 2)) ∧
        (∀ p ∈ univ ×ˢ Icc (0:ℝ) Real.pi, D.saddle p 2 = 0 ↔ p.2 = Real.pi/2) ∧
        (∀ p ∈ univ ×ˢ Ioo (0:ℝ) Real.pi,
          gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap D.saddle p))
            ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
              (chartAt (ModelProd ℝ ℝ) p p)) < 0) := by
  have hh := completedSaddleAnnulusCylinderAssembly_height_pos e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity
  obtain ⟨β,hβ,hMono,hβA,hβRN,hβDerivative,hβNeck,hβNorth⟩ :=
    exists_completedSaddleAnnulusRadialParameter hA hARN hB hμ hh
  let D := completedSaddleAnnulusCylinderInput e hA hARN hμ hB hε hL hSource hTarget
    hG hi heG hQuadratic hInfinity hβ hMono hβA hβRN hβDerivative hβNeck hβNorth
  refine ⟨sub_pos.mp hh,β,hβ,hMono,hβA,hβRN,hβDerivative,hβNeck,hβNorth,D,rfl,?_,?_,?_⟩
  · exact completedSaddleAnnulusCylinderMap_height_signs e hA hARN hμ hB hε hL
      hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN
  · intro p hp
    exact completedSaddleAnnulusCylinderMap_height_zero_iff e hA hARN hμ hB hε hL
      hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN hp
  · exact completedSaddleAnnulusCylinderMap_preferred_gaussianCurvature_neg e hA hARN hB hL
      hSource hTarget hG hi heG hNeg hInfinity hβ hMono hβA hβRN hβDerivative hβNeck

end ActualData
end
end TightVer401
