import TightVer401.CompletedSaddleAnnulusProtectedAssembly
import TightVer401.ProtectedTorusPositiveGaussCurvatureActualGraphCylinder
import TightVer401.CompletedSaddleTorusMeridianWitnessConnection

/-! Same-tuple connection from the actual protected saddle producer to its
actual graph-cylinder curvature consumer and ONE full convex closure witness.
No new geometric construction or stronger worker producer is needed. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Package the SAME ordinary potential/inverse/parameter and literal cylinder
as actual graph-cylinder data; no surface curvature conclusion is an input. -/
def completedSaddleTorusActualGraphData_of_literal
    {T w RN μ h : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (K : Set (AddCircle T × Ioo (0 : ℝ) w))
    (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) (β : ℝ → ℝ)
    (A B L d0 dInfinity : ℝ)
    (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    (hβ : ContDiff ℝ ∞ β) (hMono : StrictMonoOn β (Icc (Real.pi / 2) Real.pi))
    (hβA : β (Real.pi / 2) = A) (hβRN : β Real.pi = RN)
    (hβDerivative : ∀ u ∈ Ioo (Real.pi / 2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi / 2)] (fun u => A + B * (u - Real.pi / 2)^2))
    (hLiteral : Q.cylinder.saddle =
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) :
    ProtectedTorusActualGraphCylinderData Q.cylinder :=
  protectedTorusActualGraphCylinderData_of_ordinary Q.cylinder G e β A B L d0 dInfinity
    hA hARN hB hL hSource hTarget hG hi heG hNeg hInfinity
    hβ hMono hβA hβRN hβDerivative hβNeck hLiteral
section OrdinaryData
variable {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
variable (K : Set (AddCircle T × Ioo (0:ℝ) w))
variable {G G0 : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
variable {A RN μ B ε L d0 dInfinity : ℝ}
variable (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ) (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
variable (hSource : e.source = {p : Coord | 0 < planarRadius p})
variable (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
variable (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
variable (heG : ∀ p ∈ e.source, e p = planarGradient G p)
variable (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
variable (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
  G p = RN*planarRadius p-μ*planarRadius p^2/2+d0)
variable (hInfinity : ∀ p : Coord, L < planarRadius p →
  G p = A*planarRadius p-B/planarRadius p+dInfinity)
variable (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0:ℝ) w) Coord)
variable (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
variable (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
variable (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
variable (hK : K ⊆ c0.source) {W : Set Coord} (hW : IsOpen W) (hWe : W ⊆ e.source)
variable (hKW : c0 '' K ⊆ W) (hEq : EqOn G G0 W)

include e hA hARN hμ hB hε hL hSource hTarget hG hi heG hNeg hQuadratic hInfinity
  c0 hc0 hci0 hBand hK hW hWe hKW hEq in
/-- The retained producer already returns every scalar parameter property
needed by actual graph-cylinder curvature. Construct its Q from the original
ordinary inputs, then keep that SAME G/e/β/Q and choose ONE full closure. -/
theorem exists_completedSaddleTorusActualGraph_with_full_meridian :
    d0 < dInfinity ∧ ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧ StrictMonoOn β (Icc (Real.pi/2) Real.pi) ∧
      β (Real.pi/2) = A ∧ β Real.pi = RN ∧
      (∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) ∧
      β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2) ∧
      β =ᶠ[𝓝 Real.pi]
        (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2)) ∧
      ∃ Q : CompletedSaddleAnnulusGeometryOutput d K RN μ (dInfinity-d0),
        Q.cylinder.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β ∧
        Q.verticalOffset = dInfinity ∧
        ∃ C : ProtectedTorusActualGraphCylinderData Q.cylinder,
          C.G = G ∧ C.e = e ∧ C.beta = β ∧
          C.A = A ∧ C.B = B ∧ C.L = L ∧ C.d0 = d0 ∧ C.dInfinity = dInfinity ∧
          ∃ D : ParabolicConvexClosureData RN μ (dInfinity-d0),
            ∃ Assembly : ProtectedTorusAssemblyInput RN μ (dInfinity-d0),
              Assembly = completedSaddleTorusAssemblyFromMeridian Q.cylinder D ∧
              Assembly.toProtectedSaddleCylinderInput = Q.cylinder ∧
              Assembly.toProtectedParabolicMeridianInput = D.toProtectedParabolicMeridianInput ∧
              Assembly.meridian = D.meridian ∧
              NativeTorusSmoothEmbedding
                (protectedTorusMap Assembly.saddle Assembly.meridian (dInfinity-d0)) := by
  obtain ⟨hHeight, β, hβ, hMono, hβA, hβRN, hβDerivative, hβNeck, hβNorth,
      Q, hLiteral, hOffset⟩ :=
    exists_completedSaddleAnnulusGeometryOutput d K e hA hARN hμ hB hε hL
      hSource hTarget hG hi heG hNeg hQuadratic hInfinity
      c0 hc0 hci0 hBand hK hW hWe hKW hEq
  let C := completedSaddleTorusActualGraphData_of_literal d K Q G e β A B L d0 dInfinity
    hA hARN hB hL hSource hTarget hG hi heG hNeg hInfinity
    hβ hMono hβA hβRN hβDerivative hβNeck hLiteral
  refine ⟨hHeight, β, hβ, hMono, hβA, hβRN, hβDerivative, hβNeck, hβNorth,
    Q, hLiteral, hOffset, C, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact exists_completedSaddleTorusAssembly_with_full_meridian Q.cylinder

end OrdinaryData
end
end TightVer401
