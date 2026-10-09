import TightVer401.NativeProductPlaneAtlas

/-! Pullback identities for actual manifold derivatives and OpenAI metric forms. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.ClosedSurfaceR4

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
local instance : ChartedSpace Plane M := nativeProductPlaneChartedSpace M
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Chain rule for the atlas-changing identity gives the actual transported differential. -/
theorem nativeProductPlane_mfderiv {F : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p) :
    surfaceDifferential F p =
      (mfderiv nativeProductModel 𝓘(ℝ, V) F p).comp
        nativeProductPlaneEquiv.symm.toContinuousLinearMap := by
  have h := mfderiv_comp p hF (nativeProductPlane_inverse_hasMFDerivAt M p).mdifferentiableAt
  rw [(nativeProductPlane_inverse_hasMFDerivAt M p).mfderiv] at h
  exact h

theorem nativeProductPlane_mfderiv_apply {F : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p) (v : ℝ × ℝ) :
    surfaceDifferential F p (nativeProductPlaneEquiv v) =
      mfderiv nativeProductModel 𝓘(ℝ, V) F p v := by
  rw [nativeProductPlane_mfderiv hF]
  change (mfderiv nativeProductModel 𝓘(ℝ, V) F p)
    (nativeProductPlaneEquiv.symm (nativeProductPlaneEquiv v)) = _
  rw [nativeProductPlaneEquiv.symm_apply_apply]

/-- Actual immersion regularity is equivalent in the two tangent models. -/
theorem nativeProductPlane_immersion_iff {F : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p) :
    Function.Injective (surfaceDifferential F p) ↔
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p) := by
  rw [nativeProductPlane_mfderiv hF]
  constructor
  · intro h v w hvw
    have h' := h (show (mfderiv nativeProductModel 𝓘(ℝ, V) F p).comp
        nativeProductPlaneEquiv.symm.toContinuousLinearMap (nativeProductPlaneEquiv v) =
      (mfderiv nativeProductModel 𝓘(ℝ, V) F p).comp
        nativeProductPlaneEquiv.symm.toContinuousLinearMap (nativeProductPlaneEquiv w) by
      change (mfderiv nativeProductModel 𝓘(ℝ, V) F p)
          (nativeProductPlaneEquiv.symm (nativeProductPlaneEquiv v)) =
        (mfderiv nativeProductModel 𝓘(ℝ, V) F p)
          (nativeProductPlaneEquiv.symm (nativeProductPlaneEquiv w))
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hvw)
    exact nativeProductPlaneEquiv.injective h'
  · exact fun h => h.comp nativeProductPlaneEquiv.symm.injective

end

section Forms
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
local instance : ChartedSpace Plane M := nativeProductPlaneChartedSpace M
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Native induced pairing; its differential is native mfderiv, not an abstract supplied map. -/
def nativeProductInducedForm (F : M → V) (p : M) (v w : ℝ × ℝ) : ℝ :=
  @inner ℝ V _ (mfderiv nativeProductModel 𝓘(ℝ, V) F p v : V)
    (mfderiv nativeProductModel 𝓘(ℝ, V) F p w : V)

def nativeProductLinearMetricForm (F Y : M → V) (p : M) (v w : ℝ × ℝ) : ℝ :=
  @inner ℝ V _ (mfderiv nativeProductModel 𝓘(ℝ, V) F p v : V)
    (mfderiv nativeProductModel 𝓘(ℝ, V) Y p w : V) +
  @inner ℝ V _ (mfderiv nativeProductModel 𝓘(ℝ, V) Y p v : V)
    (mfderiv nativeProductModel 𝓘(ℝ, V) F p w : V)

theorem nativeProductPlane_inducedForm {F : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p) (v w : ℝ × ℝ) :
    inducedForm F p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      nativeProductInducedForm F p v w := by
  simp only [inducedForm, nativeProductInducedForm, nativeProductPlane_mfderiv_apply hF]

theorem nativeProductPlane_linearMetricForm {F Y : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p)
    (hY : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) Y p) (v w : ℝ × ℝ) :
    linearMetricForm F Y p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      nativeProductLinearMetricForm F Y p v w := by
  simp only [linearMetricForm, nativeProductLinearMetricForm,
    nativeProductPlane_mfderiv_apply hF, nativeProductPlane_mfderiv_apply hY]

/-- Zero native strain is exactly zero OpenAI strain, for the transported tangent vectors. -/
theorem nativeProductPlane_zero_strain_iff {F Y : M → V} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p)
    (hY : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) Y p) :
    (∀ v w, linearMetricForm F Y p v w = 0) ↔
      (∀ v w, nativeProductLinearMetricForm F Y p v w = 0) := by
  constructor
  · intro h v w
    rw [← nativeProductPlane_linearMetricForm hF hY]
    exact h _ _
  · intro h v w
    obtain ⟨v, rfl⟩ := nativeProductPlaneEquiv.surjective v
    obtain ⟨w, rfl⟩ := nativeProductPlaneEquiv.surjective w
    rw [nativeProductPlane_linearMetricForm hF hY]
    exact h _ _

end Forms
end
end TightVer401



