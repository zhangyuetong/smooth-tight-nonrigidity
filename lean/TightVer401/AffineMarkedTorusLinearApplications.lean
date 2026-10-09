import TightVer401.AffineMarkedTorusLinear
import TightVer401.NativeProductPlaneMetricBundleApplications

/-! Actual native differential, bending and new induced metric of the
affinely marked pair B X plus/minus t B inverse transpose Y.

Inputs are actual native smoothness, zero strain and baseline immersion.
Both branch immersions and one genuine smooth positive metric are derived.
Its explicit quadratic form is computed from B DX and C DY. The metric
need not equal the original induced metric. Embedding and affine curvature
covariance are separate applications.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open _root_.Manifold Bundle OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

def affineMarkedTorusLinearBase (X : M → Ambient) : M → Ambient :=
  fun p => torusAffineMarker (X p)

def affineMarkedTorusLinearBending (Y : M → Ambient) : M → Ambient :=
  fun p => torusAffineMarkerContra (Y p)

/-- Actual chain rule, stated with the native manifold differential. -/
theorem affineMarkedTorusLinear_mfderiv (A : Ambient →L[ℝ] Ambient)
    {F : M → Ambient} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) F p) :
    mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fun q => A (F q)) p =
      A.comp (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p) := by
  have hA : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞ A := A.contMDiff
  change mfderiv nativeProductModel 𝓘(ℝ, Ambient) (A ∘ F) p = _
  rw [mfderiv_comp p ((hA (F p)).mdifferentiableAt (by simp)) hF,
    mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]

/-- Evaluated actual native derivative, with its product tangent model explicit. -/
theorem affineMarkedTorusLinearBase_mfderiv_apply {X : M → Ambient} {p : M}
    (hX : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) X p) (v : ℝ × ℝ) :
    mfderiv nativeProductModel 𝓘(ℝ, Ambient) (affineMarkedTorusLinearBase X) p v =
      torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) := by
  have hd := affineMarkedTorusLinear_mfderiv torusAffineMarkerLinearEquiv.toContinuousLinearMap hX
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] Ambient => A v) hd

theorem affineMarkedTorusLinearBending_mfderiv_apply {Y : M → Ambient} {p : M}
    (hY : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) Y p) (v : ℝ × ℝ) :
    mfderiv nativeProductModel 𝓘(ℝ, Ambient) (affineMarkedTorusLinearBending Y) p v =
      torusAffineMarkerContra (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y p v) := by
  have hd := affineMarkedTorusLinear_mfderiv torusAffineMarkerContraLinearEquiv.toContinuousLinearMap hY
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] Ambient => A v) hd

theorem affineMarkedTorusLinearBase_contMDiff {X : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (affineMarkedTorusLinearBase X) := by
  have hB : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞
      torusAffineMarkerLinearEquiv.toContinuousLinearMap :=
    torusAffineMarkerLinearEquiv.toContinuousLinearMap.contMDiff
  exact hB.comp hX

theorem affineMarkedTorusLinearBending_contMDiff {Y : M → Ambient}
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (affineMarkedTorusLinearBending Y) := by
  have hC : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞
      torusAffineMarkerContraLinearEquiv.toContinuousLinearMap :=
    torusAffineMarkerContraLinearEquiv.toContinuousLinearMap.contMDiff
  exact hC.comp hY

theorem affineMarkedTorusLinear_strain {X Y : M → Ambient} {p : M}
    (hX : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) X p)
    (hY : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) Y p) (v w : ℝ × ℝ) :
    nativeProductLinearMetricForm (affineMarkedTorusLinearBase X)
      (affineMarkedTorusLinearBending Y) p v w = nativeProductLinearMetricForm X Y p v w := by
  have hbx a := affineMarkedTorusLinearBase_mfderiv_apply hX a
  have hcy a := affineMarkedTorusLinearBending_mfderiv_apply hY a
  have he0 := congrArg₂ (fun a b : Ambient => inner ℝ a b) (hbx v) (hcy w)
  have he1 := congrArg₂ (fun a b : Ambient => inner ℝ a b) (hcy v) (hbx w)
  exact (congrArg₂ (fun a b : ℝ => a + b) he0 he1).trans
    (torusAffineMarker_strain_transport
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p w)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y p v)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y p w))

theorem affineMarkedTorusLinear_isBending {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : nativeProductIsBending X Y) :
    nativeProductIsBending (affineMarkedTorusLinearBase X) (affineMarkedTorusLinearBending Y) := by
  refine ⟨affineMarkedTorusLinearBending_contMDiff hY.1, ?_⟩
  intro p v w
  rw [affineMarkedTorusLinear_strain ((hX p).mdifferentiableAt (by simp))
    ((hY.1 p).mdifferentiableAt (by simp))]
  exact hY.2 p v w

theorem affineMarkedTorusLinearBase_immersion {X : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) :
    ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (affineMarkedTorusLinearBase X) p) := by
  intro p v w he
  have hd := affineMarkedTorusLinearBase_mfderiv_apply ((hX p).mdifferentiableAt (by simp))
  exact hinj p (torusAffineMarker_injective ((hd v).symm.trans (he.trans (hd w))))

theorem affineMarkedTorusLinear_branch_immersion {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : nativeProductIsBending X Y) (t : ℝ)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) :
    ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p) ∧
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y) p) := by
  have hb := affineMarkedTorusLinearBase_contMDiff hX
  have hc := affineMarkedTorusLinear_isBending hX hY
  have hi := affineMarkedTorusLinearBase_immersion hX hinj
  have hp := nativeProduct_bending_branch_immersion hb hc t hi
  have hm := nativeProduct_bending_branch_immersion hb hc (-t) hi
  have he : affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y =
      affineMarkedTorusLinearBase X + (-t) • affineMarkedTorusLinearBending Y := by
    simp only [sub_eq_add_neg, neg_smul]
  intro p
  rw [he]
  exact ⟨hp p, hm p⟩

/-- New quadratic form of the marked pair, explicitly using B and C. -/
def affineMarkedTorusLinearQuadraticForm (X Y : M → Ambient) (t : ℝ)
    (p : M) (v w : ℝ × ℝ) : ℝ :=
  inner ℝ (torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v))
      (torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p w)) +
    t^2 * inner ℝ (torusAffineMarkerContra (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y p v))
      (torusAffineMarkerContra (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y p w))

theorem affineMarkedTorusLinear_common_native_metric {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : nativeProductIsBending X Y) (t : ℝ) (p : M) (v w : ℝ × ℝ) :
    nativeProductInducedForm
        (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p v w =
      affineMarkedTorusLinearQuadraticForm X Y t p v w := by
  rw [nativeProduct_bending_common_metric (affineMarkedTorusLinearBase_contMDiff hX)
    (affineMarkedTorusLinear_isBending hX hY)]
  have hbx a := affineMarkedTorusLinearBase_mfderiv_apply ((hX p).mdifferentiableAt (by simp)) a
  have hcy a := affineMarkedTorusLinearBending_mfderiv_apply ((hY.1 p).mdifferentiableAt (by simp)) a
  have he0 := congrArg₂ (fun a b : Ambient => inner ℝ a b) (hbx v) (hbx w)
  have he1 := congrArg₂ (fun a b : Ambient => inner ℝ a b) (hcy v) (hcy w)
  exact congrArg₂ (fun a b : ℝ => a + t^2 * b) he0 he1

theorem affineMarkedTorusLinear_opposite_native_forms {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : nativeProductIsBending X Y) (t : ℝ) (p : M) (v w : ℝ × ℝ) :
    nativeProductInducedForm
        (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p v w =
      nativeProductInducedForm
        (affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y) p v w :=
  nativeProduct_exact_sign_pair (affineMarkedTorusLinearBase_contMDiff hX)
    (nativeProduct_bending_const_smul (affineMarkedTorusLinearBase_contMDiff hX)
      (affineMarkedTorusLinear_isBending hX hY) t) p v w

theorem affineMarkedTorusLinearBending_tsupport (Y : M → Ambient) :
    tsupport (affineMarkedTorusLinearBending Y) = tsupport Y :=
  torusAffineMarkerContra_tsupport Y

theorem affineMarkedTorusLinearBending_nonzero_iff (Y : M → Ambient) :
    (∃ p, affineMarkedTorusLinearBending Y p ≠ 0) ↔ ∃ p, Y p ≠ 0 :=
  torusAffineMarkerContra_nonzero_iff Y

local instance affineMarkedTorusLinearPlaneCharts : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M
local instance affineMarkedTorusLinearPlaneManifold [IsManifold nativeProductModel ∞ M] :
    IsManifold planeModel ∞ M := nativeProductPlane_isManifold M

/-- Construct the new genuine common smooth positive metric from baseline
immersion, for every amplitude. Its displayed value is the marked quadratic
form, and both actual branch differential injections are derived. -/
theorem affineMarkedTorusLinear_common_smooth_metric
    [IsManifold nativeProductModel ∞ M] {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : nativeProductIsBending X Y) (t : ℝ)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) :
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : M => TangentSpace planeModel p),
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞
        (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞
        (affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y) ∧
      (∀ (p : M) (v w : TangentSpace planeModel p),
        g.inner p v w = inducedForm
          (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p v w ∧
        g.inner p v w = inducedForm
          (affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y) p v w) ∧
      (∀ p : M, Function.Injective (surfaceDifferential
          (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p) ∧
        Function.Injective (surfaceDifferential
          (affineMarkedTorusLinearBase X - t • affineMarkedTorusLinearBending Y) p)) ∧
      (∀ (p : M) (v w : ℝ × ℝ),
        g.inner p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
          affineMarkedTorusLinearQuadraticForm X Y t p v w) := by
  have hb := affineMarkedTorusLinearBase_contMDiff hX
  have hc := affineMarkedTorusLinear_isBending hX hY
  obtain ⟨g, hp, hm, hg, hi⟩ := nativeProductPlane_bending_scaled_common_smooth_metric
    hb hc t (affineMarkedTorusLinearBase_immersion hX hinj)
  refine ⟨g, hp, hm, hg, hi, ?_⟩
  intro p v w
  have ht : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (t • affineMarkedTorusLinearBending Y) :=
    (nativeProduct_bending_const_smul hb hc t).1
  calc
    g.inner p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
        inducedForm (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y)
          p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) := (hg p _ _).1
    _ = nativeProductInducedForm
        (affineMarkedTorusLinearBase X + t • affineMarkedTorusLinearBending Y) p v w :=
      nativeProductPlane_inducedForm (((hb.add ht) p).mdifferentiableAt (by simp)) v w
    _ = affineMarkedTorusLinearQuadraticForm X Y t p v w :=
      affineMarkedTorusLinear_common_native_metric hX hY t p v w

end
end
end TightVer401
