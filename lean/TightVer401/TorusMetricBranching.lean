import TightVer401.ProtectedTorusBending
import TightVer401.NativeProductPlaneMetricBundleApplications

/-! Exact branching for the SAME literal protected torus bending field.
The native quadratic identity and genuine smooth metric construction are reused.
The torus map, its baseline immersion, and a point outside the protected support
image remain actual construction inputs. No embedding, tightness, or image
noncongruence conclusion is assumed or asserted by this metric application. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance : IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

/-- The proved protected extension is an actual native bending of the same F. -/
theorem protectedTorus_isNativeBending {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p)) :
    nativeProductIsBending F (protectedTorusBendingField e A Y) := by
  obtain ⟨hZ, hstrain, _, _, _⟩ := protectedTorus_compact_nonzero_bending
    hX hY hcompact hnonzero e hsupport he A F hplacement
  exact ⟨hZ, hstrain⟩

/-- Actual native induced forms of the literal opposite branches agree exactly. -/
theorem protectedTorus_exact_sign_pair {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (ε : ℝ) (p : NonrigidTorusSource) (v z : ℝ × ℝ) :
    nativeProductInducedForm (F + ε • protectedTorusBendingField e A Y) p v z =
      nativeProductInducedForm (F - ε • protectedTorusBendingField e A Y) p v z := by
  exact nativeProduct_exact_sign_pair hF
    (nativeProduct_bending_const_smul hF
      (protectedTorus_isNativeBending hX hY hcompact hnonzero e hsupport he A F hplacement)
      ε) p v z

/-- The common form is the actual baseline form plus the nonnegative quadratic
contribution of the SAME protected field. -/
theorem protectedTorus_bending_common_metric {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (ε : ℝ) (p : NonrigidTorusSource) (v z : ℝ × ℝ) :
    nativeProductInducedForm (F + ε • protectedTorusBendingField e A Y) p v z =
      nativeProductInducedForm F p v z +
        ε ^ 2 * nativeProductInducedForm (protectedTorusBendingField e A Y) p v z :=
  nativeProduct_bending_common_metric hF
    (protectedTorus_isNativeBending hX hY hcompact hnonzero e hsupport he A F hplacement)
    ε p v z

/-- A genuine common smooth positive Plane metric follows from the actual
baseline native immersion for every real amplitude. -/
theorem protectedTorus_bending_common_smooth_metric {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (ε : ℝ) :
    let Z := protectedTorusBendingField e A Y
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : NonrigidTorusSource => TangentSpace planeModel p),
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F + ε • Z) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F - ε • Z) ∧
      (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
        g.inner p v z = inducedForm (F + ε • Z) p v z ∧
        g.inner p v z = inducedForm (F - ε • Z) p v z) ∧
      (∀ p : NonrigidTorusSource,
        Function.Injective (surfaceDifferential (F + ε • Z) p) ∧
        Function.Injective (surfaceDifferential (F - ε • Z) p)) :=
  nativeProductPlane_bending_scaled_common_smooth_metric hF
    (protectedTorus_isNativeBending hX hY hcompact hnonzero e hsupport he A F hplacement)
    ε hinj

/-- Compact protection produces an explicit open agreement set. Its nonemptiness
requires only an actual point outside the compact support image. -/
theorem protectedTorus_bending_open_agreement {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (ε : ℝ)
    (hout : ∃ q, q ∉ e '' tsupport Y) :
    let U := (e '' tsupport Y)ᶜ
    IsOpen U ∧ U.Nonempty ∧
      EqOn (F + ε • protectedTorusBendingField e A Y) F U ∧
      EqOn (F - ε • protectedTorusBendingField e A Y) F U := by
  let Z := protectedTorusBendingField e A Y
  have hzero : ∀ q ∈ (e '' tsupport Y)ᶜ, Z q = 0 := by
    intro q hq
    by_contra hn
    exact hq (protectedTorusBendingField_tsupport e A hcompact hsupport
      (subset_tsupport Z hn))
  refine ⟨(protectedTorusBendingField_support_image_isCompact e hcompact hsupport).isClosed.isOpen_compl,
    hout, ?_, ?_⟩
  · intro q hq
    change F q + ε • Z q = F q
    rw [hzero q hq, smul_zero, add_zero]
  · intro q hq
    change F q - ε • Z q = F q
    rw [hzero q hq, smul_zero, sub_zero]

/-- Nonzero amplitudes separate the actual parametrized maps. Image
noncongruence is a later conclusion requiring marking and rigidity. -/
theorem protectedTorus_bending_sign_separation {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (hsupport : tsupport Y ⊆ e.source)
    (hnonzero : ∃ p, Y p ≠ 0) (F : NonrigidTorusSource → Ambient)
    {ε : ℝ} (hε : ε ≠ 0) :
    F + ε • protectedTorusBendingField e A Y ≠
      F - ε • protectedTorusBendingField e A Y := by
  intro heq
  obtain ⟨p, hp⟩ := protectedTorusBendingField_nonzero e A hsupport hnonzero
  have he' : F p + ε • protectedTorusBendingField e A Y p =
      F p + -(ε • protectedTorusBendingField e A Y p) := by
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]
      using congrFun heq p
  have ha := add_left_cancel he'
  have hz : (ε + ε) • protectedTorusBendingField e A Y p = 0 := by
    rw [add_smul]
    exact (congrArg (fun u : Ambient => u + ε • protectedTorusBendingField e A Y p) ha).trans
      (neg_add_cancel _)
  have hscalar : ε + ε ≠ 0 := by intro h; apply hε; linarith
  exact hp ((smul_eq_zero.mp hz).resolve_left hscalar)

/-- Same-object metric branching data for the final image-separation consumer.
All forms and all branch maps use the one literal Z and amplitude ε. -/
theorem protectedTorus_metric_branching {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p))
    (hout : ∃ q, q ∉ e '' tsupport Y) {ε : ℝ} (hε : ε ≠ 0) :
    let Z := protectedTorusBendingField e A Y
    let U := (e '' tsupport Y)ᶜ
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : NonrigidTorusSource => TangentSpace planeModel p),
      ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F + ε • Z) ∧
      ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F - ε • Z) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F + ε • Z) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F - ε • Z) ∧
      (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
        g.inner p v z = inducedForm (F + ε • Z) p v z ∧
        g.inner p v z = inducedForm (F - ε • Z) p v z) ∧
      (∀ p (v z : ℝ × ℝ),
        nativeProductInducedForm (F + ε • Z) p v z =
          nativeProductInducedForm (F - ε • Z) p v z ∧
        nativeProductInducedForm (F + ε • Z) p v z =
          nativeProductInducedForm F p v z + ε ^ 2 * nativeProductInducedForm Z p v z) ∧
      (∀ p (v : ℝ × ℝ), v ≠ 0 →
        0 < nativeProductInducedForm (F + ε • Z) p v v) ∧
      (∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F + ε • Z) p) ∧
        Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F - ε • Z) p)) ∧
      (IsOpen U ∧ U.Nonempty ∧ EqOn (F + ε • Z) F U ∧ EqOn (F - ε • Z) F U) ∧
      F + ε • Z ≠ F - ε • Z := by
  let Z := protectedTorusBendingField e A Y
  have hZ : nativeProductIsBending F Z :=
    protectedTorus_isNativeBending hX hY hcompact hnonzero e hsupport he A F hplacement
  have hεZ := nativeProduct_bending_const_smul hF hZ ε
  have hplus := hF.add hεZ.1
  have hminus := hF.sub hεZ.1
  have hip := nativeProduct_bending_branch_immersion hF hZ ε hinj
  have him := nativeProduct_opposite_branch_immersion hF hεZ hip
  obtain ⟨g, hplusPlane, hminusPlane, hg, _⟩ :=
    nativeProductPlane_bending_scaled_common_smooth_metric hF hZ ε hinj
  refine ⟨g, hplus, hminus, hplusPlane, hminusPlane, hg, ?_, ?_,
    (fun p => ⟨hip p, him p⟩),
    protectedTorus_bending_open_agreement e A hcompact hsupport F ε hout,
    protectedTorus_bending_sign_separation e A hsupport hnonzero F hε⟩
  · intro p v z
    exact ⟨nativeProduct_exact_sign_pair hF hεZ p v z,
      nativeProduct_bending_common_metric hF hZ ε p v z⟩
  · intro p v hv
    apply real_inner_self_pos.mpr
    intro hz
    apply hv
    apply hip p
    simpa only [map_zero] using hz

end
end TightVer401
