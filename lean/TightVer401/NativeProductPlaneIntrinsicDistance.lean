import TightVer401.NativeProductPlaneIntrinsicDistanceCurves

/-! Intrinsic extended-distance transport for the actual induced metrics.

Ordinary inputs are a native smooth manifold and an actual smooth immersion
`F` into a real inner product space. The two distances below install the
proved induced tangent metrics and invoke the existing
`Manifold.riemannianEDist`: the infimum of actual differential-norm integrals
over the same continuous `Path x y` and its C1 manifold admissibility proof.

The atlas identity preserves C1 admissibility, while the proved incoming
differential and genuine metric norm transport preserve the actual path
integrals. Consequently the intrinsic extended distances agree. No ambient
chordal distance, compatible distance instance, connectedness, completeness,
compactness or actual torus is an input. This theorem does not assert finite
distance between distinct connected components or construct a global torus.
-/
open Manifold Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
  [IsManifold nativeProductModel ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local instance nativeProductPlaneIntrinsicDistanceChartedSpace : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M
local instance nativeProductPlaneIntrinsicDistanceIsManifold : IsManifold planeModel ∞ M :=
  nativeProductPlane_isManifold M

attribute [local instance] Measure.Subtype.measureSpace

/-- Existing intrinsic distance with the actual native induced tangent metric. -/
def nativeProductImmersionEDist (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun p : M => TangentSpace nativeProductModel p) :=
    nativeProductImmersionRiemannianBundle F hF hinj
  Manifold.riemannianEDist nativeProductModel x y

/-- Existing intrinsic distance with the actual transported Plane induced metric. -/
def nativeProductPlaneImmersionEDist (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun p : M => TangentSpace planeModel p) :=
    nativeProductPlaneImmersionRiemannianBundle F hF hinj
  Manifold.riemannianEDist planeModel x y

/-- The very same continuous path, including its endpoint proofs, is C1 in
one atlas exactly when it is C1 in the other. -/
theorem nativeProductPlane_path_contMDiff_iff {x y : M} (γ : Path x y) :
    ContMDiff (𝓡∂ 1) planeModel 1 (γ : unitInterval → M) ↔
      ContMDiff (𝓡∂ 1) nativeProductModel 1 (γ : unitInterval → M) :=
  nativeProductPlane_incoming_contMDiff_iff (n := 1) (by simp) (γ : unitInterval → M)

/-- Concrete native piecewise C1 admissibility: a continuous real curve on the
closed interval has an ordered finite subdivision with genuine C1 smoothness
on each closed piece. Repeated subdivision points permit a constant interval. -/
def nativeProductPiecewiseC1 (c : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn c (Icc a b) ∧
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
      t 0 = a ∧ t (Fin.last n) = b ∧ Monotone t ∧
        ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) nativeProductModel 1 c
          (Icc (t i.castSucc) (t i.succ))

/-- The same finite subdivision and continuous curve, using Plane C1 smoothness. -/
def nativeProductPlanePiecewiseC1 (c : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn c (Icc a b) ∧
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
      t 0 = a ∧ t (Fin.last n) = b ∧ Monotone t ∧
        ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) planeModel 1 c
          (Icc (t i.castSucc) (t i.succ))

/-- Atlas transport preserves the actual finite-subdivision witnesses. -/
theorem nativeProductPlane_piecewiseC1_iff (c : ℝ → M) (a b : ℝ) :
    nativeProductPlanePiecewiseC1 c a b ↔ nativeProductPiecewiseC1 c a b := by
  constructor
  · rintro ⟨hab, hc, n, t, ha, hb, ht, hs⟩
    refine ⟨hab, hc, n, t, ha, hb, ht, ?_⟩
    intro i
    exact (nativeProductPlane_incoming_contMDiffOn_iff (n := 1) (by simp) c
      (Icc (t i.castSucc) (t i.succ))).mp (hs i)
  · rintro ⟨hab, hc, n, t, ha, hb, ht, hs⟩
    refine ⟨hab, hc, n, t, ha, hb, ht, ?_⟩
    intro i
    exact (nativeProductPlane_incoming_contMDiffOn_iff (n := 1) (by simp) c
      (Icc (t i.castSucc) (t i.succ))).mpr (hs i)

/-- Transport the existing C1-path infimum using actual path integral equality.
Both sides use the constructed induced metrics rather than an ambient distance. -/
theorem nativeProductPlaneImmersionEDist_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (x y : M) :
    nativeProductImmersionEDist F hF hinj x y =
      nativeProductPlaneImmersionEDist F hF hinj x y := by
  have hlen (γ : Path x y) :
      (letI : RiemannianBundle (fun p : M => TangentSpace nativeProductModel p) :=
        nativeProductImmersionRiemannianBundle F hF hinj
       ∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) nativeProductModel γ t 1‖ₑ) =
      (letI : RiemannianBundle (fun p : M => TangentSpace planeModel p) :=
        nativeProductPlaneImmersionRiemannianBundle F hF hinj
       ∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) planeModel γ t 1‖ₑ) :=
    nativeProductPlaneImmersion_pathIntegral_transport F hF hinj (γ : unitInterval → M)
  unfold nativeProductImmersionEDist nativeProductPlaneImmersionEDist
  rw [Manifold.riemannianEDist, Manifold.riemannianEDist]
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun hγ => ?_
    have hn := (nativeProductPlane_path_contMDiff_iff γ).mp hγ
    exact (iInf_le_of_le γ (iInf_le_of_le hn le_rfl)).trans_eq (hlen γ)
  · refine le_iInf fun γ => le_iInf fun hγ => ?_
    have hp := (nativeProductPlane_path_contMDiff_iff γ).mpr hγ
    exact (iInf_le_of_le γ (iInf_le_of_le hp le_rfl)).trans_eq (hlen γ).symm

end
end
end TightVer401
