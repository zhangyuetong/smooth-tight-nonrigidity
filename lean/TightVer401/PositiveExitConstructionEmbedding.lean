import TightVer401.NativeSupportedEmbeddingTopology
import TightVer401.NativeCompactEmbeddingGraphDerivative
import TightVer401.PlanarGradientInverse
import TightVer401.IdentityBandPlanarSupportGradient
import TightVer401.OpenCoordinateDifferential
import TightVer401.ScalarCoordinateCalculus
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Fixed-core exit consumer: the actual Cartesian gradient of G+a*J remains
a global embedding on the original open source for sufficiently small a.
The direction J and its compact geometric support are fixed before a.
Local graph injection is derived from the actual baseline Hessian. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Actual gradient linearity for the fixed Cartesian change, on the actual
open source where the original potential is smooth. -/
theorem positiveExit_actual_gradient_linear {G J : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hJ : ContDiff ℝ ∞ J)
    {p : Coord} (hp : p ∈ U) (a : ℝ) :
    planarGradient (fun q => G q + a * J q) p =
      planarGradient G p + a • planarGradient J p := by
  have hdG := ((hG p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdJ := hJ.differentiable (by simp) p
  ext i
  change coordPartial i (fun q => G q + a * J q) p =
    coordPartial i G p + a * coordPartial i J p
  have hd := (hdG.hasFDerivAt.add (hdJ.hasFDerivAt.const_mul a)).fderiv
  change fderiv ℝ (fun q => G q + a * J q) p (Pi.single i 1) = _
  change fderiv ℝ (fun q => G q + a * J q) p =
    fderiv ℝ G p + a • fderiv ℝ J p at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, coordPartial]

/-- No gradient change occurs outside the geometric support fixed before a. -/
theorem positiveExit_actual_gradient_direction_zero {J : Coord → ℝ} {K : Set Coord}
    (hsupport : tsupport J ⊆ K) {p : Coord} (hp : p ∉ K) :
    planarGradient J p = 0 := by
  have hpJ : p ∉ tsupport J := fun h => hp (hsupport h)
  have hz : fderiv ℝ J p = 0 := fderiv_of_notMem_tsupport ℝ hpJ
  ext i
  change fderiv ℝ J p (Pi.single i 1 : Coord) = 0
  rw [hz, ContinuousLinearMap.zero_apply]

/-- Actual compactly supported Cartesian exit directions have a global
source-gradient embedding threshold. Neither parameter-graph injection nor
an inverse or desired perturbed embedding is supplied as an assumption. -/
theorem positiveExit_actual_gradient_embedding_threshold {G J : Coord → ℝ}
    {U K : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hJ : ContDiff ℝ ∞ J)
    (hemb : Topology.IsEmbedding (fun p : U => planarGradient G p.val))
    (hdet : ∀ p ∈ U, (planarHessian G p).det ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) (hsupport : tsupport J ⊆ K) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      Topology.IsEmbedding (fun p : U => planarGradient (fun q => G q + a * J q) p.val) := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let X : U → Coord := fun p => planarGradient G p.val
  let Y : U → Coord := fun p => planarGradient J p.val
  let F : U × ℝ → Coord := fun z => X z.1 + z.2 • Y z.1
  let S : Set U := (Subtype.val : U → Coord) ⁻¹' K
  have hgradG := planarGradient_contDiffOn hG hU
  have hgradJ : ContDiff ℝ ∞ (planarGradient J) :=
    contDiffOn_univ.mp (planarGradient_contDiffOn hJ.contDiffOn isOpen_univ)
  have hX : Continuous X := continuousOn_iff_continuous_restrict.mp hgradG.continuousOn
  have hY : Continuous Y := hgradJ.continuous.comp continuous_subtype_val
  have hF : Continuous F := (hX.comp continuous_fst).add
    (continuous_snd.smul (hY.comp continuous_fst))
  have hS : IsCompact S := by
    apply Subtype.isCompact_iff.mpr
    have heq : (Subtype.val : U → Coord) '' S = K := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hp
        exact ⟨⟨p, hKU hp⟩, hp, rfl⟩
    rw [heq]
    exact hK
  have hfixed : ∀ p ∉ S, ∀ a : ℝ, F (p, a) = X p := by
    intro p hp a
    have hz : Y p = 0 := positiveExit_actual_gradient_direction_zero hsupport hp
    simp only [F, hz, smul_zero, add_zero]
  have hgraph : ∀ p : U, ∃ V ∈ 𝓝 (p, (0 : ℝ)),
      InjOn (fun z : U × ℝ => (z.2, F z)) V := by
    intro p
    have hlocalG : ContDiffAt ℝ ∞ (planarGradient G) p.val :=
      (hgradG p.val p.property).contDiffAt (hU.mem_nhds p.property)
    have hlocalJ : ContDiffAt ℝ ∞ (planarGradient J) p.val := hgradJ.contDiffAt
    have hi := planarGradient_differential_injective hG hU p.property (hdet _ p.property)
    obtain ⟨V, hV, hlocal⟩ := nativeCompactEmbeddingGraph_exists_local_injOn hlocalG hlocalJ hi
    let lift : U × ℝ → Coord × ℝ := fun z => (z.1.val, z.2)
    have hlift : Continuous lift := continuous_subtype_val.prodMap continuous_id
    have hilift : Function.Injective lift := by
      intro z y heq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq)
      · have hh := congrArg (fun t : Coord × ℝ => t.2) heq
        exact hh
    refine ⟨lift ⁻¹' V, hlift.continuousAt.preimage_mem_nhds hV, ?_⟩
    intro z hz y hy heq
    apply hilift
    apply hlocal hz hy
    exact heq
  obtain ⟨δ, hδ, hembed⟩ := nativeSupportedEmbedding_exists_parameter_threshold
    hemb hF (fun p => by simp [F, X]) hS hfixed hgraph
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hactual : (fun p : U => planarGradient (fun q => G q + a * J q) p.val) =
      (fun p : U => F (p, a)) := by
    funext p
    exact positiveExit_actual_gradient_linear hU hG hJ p.property a
  rw [hactual]
  exact hembed a ha

/-- Nonvanishing of the actual perturbed Hessian supplies the actual smooth
local inverses once the small-amplitude global embedding has been obtained.
The global chart assembly can reuse the retained regular coordinate-image
constructor; no inverse witness is needed at a point. -/
theorem positiveExit_actual_gradient_local_inverse {G J : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hJ : ContDiff ℝ ∞ J)
    (a : ℝ) (hdet : ∀ p ∈ U, (planarHessian (fun q => G q + a * J q) p).det ≠ 0)
    {p : Coord} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧
      (e : Coord → Coord) = planarGradient (fun q => G q + a * J q) ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hGa : ContDiffOn ℝ ∞ (fun q => G q + a * J q) U :=
    hG.add (contDiffOn_const.mul hJ.contDiffOn)
  exact planarGradient_exists_smooth_local_inverse hGa hU hdet hp

/-- Once the actual perturbed Hessian is nonzero and the small-parameter
embedding has been obtained, the retained coordinate-image construction gives
an actual global inverse of that SAME perturbed gradient on its entire image. -/
theorem positiveExit_actual_gradient_global_inverse {G J : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hne : U.Nonempty) (hG : ContDiffOn ℝ ∞ G U)
    (hJ : ContDiff ℝ ∞ J) (a : ℝ)
    (hdet : ∀ p ∈ U, (planarHessian (fun q => G q + a * J q) p).det ≠ 0)
    (hemb : Topology.IsEmbedding
      (fun p : U => planarGradient (fun q => G q + a * J q) p.val)) :
    ∃ e : OpenPartialHomeomorph U Coord,
      e.source = univ ∧
      e.target = range (fun p : U => planarGradient (fun q => G q + a * J q) p.val) ∧
      (e : U → Coord) = (fun p : U => planarGradient (fun q => G q + a * J q) p.val) ∧
      ContDiffOn ℝ ∞ (fun q => (e.symm q).val) e.target := by
  let V : TopologicalSpace.Opens Coord := ⟨U, hU⟩
  obtain ⟨p0, hp0⟩ := hne
  letI : Nonempty V := ⟨⟨p0, hp0⟩⟩
  let Ga : Coord → ℝ := fun q => G q + a * J q
  let P : V → Coord := fun p => planarGradient Ga p.val
  have hGa : ContDiffOn ℝ ∞ Ga U := hG.add (contDiffOn_const.mul hJ.contDiffOn)
  have hgrad := planarGradient_contDiffOn hGa hU
  have hP : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ P := by
    intro p
    have hraw := (hgrad p.val p.property).contDiffAt (hU.mem_nhds p.property)
    exact hraw.contMDiffAt.comp p (contMDiff_subtype_val (U := V) (n := ∞) p)
  have hiP (p : V) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) P p) := by
    have hraw := ((hgrad p.val p.property).contDiffAt (hU.mem_nhds p.property)).differentiableAt (by simp)
    have hval : MDifferentiableAt 𝓘(ℝ, Coord) 𝓘(ℝ, Coord)
        (Subtype.val : V → Coord) p :=
      (contMDiff_subtype_val (I := 𝓘(ℝ, Coord)) (U := V) (n := ∞) p).mdifferentiableAt (by simp)
    have hres : (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) P p : Coord →L[ℝ] Coord) =
        (fderiv ℝ (planarGradient Ga) p.val).comp (openCoordinateInclusionDifferential V p) :=
      (hraw.hasFDerivAt.hasMFDerivAt.comp p hval.hasMFDerivAt).mfderiv
    rw [openCoordinate_inclusion_derivative, ContinuousLinearMap.comp_id] at hres
    rw [hres]
    exact planarGradient_differential_injective hGa hU p.property (hdet _ p.property)
  have hPi : Function.Injective P := hemb.injective
  obtain ⟨e, heS, heT, heP, heI⟩ := identityBandPlanarSupport_regular_coordinate_image hP hiP hPi
  refine ⟨e, heS, heT, heP, ?_⟩
  exact ((contMDiff_subtype_val (U := V) (n := ∞)).comp_contMDiffOn heI).contDiffOn

end
end TightVer401