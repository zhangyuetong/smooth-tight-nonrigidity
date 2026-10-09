import TightVer401.ClassicalEmbeddedReparam
import TightVer401.TorusNativeCurvatureReparamConnection
import TightVer401.TorusRigidCurvatureConnection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Actual entire positive-image transport and a conditional marked-image
noncongruence consumer. The original marker stabilizer remains an ordinary
producer hypothesis. No original torus, marking or pair existence is granted. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Ambient affine isometries preserve actual native smooth embedded immersions.
Smoothness, regular differential and topological embedding are derived. -/
theorem nativeTorusSmoothEmbedding_affineIsometry
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) {X : NonrigidTorusSource → Ambient}
    (hX : NativeTorusSmoothEmbedding X) : NativeTorusSmoothEmbedding (A ∘ X) := by
  let O := A.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hOapply (x : Ambient) : O x = A.linearIsometryEquiv x := rfl
  have hfun : A ∘ X = fun p => O (X p) + A 0 := by
    funext p
    rw [hOapply]
    simpa only [Function.comp_apply, vadd_eq_add, add_zero] using
      A.map_vadd (0 : Ambient) (X p)
  refine ⟨?_, ?_, A.toHomeomorph.isEmbedding.comp hX.2.2⟩
  · rw [hfun]
    exact (O.contDiff.contMDiff.comp hX.1).add contMDiff_const
  · intro p
    have hx := (hX.1 p).mdifferentiableAt (by simp)
    have hox := O.mdifferentiableAt.comp p hx
    have hd := mfderiv_comp p O.mdifferentiableAt hx
    have hO : mfderiv 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) O (X p) = O := by
      rw [mfderiv_eq_fderiv]
      exact O.fderiv
    rw [hO] at hd
    have hadd := mfderiv_add hox
      (mdifferentiableAt_const (I := nativeProductModel) (c := A 0) (x := p))
    have hder : mfderiv nativeProductModel 𝓘(ℝ, Ambient) (A ∘ X) p =
        O.comp (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p) := by
      rw [hfun]
      calc
        _ = mfderiv nativeProductModel 𝓘(ℝ, Ambient) (O ∘ X) p := by
          simp only [mfderiv_const, add_zero] at hadd
          convert! hadd using 1
        _ = _ := hd
    rw [hder]
    exact A.linearIsometryEquiv.injective.comp (hX.2.1 p)

/-- Actual ambient congruence of smooth embedded native torus images preserves
THE ENTIRE positive-curvature images. Only the explicit classical smooth
embedded-image reparameterization claim is used; curvature transport is proved. -/
theorem nativeTorusPositiveImages_eq_of_ambient_congruence
    (background : ClassicalEmbeddedImageReparametrizationClaim)
    (X Y : NonrigidTorusSource → Ambient)
    (hX : NativeTorusSmoothEmbedding X) (hY : NativeTorusSmoothEmbedding Y)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (himage : A '' range X = range Y) :
    A '' (X '' nativeTorusPositiveRegion X) = Y '' nativeTorusPositiveRegion Y := by
  have hAX := nativeTorusSmoothEmbedding_affineIsometry A hX
  have hrange : range (A ∘ X) = range Y := by
    rw [Set.range_comp]
    exact himage
  obtain ⟨e, he, hi, hvalue⟩ :=
    classicalEmbeddedImages_reparametrize background (A ∘ X) Y hAX hY hrange
  have hfun : Y ∘ e = A ∘ X := funext hvalue
  have hK (p : NonrigidTorusSource) :
      nativeTorusChartCurvature Y (e p) = nativeTorusChartCurvature X p := by
    calc
      _ = nativeTorusChartCurvature (Y ∘ e) p :=
        (nativeTorusChartCurvature_comp_homeomorph hY.1 hY.2.1 e he hi p).symm
      _ = nativeTorusChartCurvature (A ∘ X) p := by rw [hfun]
      _ = _ := nativeTorusChartCurvature_affineIsometry A X p
  ext z
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨e p, ?_, hvalue p⟩
    change 0 < nativeTorusChartCurvature Y (e p)
    rw [hK]
    exact hp
  · rintro ⟨q, hq, hqz⟩
    obtain ⟨p, rfl⟩ := e.surjective q
    refine ⟨X p, ⟨p, ?_, rfl⟩, ?_⟩
    · change 0 < nativeTorusChartCurvature X p
      rw [← hK]
      exact hq
    · exact (hvalue p).symm.trans hqz

/-- A common actual positive image with trivial ambient stabilizer promotes
range inequality to ImageNoncongruent. The stabilizer is an ORIGINAL marker
producer input, not an externally granted statement. -/
theorem torusImageNoncongruent_of_positive_marker_and_ranges_ne
    (background : ClassicalEmbeddedImageReparametrizationClaim)
    (X Y : NonrigidTorusSource → Ambient)
    (hX : NativeTorusSmoothEmbedding X) (hY : NativeTorusSmoothEmbedding Y)
    (P : Set Ambient)
    (hPX : X '' nativeTorusPositiveRegion X = P)
    (hPY : Y '' nativeTorusPositiveRegion Y = P)
    (hmarker : ∀ A : Ambient ≃ᵃⁱ[ℝ] Ambient, A '' P = P → ∀ x, A x = x)
    (hne : range X ≠ range Y) : ImageNoncongruent X Y := by
  intro A himage
  have hpositive := nativeTorusPositiveImages_eq_of_ambient_congruence
    background X Y hX hY A himage
  rw [hPX, hPY] at hpositive
  have hfix := hmarker A hpositive
  have hAX : A ∘ X = X := funext (fun p => hfix (X p))
  apply hne
  calc
    range X = range (A ∘ X) := congrArg Set.range hAX.symm
    _ = A '' range X := Set.range_comp A X
    _ = range Y := himage

/-- Conditional marked-image noncongruence for the SAME two actual maps:
common actual forms and a nonempty open agreement, together with map inequality,
exclude equal ranges by the existing classical fixed-open result. The proved
positive-image transport then excludes every ambient affine isometry.
No construction, marker, embedding, tightness or final-pair output is granted. -/
theorem torusImageNoncongruent_of_positive_marker_and_open_agreement
    (reparamBackground : ClassicalEmbeddedImageReparametrizationClaim)
    (rigidityBackground : ClassicalExternalResults)
    (X Y : NonrigidTorusSource → Ambient)
    (hX : NativeTorusSmoothEmbedding X) (hY : NativeTorusSmoothEmbedding Y)
    (hmetric : ∀ p (v w : ℝ × ℝ),
      nativeProductInducedForm X p v w = nativeProductInducedForm Y p v w)
    (U : Set NonrigidTorusSource) (hU : IsOpen U) (hneU : U.Nonempty)
    (hagree : EqOn X Y U) (hne : X ≠ Y)
    (P : Set Ambient)
    (hPX : X '' nativeTorusPositiveRegion X = P)
    (hPY : Y '' nativeTorusPositiveRegion Y = P)
    (hmarker : ∀ A : Ambient ≃ᵃⁱ[ℝ] Ambient, A '' P = P → ∀ x, A x = x) :
    ImageNoncongruent X Y := by
  apply torusImageNoncongruent_of_positive_marker_and_ranges_ne
    reparamBackground X Y hX hY P hPX hPY hmarker
  intro hrange
  exact hne (classicalCoincidentEmbeddings_eq rigidityBackground X Y hX hY
    hmetric hrange U hU hneU hagree)

end
end TightVer401


