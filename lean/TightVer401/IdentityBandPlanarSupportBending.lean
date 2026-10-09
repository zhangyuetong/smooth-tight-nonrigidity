import TightVer401.IdentityBandPlanarSupportRegion
import TightVer401.MetricBranching

/-! Actual infinitesimal bending transferred through the constructed source
coordinates. The coordinate field is considered only on the open target;
its compact support on that target's subtype is handled by Region. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M]

/-- Actual source symmetric differential pairing pulls back to zero Cartesian
strain. Reconstruction supplies equality on an open neighborhood, so the
Cartesian derivatives are those of the original immersion composed with the
actual smooth inverse. -/
theorem identityBandPlanarSupport_bending_transfer
    {X Y : M → Ambient} {G : Coord → ℝ}
    (hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ X)
    (hY : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ Y)
    (hstrain : ∀ p : M, ∀ v w : TangentSpace 𝓘(ℝ, Coord) p,
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p w) +
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p w) = 0)
    (e : OpenPartialHomeomorph M Coord) (_he : e.source = univ)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e.symm e.target)
    (hrec : ∀ p : M, planarSupportMap G (e p) = X p) :
    IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target := by
  have hYs : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (Y ∘ e.symm) e.target :=
    (hY.contMDiffOn (s := univ)).comp heI (fun _ _ => mem_univ _)
  refine ⟨hYs.contDiffOn, ?_⟩
  intro q hq i j
  have heq : planarSupportMap G =ᶠ[𝓝 q] (X ∘ e.symm) := by
    filter_upwards [e.open_target.mem_nhds hq] with z hz
    have hr := hrec (e.symm z)
    rw [e.right_inv hz] at hr
    exact hr
  have hdi := (heI.contMDiffAt (e.open_target.mem_nhds hq)).mdifferentiableAt (by simp)
  have hdX := mfderiv_comp q ((hX (e.symm q)).mdifferentiableAt (by simp)) hdi
  have hdY := mfderiv_comp q ((hY (e.symm q)).mdifferentiableAt (by simp)) hdi
  rw [mfderiv_eq_fderiv] at hdX hdY
  unfold strain coordPartial
  rw [heq.fderiv_eq (𝕜 := ℝ), hdX, hdY]
  let v := mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) e.symm q (Pi.single i 1)
  let w := mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) e.symm q (Pi.single j 1)
  change @inner ℝ Ambient _
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X (e.symm q) v)
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y (e.symm q) w) +
    @inner ℝ Ambient _
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y (e.symm q) v)
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X (e.symm q) w) = 0
  exact hstrain (e.symm q) v w

/-- On the physical target this coordinate representative is exactly the
subtype field whose compact support was transported by the same chart. -/
theorem identityBandPlanarSupport_bending_field_on_target
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    (Y : M → Ambient) (q : e.target) :
    identityBandPlanarRegionField e he Y q = (Y ∘ e.symm) q.val := rfl

end
end TightVer401

