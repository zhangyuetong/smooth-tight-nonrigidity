import TightVer401.IdentityBandPlanarSupportImage

/-! The global regular horizontal image and the actual gradient image of the
constructed support potential. Inverses are derived, not supplied. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

local instance identityBandPlanarSupportGradientSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M] [Nonempty M]

/-- The actual first two Cartesian coordinates of the ambient immersion. -/
def identityBandPlanarHorizontalCLM : Ambient →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i : Fin 2 =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (Fin.castSucc i))

/-- Reuse the checked global Gauss inverse to derive the inverse of any
regular injective coordinate map. The auxiliary sphere map is gnomonicPoint
composed with the coordinate map; no normal or support assumptions are needed. -/
theorem identityBandPlanarSupport_regular_coordinate_image {P : M → Coord}
    (hP : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ P)
    (hiP : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) P p))
    (hPi : Function.Injective P) :
    ∃ e : OpenPartialHomeomorph M Coord,
      e.source = univ ∧ e.target = range P ∧ (e : M → Coord) = P ∧
      ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e.symm e.target := by
  let N : M → RoundSphere := fun p => gnomonicPoint (P p)
  have hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N := gnomonicPoint_contMDiff.comp hP
  have hiN (p : M) : Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p) := by
    have hd := mfderiv_comp p
      ((gnomonicNormal_contDiff.contMDiff.contMDiffAt (x := P p)).mdifferentiableAt (by simp))
      ((hP p).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    change mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p = _ at hd
    rw [hd]
    exact (gnomonicNormal_differential_injective (P p)).comp (hiP p)
  have hNi : Function.Injective N := by
    intro p q hpq
    apply hPi
    have he := congrArg (fun n : RoundSphere => gnomonicInverse n.val) hpq
    change gnomonicInverse (planarUnitNormal (P p)) =
      gnomonicInverse (planarUnitNormal (P q)) at he
    simpa only [gnomonic_left_inverse] using he
  have hnorth (p : M) : 0 < (N p).val 2 := gnomonicPoint_north (P p)
  let e := identityBandPlanarSourceChart hN hiN hNi hnorth
  have heP : (e : M → Coord) = P := by
    funext p
    exact gnomonic_left_inverse (P p)
  have heT : e.target = range P := by
    change identityBandPlanarSourceDomain N = range P
    rw [identityBandPlanarSourceDomain_eq_range hnorth]
    have he : identityBandPlanarSource N = P := heP
    rw [he]
  exact ⟨e, rfl, heT, heP, identityBandPlanarSourceInverse_contMDiffOn hN hiN hNi⟩

/-- The reconstructed gradient is exactly the actual horizontal projection. -/
theorem identityBandPlanarSupport_gradient_eq {N : M → RoundSphere} {X : M → Ambient}
    {G : Coord → ℝ}
    (hrec : ∀ p, planarSupportMap G (identityBandPlanarSource N p) = X p) (p : M) :
    planarGradient G (identityBandPlanarSource N p) = identityBandPlanarHorizontalCLM (X p) := by
  ext i
  have he := congrArg (fun u : Ambient => u (Fin.castSucc i)) (hrec p)
  fin_cases i <;> simpa [planarGradient, planarSupportMap, identityBandPlanarHorizontalCLM,
    ContinuousLinearMap.pi_apply, PiLp.proj_apply] using he

/-- Global source and gradient images are constructed from actual Gauss and
horizontal regularity. Both source images are parametrized by the same M,
so specializing M to the retained native cylinder identifies actual annuli. -/
theorem identityBandPlanarSupport_exists_source_gradient_images
    {N : M → RoundSphere} {X : M → Ambient}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hiN : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p))
    (hNi : Function.Injective N) (hnorth : ∀ p, 0 < (N p).val 2)
    (hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ X)
    (horth : ∀ p, ∀ v : TangentSpace 𝓘(ℝ, Coord) p,
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p v) (N p).val = 0)
    (hiH : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord)
      (fun p => identityBandPlanarHorizontalCLM (X p)) p))
    (hHi : Function.Injective (fun p => identityBandPlanarHorizontalCLM (X p))) :
    ∃ G : Coord → ℝ, ∃ e : OpenPartialHomeomorph M Coord,
      ∃ h : OpenPartialHomeomorph M Coord, ∃ g : OpenPartialHomeomorph Coord Coord,
        e.source = univ ∧ e.target = range (identityBandPlanarSource N) ∧
        (e : M → Coord) = identityBandPlanarSource N ∧
        ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e ∧
        ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e.symm e.target ∧
        h.source = univ ∧ h.target = range (fun p => identityBandPlanarHorizontalCLM (X p)) ∧
        (h : M → Coord) = (fun p => identityBandPlanarHorizontalCLM (X p)) ∧
        ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ h.symm h.target ∧
        ContDiffOn ℝ ∞ G e.target ∧ (∀ p, planarSupportMap G (e p) = X p) ∧
        g.source = e.target ∧ g.target = h.target ∧
        EqOn g (planarGradient G) g.source ∧
        ContDiffOn ℝ ∞ g g.source ∧ ContDiffOn ℝ ∞ g.symm g.target := by
  let P : M → Coord := fun p => identityBandPlanarHorizontalCLM (X p)
  have hP : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ P :=
    identityBandPlanarHorizontalCLM.contDiff.contMDiff.comp hX
  obtain ⟨h, hS, hT, hfun, hI⟩ := identityBandPlanarSupport_regular_coordinate_image hP hiH hHi
  obtain ⟨G, hG, hrec, _⟩ := identityBandPlanarSupport_exists_potential hN hiN hNi hnorth hX horth
  let e := identityBandPlanarSourceChart hN hiN hNi hnorth
  have heS : e.source = univ := rfl
  have heF : (e : M → Coord) = identityBandPlanarSource N := rfl
  have heT : e.target = range (identityBandPlanarSource N) :=
    identityBandPlanarSourceDomain_eq_range hnorth
  have heD : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e :=
    identityBandPlanarSource_contMDiff hN hnorth
  have heI : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ e.symm e.target :=
    identityBandPlanarSourceInverse_contMDiffOn hN hiN hNi
  let g := e.symm.trans h
  have hgS : g.source = e.target := by
    simp only [g, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      hS, preimage_univ, inter_univ]
  have hgT : g.target = h.target := by
    simp only [g, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      heS, preimage_univ, inter_univ]
  have hgF : EqOn g (planarGradient G) g.source := by
    intro q hq
    have hqe : q ∈ e.target := hgS ▸ hq
    have hgrad := identityBandPlanarSupport_gradient_eq hrec (e.symm q)
    change planarGradient G (e (e.symm q)) = P (e.symm q) at hgrad
    rw [e.right_inv hqe] at hgrad
    change h (e.symm q) = planarGradient G q
    rw [hfun]
    exact hgrad.symm
  have hgD : ContDiffOn ℝ ∞ g g.source := by
    rw [hgS]
    exact (planarGradient_contDiffOn hG e.open_target).congr
      (fun q hq => hgF (hgS.symm ▸ hq))
  have hgI : ContDiffOn ℝ ∞ g.symm g.target := by
    rw [hgT]
    have hd : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ (fun q => e (h.symm q)) h.target :=
      (heD.contMDiffOn (s := univ)).comp hI (by intro q hq; trivial)
    exact hd.contDiffOn
  exact ⟨G, e, h, g, heS, heT, heF, heD, heI, hS, hT, hfun, hI, hG,
    hrec, hgS, hgT, hgF, hgD, hgI⟩

end
end TightVer401
