import TightVer401.GaussImageInverse
import TightVer401.GnomonicSupport
import TightVer401.PlanarGradientInverse

/-! Global planar source coordinates and support reconstructed from actual
regular injective north Gauss data. Native atlas transport is a separate input
application: these lemmas use the existing audited Coord source model. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

local instance identityBandPlanarSupportImageSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M] [Nonempty M]

def identityBandPlanarSource (N : M → RoundSphere) (p : M) : Coord :=
  gnomonicInverse (N p).val

def identityBandPlanarSourceDomain (N : M → RoundSphere) : Set Coord :=
  gnomonicPoint ⁻¹' range N

def identityBandPlanarSourceInverse (N : M → RoundSphere) (q : Coord) : M :=
  gaussImageInverse N univ (gnomonicPoint q)

theorem identityBandPlanarSource_contMDiff {N : M → RoundSphere}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hnorth : ∀ p, 0 < (N p).val 2) :
    ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ (identityBandPlanarSource N) := by
  intro p
  exact (gnomonicInverse_contMDiffAt (hnorth p)).comp p (hN p)

theorem identityBandPlanarSourceDomain_eq_range {N : M → RoundSphere}
    (hnorth : ∀ p, 0 < (N p).val 2) :
    identityBandPlanarSourceDomain N = range (identityBandPlanarSource N) := by
  ext q
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    unfold identityBandPlanarSource
    rw [hp]
    exact gnomonic_left_inverse q
  · rintro ⟨p, rfl⟩
    change gnomonicPoint (gnomonicInverse (N p).val) ∈ range N
    rw [gnomonic_right_inverse (hnorth p)]
    exact mem_range_self p

theorem identityBandPlanarSourceInverse_left {N : M → RoundSphere}
    (hNi : Function.Injective N) (hnorth : ∀ p, 0 < (N p).val 2) (p : M) :
    identityBandPlanarSourceInverse N (identityBandPlanarSource N p) = p := by
  unfold identityBandPlanarSourceInverse identityBandPlanarSource
  rw [gnomonic_right_inverse (hnorth p)]
  exact gaussImageInverse_left hNi.injOn (mem_univ p)

theorem identityBandPlanarSourceInverse_right {N : M → RoundSphere} {q : Coord}
    (hq : q ∈ identityBandPlanarSourceDomain N) :
    identityBandPlanarSource N (identityBandPlanarSourceInverse N q) = q := by
  unfold identityBandPlanarSource identityBandPlanarSourceInverse
  have hr : gnomonicPoint q ∈ N '' univ := by simpa only [image_univ, identityBandPlanarSourceDomain, Set.mem_preimage] using hq
  rw [gaussImageInverse_right hr]
  exact gnomonic_left_inverse q

theorem identityBandPlanarSourceDomain_isOpen {N : M → RoundSphere}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p)) :
    IsOpen (identityBandPlanarSourceDomain N) := by
  have hΩ : IsOpen (range N) := by
    simpa only [image_univ] using gaussManifold_image_isOpen hN.contMDiffOn isOpen_univ
      (fun p _ => hi p)
  exact hΩ.preimage gnomonicPoint_contMDiff.continuous

theorem identityBandPlanarSourceInverse_contMDiffOn {N : M → RoundSphere}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p))
    (hNi : Function.Injective N) :
    ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ (identityBandPlanarSourceInverse N)
      (identityBandPlanarSourceDomain N) := by
  have hI := gaussImageInverse_contMDiffOn hN.contMDiffOn isOpen_univ
    (fun p _ => hi p) hNi.injOn
  exact hI.comp gnomonicPoint_contMDiff.contMDiffOn
    (fun q hq => by simpa only [image_univ, identityBandPlanarSourceDomain, Set.mem_preimage] using hq)

/-- The actual source map is a global homeomorphism onto its open image,
with smooth inverse derived from the checked local Gauss inverses. -/
def identityBandPlanarSourceChart {N : M → RoundSphere}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p))
    (hNi : Function.Injective N) (hnorth : ∀ p, 0 < (N p).val 2) :
    OpenPartialHomeomorph M Coord where
  toFun := identityBandPlanarSource N
  invFun := identityBandPlanarSourceInverse N
  source := univ
  target := identityBandPlanarSourceDomain N
  map_source' := by
    intro p _
    rw [identityBandPlanarSourceDomain_eq_range hnorth]
    exact mem_range_self p
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun p _ => identityBandPlanarSourceInverse_left hNi hnorth p
  right_inv' := fun _ hq => identityBandPlanarSourceInverse_right hq
  open_source := isOpen_univ
  open_target := identityBandPlanarSourceDomain_isOpen hN hi
  continuousOn_toFun := (identityBandPlanarSource_contMDiff hN hnorth).continuous.continuousOn
  continuousOn_invFun :=
    (identityBandPlanarSourceInverse_contMDiffOn hN hi hNi).continuousOn

/-- No spherical potential is supplied: it is constructed from the actual
surface and its derived global inverse, then transferred by the gnomonic chart. -/
theorem identityBandPlanarSupport_exists_potential {N : M → RoundSphere} {X : M → Ambient}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) p))
    (hNi : Function.Injective N) (hnorth : ∀ p, 0 < (N p).val 2)
    (hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ X)
    (horth : ∀ p, ∀ v : TangentSpace 𝓘(ℝ, Coord) p,
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p v) (N p).val = 0) :
    ∃ G : Coord → ℝ,
      ContDiffOn ℝ ∞ G (identityBandPlanarSourceDomain N) ∧
      (∀ p, planarSupportMap G (identityBandPlanarSource N p) = X p) ∧
      (∀ p, ∀ i : Fin 2, coordPartial i G (identityBandPlanarSource N p) =
        X p (Fin.castSucc i)) := by
  obtain ⟨H, hΩ, hH, hrec⟩ := gaussImage_support_exists hN.contMDiffOn isOpen_univ
    (fun p _ => hi p) hNi.injOn hX.contMDiffOn (fun p _ v => horth p v)
  have hnΩ : ∀ q ∈ N '' univ, 0 < q.val 2 := by
    rintro q ⟨p, _, rfl⟩
    exact hnorth p
  have hG : ContDiffOn ℝ ∞ (gnomonicPotential H) (identityBandPlanarSourceDomain N) := by
    simpa only [image_univ, identityBandPlanarSourceDomain] using gnomonicPotential_contDiffOn hH
  have hR (p : M) : planarSupportMap (gnomonicPotential H) (identityBandPlanarSource N p) = X p := by
    have hp : gnomonicPoint (identityBandPlanarSource N p) ∈ N '' univ := by
      change gnomonicPoint (gnomonicInverse (N p).val) ∈ N '' univ
      rw [gnomonic_right_inverse (hnorth p)]
      exact mem_image_of_mem N (mem_univ p)
    rw [gnomonicSupport_reconstruction hH hΩ hnΩ hp]
    change globalSphereSupport H (gnomonicPoint (gnomonicInverse (N p).val)) = X p
    rw [gnomonic_right_inverse (hnorth p)]
    exact (hrec p (mem_univ p)).symm
  refine ⟨gnomonicPotential H, hG, hR, ?_⟩
  intro p i
  have he := congrArg (fun x : Ambient => x (Fin.castSucc i)) (hR p)
  fin_cases i <;> simpa [planarSupportMap] using he

/-- The full retained compact support remains inside the actual open planar
image. Any protected-region inclusion transports by the same actual map. -/
theorem identityBandPlanarSource_protected_support {N : M → RoundSphere} {Y : M → Ambient}
    (hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N)
    (hnorth : ∀ p, 0 < (N p).val 2) (hY : HasCompactSupport Y)
    {K : Set M} (hprotect : tsupport Y ⊆ K) :
    IsCompact (identityBandPlanarSource N '' tsupport Y) ∧
      identityBandPlanarSource N '' tsupport Y ⊆ identityBandPlanarSourceDomain N ∧
      identityBandPlanarSource N '' tsupport Y ⊆ identityBandPlanarSource N '' K := by
  refine ⟨hY.image (identityBandPlanarSource_contMDiff hN hnorth).continuous, ?_,
    image_mono hprotect⟩
  rw [identityBandPlanarSourceDomain_eq_range hnorth]
  exact image_subset_range _ _

end
end TightVer401


