import TightVer401.QuadraticRadialFillingInnerAssembly

/-! Conditional actual image assembly from a genuine closed-band image and
injection, its actual outer boundary image, and the retained actual inner
scalar germ. The ordinary degree-band data remain explicit caller inputs. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Injectivity removes exactly the actual outer source circle from the
band image, yielding the actual half-open-band complement of the closed
Jordan set. The source/target image exclusion is derived here. -/
theorem quadraticRadialFilling_halfOpenBand_image_of_closedBand
    {H : Coord → ℝ} {ρ S C : ℝ} {Jopen Jboundary Jclosed : Set Coord}
    (hρS : ρ < S)
    (hBand : InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S))
    (hBandImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      {y : Coord | planarRadius y ≤ C} \ Jopen)
    (hOuterImage : planarGradient H '' quadraticRadialFillingRadiusLevel S = Jboundary)
    (hPartition : Jclosed = Jopen ∪ Jboundary) :
    planarGradient H '' {x : Coord | ρ ≤ planarRadius x ∧ planarRadius x < S} =
      {y : Coord | planarRadius y ≤ C} \ Jclosed := by
  have hLevel : quadraticRadialFillingRadiusLevel S ⊆ quadraticRadialFillingClosedAnnulus ρ S := by
    intro x hx
    change planarRadius x = S at hx
    change ρ ≤ planarRadius x ∧ planarRadius x ≤ S
    rw [hx]
    exact ⟨hρS.le, le_rfl⟩
  have hSource : quadraticRadialFillingClosedAnnulus ρ S \ quadraticRadialFillingRadiusLevel S =
      {x : Coord | ρ ≤ planarRadius x ∧ planarRadius x < S} := by
    ext x
    constructor
    · rintro ⟨hx, hne⟩
      change ρ ≤ planarRadius x ∧ planarRadius x ≤ S at hx
      change planarRadius x ≠ S at hne
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
    · rintro ⟨hl, hr⟩
      exact ⟨⟨hl, hr.le⟩, ne_of_lt hr⟩
  rw [← hSource, hBand.image_sdiff_subset hLevel, hBandImage, hOuterImage, hPartition]
  ext y
  constructor
  · rintro ⟨⟨hr, hnopen⟩, hnboundary⟩
    exact ⟨hr, fun hy => hy.elim hnopen hnboundary⟩
  · rintro ⟨hr, hnclosed⟩
    exact ⟨⟨hr, fun hy => hnclosed (Or.inl hy)⟩,
      fun hy => hnclosed (Or.inr hy)⟩

/-- The actual closed-band image equality supplies its actual physical
radius bound; the bound is not an additional geometric package input. -/
theorem quadraticRadialFilling_closedBand_radius_bound_of_image
    {H : Coord → ℝ} {ρ S C : ℝ} {Jopen : Set Coord}
    (hBandImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      {y : Coord | planarRadius y ≤ C} \ Jopen) :
    ∀ x ∈ quadraticRadialFillingClosedAnnulus ρ S, planarRadius (planarGradient H x) ≤ C := by
  intro x hx
  have hy : planarGradient H x ∈ {y : Coord | planarRadius y ≤ C} \ Jopen := by
    rw [← hBandImage]
    exact mem_image_of_mem (planarGradient H) hx
  exact hy.1

/-- Combine the actual strict inner radial image and genuine degree-band
image into the exact actual whole punctured-disk image. This is conditional
assembly: the degree-band hypotheses must be proved by the degree application. -/
theorem quadraticRadialFilling_puncturedDisk_image_of_degreeBand
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ ≤ R/2) (hρS : ρ < S) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {Jopen Jboundary Jclosed : Set Coord}
    (hPartition : Jclosed = Jopen ∪ Jboundary)
    (hJordanBound : Jclosed ⊆ {y : Coord | planarRadius y < M * (R-ρ)})
    (hBand : InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S))
    (hBandImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      {y : Coord | planarRadius y ≤ M * (R-ρ)} \ Jopen)
    (hOuterImage : planarGradient H '' quadraticRadialFillingRadiusLevel S = Jboundary) :
    planarGradient H '' {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} =
      {y : Coord | planarRadius y < M * R} \ Jclosed := by
  have hSource : {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} =
      {x : Coord | 0 < planarRadius x ∧ planarRadius x < ρ} ∪
        {x : Coord | ρ ≤ planarRadius x ∧ planarRadius x < S} := by
    ext x
    constructor
    · intro hx
      by_cases hxr : planarRadius x < ρ
      · exact Or.inl ⟨hx.1, hxr⟩
      · exact Or.inr ⟨le_of_not_gt hxr, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans hρS⟩
      · exact ⟨hρ.trans_le hx.1, hx.2⟩
  rw [hSource, image_union, quadraticRadialFilling_inner_subdisk_image hR hM hρ hρR hInner,
    quadraticRadialFilling_halfOpenBand_image_of_closedBand hρS hBand hBandImage
      hOuterImage hPartition]
  have hCupper : M * (R-ρ) < M * R :=
    mul_lt_mul_of_pos_left (by linarith) hM
  ext y
  constructor
  · rintro (hy | hy)
    · exact ⟨hy.2, fun hJ => lt_asymm hy.1 (hJordanBound hJ)⟩
    · exact ⟨hy.1.trans_lt hCupper, hy.2⟩
  · intro hy
    by_cases hlow : planarRadius y ≤ M * (R-ρ)
    · exact Or.inr ⟨hlow, hy.2⟩
    · exact Or.inl ⟨lt_of_not_ge hlow, hy.1⟩

/-- The genuine closed-band image yields its needed bound, so the checked
actual inner injection combines with ordinary closed-band injection. -/
theorem quadraticRadialFilling_puncturedDisk_injOn_of_band_image
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ ≤ R/2) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {Jopen : Set Coord}
    (hBand : InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S))
    (hBandImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      {y : Coord | planarRadius y ≤ M * (R-ρ)} \ Jopen) :
    InjOn (planarGradient H) {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} :=
  quadraticRadialFilling_puncturedDisk_injOn_of_closedBand hR hM hρ hρR hInner hBand
    (quadraticRadialFilling_closedBand_radius_bound_of_image hBandImage)

/-- Conditional exact whole image and actual injection companion. The
ordinary degree-band data are explicit and not an existence grant. -/
theorem quadraticRadialFilling_puncturedDisk_image_and_injOn_of_degreeBand
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ ≤ R/2) (hρS : ρ < S) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {Jopen Jboundary Jclosed : Set Coord}
    (hPartition : Jclosed = Jopen ∪ Jboundary)
    (hJordanBound : Jclosed ⊆ {y : Coord | planarRadius y < M * (R-ρ)})
    (hBand : InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S))
    (hBandImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      {y : Coord | planarRadius y ≤ M * (R-ρ)} \ Jopen)
    (hOuterImage : planarGradient H '' quadraticRadialFillingRadiusLevel S = Jboundary) :
    (planarGradient H '' {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} =
      {y : Coord | planarRadius y < M * R} \ Jclosed) ∧
      InjOn (planarGradient H) {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} :=
  ⟨quadraticRadialFilling_puncturedDisk_image_of_degreeBand hR hM hρ hρR hρS hInner
      hPartition hJordanBound hBand hBandImage hOuterImage,
    quadraticRadialFilling_puncturedDisk_injOn_of_band_image hR hM hρ hρR hInner hBand hBandImage⟩

end
end TightVer401
