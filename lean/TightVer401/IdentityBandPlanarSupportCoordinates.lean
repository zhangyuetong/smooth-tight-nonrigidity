import TightVer401.GnomonicCoordinates
import TightVer401.PlanarSupportConverse
import TightVer401.PeriodicRuledNativeGauss

/-! Coordinate adapters for planar support of the actual identity band.
The global Gauss inverse and annular image are separate constructions. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The unnormalized planar normal is the actual north normal rescaled by
its vertical coordinate. No unit-length hypothesis is needed for this algebra. -/
theorem identityBand_gnomonic_normalNumerator {n : Ambient} (hn : n 2 ≠ 0) :
    planarNormalNumerator (gnomonicInverse n) = (n 2)⁻¹ • n := by
  ext i
  fin_cases i <;>
    simp [planarNormalNumerator, gnomonicInverse, div_eq_mul_inv, mul_comm, hn]

/-- The north unit normal is recovered exactly by its gnomonic coordinates. -/
theorem identityBand_gnomonic_unitNormal {n : Ambient}
    (hunit : inner ℝ n n = 1) (hnorth : 0 < n 2) :
    planarUnitNormal (gnomonicInverse n) = n := by
  have hnorm : ‖n‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hunit
    nlinarith [norm_nonneg n]
  let q : RoundSphere := ⟨n, by simpa using hnorm⟩
  exact congrArg Subtype.val (gnomonic_right_inverse (q := q) hnorth)

/-- This is the retained native ruled-band normal, rather than an assumed
normal of a reconstructed graph. -/
theorem identityBand_bandGauss_planarUnitNormal {L b : ℝ}
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b)
    (hnorth : 0 < d.bandGaussMap p 2) :
    planarUnitNormal (gnomonicInverse (d.bandGaussMap p)) = d.bandGaussMap p := by
  apply identityBand_gnomonic_unitNormal _ hnorth
  exact periodicRuledFrame_fullGaussMap_unit d (p.1, (p.2 : ℝ))

/-- Every actual band derivative is orthogonal to the graph-support normal
numerator in the band's own gnomonic coordinates. -/
theorem identityBand_bandDifferential_gnomonic_orthogonal {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b)
    (hnorth : 0 < d.bandGaussMap p 2) (v : ℝ × ℝ) :
    inner ℝ (bandDifferential d.bandMap p v)
      (planarNormalNumerator (gnomonicInverse (d.bandGaussMap p))) = 0 := by
  rw [identityBand_gnomonic_normalNumerator (ne_of_gt hnorth),
    real_inner_smul_right, periodicRuledFrame_bandGaussMap_orthogonal d p v, mul_zero]

/-- The support height of the actual band has the exact scalar normalization
used by the Cartesian potential after gnomonic reparametrization. -/
theorem identityBand_band_support_height {L b : ℝ}
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b)
    (hnorth : 0 < d.bandGaussMap p 2) :
    inner ℝ (d.bandMap p)
      (planarNormalNumerator (gnomonicInverse (d.bandGaussMap p))) =
      inner ℝ (d.bandMap p) (d.bandGaussMap p) / d.bandGaussMap p 2 := by
  rw [identityBand_gnomonic_normalNumerator (ne_of_gt hnorth), real_inner_smul_right]
  simp only [div_eq_mul_inv, mul_comm]
/-- Once a smooth Cartesian reparametrization has actually been constructed,
its north Gauss-coordinate identity supplies the actual smooth potential,
horizontal-gradient identity, and support reconstruction. This adapter does
not provide or assume a global band inverse or identify an annular image. -/
theorem identityBand_planarSupport_from_cartesian_coordinates
    {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U)
    (hn : ∀ p ∈ U, IsUnitNormalAt X (N p) p)
    (hnorth : ∀ p ∈ U, 0 < N p 2)
    (hcoords : ∀ p ∈ U, gnomonicInverse (N p) = p) :
    ContDiffOn ℝ ∞ (planarPotential X) U ∧
      (∀ p ∈ U, ∀ i : Fin 2,
        coordPartial i (planarPotential X) p = X p (Fin.castSucc i)) ∧
      Set.EqOn X (planarSupportMap (planarPotential X)) U := by
  have hnormal : ∀ p ∈ U, IsUnitNormalAt X (planarUnitNormal p) p := by
    intro p hp
    have heq : planarUnitNormal p = N p := by
      simpa only [hcoords p hp] using
        identityBand_gnomonic_unitNormal (hn p hp).1 (hnorth p hp)
    rw [heq]
    exact hn p hp
  exact ⟨planarPotential_contDiffOn hX,
    fun p hp i => planarPotential_coordPartial hX hU hp (hnormal p hp) i,
    planarSupportMap_converse_local hX hU hnormal⟩

end
end TightVer401


