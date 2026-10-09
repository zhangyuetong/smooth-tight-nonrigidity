import TightVer401.ProtectedTorusPositiveGaussPhaseHeight
import TightVer401.ProtectedTorusPositiveGaussNormal
import TightVer401.ParabolicConvexClosureComplete

/-! Actual Gauss homeomorphism for the same assembled meridian.
The inverse uses the proved meridian Gauss inverse and the actual cosine-height
inverse. The forward map is the global normalized differential cross. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussHomeomorphPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def protectedTorusPositiveGaussAssembly {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) :
    ProtectedTorusAssemblyInput RN mu h where
  toProtectedSaddleCylinderInput := S
  toProtectedParabolicMeridianInput := D.toProtectedParabolicMeridianInput

@[simp] theorem protectedTorusPositiveGaussAssembly_saddle {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) :
    (protectedTorusPositiveGaussAssembly S D).saddle = S.saddle := rfl

@[simp] theorem protectedTorusPositiveGaussAssembly_meridian {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) :
    (protectedTorusPositiveGaussAssembly S D).meridian = D.meridian := rfl

/-- The full chosen closure is projected once; the literal map is retained. -/
theorem protectedTorusPositiveGaussAssembly_map {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) :
    protectedTorusMap (protectedTorusPositiveGaussAssembly S D).saddle
      (protectedTorusPositiveGaussAssembly S D).meridian h =
      protectedTorusMap S.saddle D.meridian h := rfl

/-- Return to the literal convex phase from actual meridian height coordinates. -/
def protectedTorusPositiveGaussReturn {h : ℝ} (hh : 0 < h)
    (p : AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h) :
    NonrigidTorusSource :=
  (p.1, periodProjection (2 * Real.pi) (protectedTorusPositiveGaussHeightInverse h p.2))

theorem protectedTorusPositiveGaussReturn_mem {h : ℝ} (hh : 0 < h)
    (p : AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h) :
    protectedTorusPositiveGaussReturn hh p ∈ protectedTorusPositiveGaussRegion := by
  change p.1 ∈ univ ∧ _
  exact ⟨mem_univ _, ⟨_, protectedTorusPositiveGaussHeightInverse_mem hh p.2.property, rfl⟩⟩

theorem protectedTorusPositiveGaussReturn_contMDiff {h : ℝ} (hh : 0 < h) :
    ContMDiff nativeProductModel nativeProductModel ∞ (protectedTorusPositiveGaussReturn hh) := by
  have hs := (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ))
    (U := protectedTorusPositiveGaussPhaseDomain)).comp
      (protectedTorusPositiveGaussHeightDiffeomorph hh).symm.contMDiff
  exact contMDiff_fst.prodMk
    ((periodProjection_contMDiff (2 * Real.pi)).comp (hs.comp contMDiff_snd))

/-- Actual height coordinates of a point in the open convex phase. -/
def protectedTorusPositiveGaussCoordinates {h : ℝ} (hh : 0 < h)
    (p : protectedTorusPositiveGaussRegion) :
    AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h :=
  (p.val.1, ⟨protectedTorusPositiveGaussHeight h
    (protectedTorusPositiveGaussPhaseChart.symm p.val.2),
    protectedTorusPositiveGaussHeight_mem hh
      (by
        have hp : p.val.2 ∈ protectedTorusPositiveGaussPhaseChart.target := by
          rw [protectedTorusPositiveGaussPhaseChart_target]
          exact p.property.2
        have ht := protectedTorusPositiveGaussPhaseChart.map_target hp
        rwa [protectedTorusPositiveGaussPhaseChart_source] at ht)⟩)

theorem protectedTorusPositiveGaussCoordinates_return {h : ℝ} (hh : 0 < h)
    (p : protectedTorusPositiveGaussRegion) :
    protectedTorusPositiveGaussReturn hh (protectedTorusPositiveGaussCoordinates hh p) = p.val := by
  have hp : p.val.2 ∈ protectedTorusPositiveGaussPhaseChart.target := by
    rw [protectedTorusPositiveGaussPhaseChart_target]; exact p.property.2
  have ht := protectedTorusPositiveGaussPhaseChart.map_target hp
  rw [protectedTorusPositiveGaussPhaseChart_source] at ht
  apply Prod.ext
  · rfl
  change periodProjection (2 * Real.pi)
    (protectedTorusPositiveGaussHeightInverse h
      (protectedTorusPositiveGaussHeight h (protectedTorusPositiveGaussPhaseChart.symm p.val.2))) = _
  rw [protectedTorusPositiveGaussHeight_left hh ht]
  exact protectedTorusPositiveGaussPhaseChart.right_inv hp

theorem protectedTorusPositiveGaussCoordinates_normal {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : protectedTorusPositiveGaussRegion) :
    protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D) p.val =
      (D.gaussDiffeomorph (protectedTorusPositiveGaussCoordinates D.height_pos p) : RoundSphere) := by
  let φ := protectedTorusPositiveGaussPhaseChart.symm p.val.2
  have hp : p.val.2 ∈ protectedTorusPositiveGaussPhaseChart.target := by
    rw [protectedTorusPositiveGaussPhaseChart_target]; exact p.property.2
  have ht := protectedTorusPositiveGaussPhaseChart.map_target hp
  rw [protectedTorusPositiveGaussPhaseChart_source] at ht
  have he : periodProjection (2 * Real.pi) φ = p.val.2 :=
    protectedTorusPositiveGaussPhaseChart.right_inv hp
  rw [D.gaussDiffeomorph_eq]
  have hn := protectedTorusPositiveGaussNormal_convex
    (protectedTorusPositiveGaussAssembly S D) p.val.1 φ ht
  rw [he] at hn
  exact hn

/-- A total representative of the Gauss inverse, with an irrelevant fallback
outside its precise open target. -/
def protectedTorusPositiveGaussInverse {RN mu h : ℝ}
    (D : ParabolicConvexClosureData RN mu h) (n : RoundSphere) : NonrigidTorusSource := by
  classical
  exact if hn : n ∈ parabolicConvexClosureSphereBelt then
    protectedTorusPositiveGaussReturn D.height_pos (D.gaussDiffeomorph.symm ⟨n, hn⟩)
    else (0, 0)

theorem protectedTorusPositiveGaussInverse_contMDiffOn {RN mu h : ℝ}
    (D : ParabolicConvexClosureData RN mu h) :
    ContMDiffOn (𝓡 2) nativeProductModel ∞ (protectedTorusPositiveGaussInverse D)
      parabolicConvexClosureSphereBelt := by
  classical
  have he : (fun n : parabolicConvexClosureSphereBelt =>
      protectedTorusPositiveGaussInverse D n.val) =
      protectedTorusPositiveGaussReturn D.height_pos ∘ D.gaussDiffeomorph.symm := by
    funext n
    simp [protectedTorusPositiveGaussInverse, n.property]
  have hs := (protectedTorusPositiveGaussReturn_contMDiff D.height_pos).comp
    D.gaussDiffeomorph.symm.contMDiff
  intro n hn
  have hp : ContMDiffAt (𝓡 2) nativeProductModel ∞
      (fun n : parabolicConvexClosureSphereBelt => protectedTorusPositiveGaussInverse D n.val)
      ⟨n, hn⟩ := by rw [he]; exact hs _
  exact (contMDiffAt_subtype_iff.mp hp).contMDiffWithinAt

theorem protectedTorusPositiveGaussInverse_left {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : protectedTorusPositiveGaussRegion) :
    protectedTorusPositiveGaussInverse D
      (protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D) p.val) = p.val := by
  classical
  rw [protectedTorusPositiveGaussCoordinates_normal S D p]
  simp only [protectedTorusPositiveGaussInverse, dif_pos (D.gaussDiffeomorph _).property]
  rw [D.gaussDiffeomorph.symm_apply_apply]
  exact protectedTorusPositiveGaussCoordinates_return D.height_pos p

theorem protectedTorusPositiveGaussInverse_right {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (n : parabolicConvexClosureSphereBelt) :
    protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D)
      (protectedTorusPositiveGaussInverse D n.val) = n.val := by
  classical
  simp only [protectedTorusPositiveGaussInverse, dif_pos n.property]
  let p := D.gaussDiffeomorph.symm n
  have hφ := protectedTorusPositiveGaussHeightInverse_mem D.height_pos p.2.property
  change protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D)
    (p.1, periodProjection (2 * Real.pi)
      (protectedTorusPositiveGaussHeightInverse h p.2)) = n.val
  rw [protectedTorusPositiveGaussNormal_convex _ p.1 _ hφ]
  have hz := protectedTorusPositiveGaussHeight_right D.height_pos p.2.property
  change protectedTorusPositiveGaussHeight h
    (protectedTorusPositiveGaussHeightInverse h p.2) = (p.2 : ℝ) at hz
  have hp : (p.1, ⟨-h * Real.cos (protectedTorusPositiveGaussHeightInverse h p.2),
      protectedTorusPositiveGauss_convex_height_mem D.height_pos hφ⟩) = p :=
    Prod.ext rfl (Subtype.ext hz)
  rw [hp, protectedTorusPositiveGaussAssembly_meridian, ← D.gaussDiffeomorph_eq p]
  exact congrArg Subtype.val (D.gaussDiffeomorph.apply_symm_apply n)

/-- Actual whole convex Gauss homeomorphism of the literal assembled map. -/
def protectedTorusPositiveGaussHomeomorph {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) :
    OpenPartialHomeomorph NonrigidTorusSource RoundSphere where
  toFun := protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D)
  invFun := protectedTorusPositiveGaussInverse D
  source := protectedTorusPositiveGaussRegion
  target := parabolicConvexClosureSphereBelt
  map_source' p hp := by
    rw [protectedTorusPositiveGaussCoordinates_normal S D ⟨p, hp⟩]
    exact (D.gaussDiffeomorph _).property
  map_target' n hn := by
    classical
    change protectedTorusPositiveGaussInverse D n ∈ protectedTorusPositiveGaussRegion
    change n ∈ parabolicConvexClosureSphereBelt at hn
    simp only [protectedTorusPositiveGaussInverse, dif_pos hn]
    exact protectedTorusPositiveGaussReturn_mem D.height_pos _
  left_inv' p hp := protectedTorusPositiveGaussInverse_left S D ⟨p, hp⟩
  right_inv' n hn := protectedTorusPositiveGaussInverse_right S D ⟨n, hn⟩
  open_source := protectedTorusPositiveGaussRegion.isOpen
  open_target := parabolicConvexClosureSphereBelt.isOpen
  continuousOn_toFun := (protectedTorusPositiveGaussNormal_contMDiff _).continuous.continuousOn
  continuousOn_invFun := (protectedTorusPositiveGaussInverse_contMDiffOn D).continuousOn

end
end TightVer401
