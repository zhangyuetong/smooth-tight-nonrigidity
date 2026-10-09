import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual interval inverse of the completed-cylinder radial parameter.
Its image, open embedding and inverse smoothness are derived from ordinary
smoothness, strict order, endpoint values and positive actual derivative. -/
namespace TightVer401
noncomputable section
open Set Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem completedSaddleAnnulusRadialParameter_image
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    β '' Ioo a b = Ioo A RN := by
  simpa only [hleft,hright] using
    hβ.continuous.continuousOn.image_Ioo_of_strictMonoOn hab.le hmono

/-- The actual strictly ordered interval restriction is open in the
ambient real line, by the derived exact image and order connectedness. -/
theorem completedSaddleAnnulusRadialParameter_openEmbedding
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    IsOpenEmbedding ((Ioo a b).domRestrict β) := by
  have hStrict : StrictMono ((Ioo a b).domRestrict β) := by
    intro x y hxy
    exact hmono (Ioo_subset_Icc_self x.property) (Ioo_subset_Icc_self y.property) hxy
  have hRange : range ((Ioo a b).domRestrict β) = Ioo A RN := by
    rw [← completedSaddleAnnulusRadialParameter_image hab hβ hmono hleft hright]
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hEmbedding : IsEmbedding ((Ioo a b).domRestrict β) :=
    hStrict.isEmbedding_of_ordConnected (by rw [hRange]; exact ordConnected_Ioo)
  exact ⟨hEmbedding, by rw [hRange]; exact isOpen_Ioo⟩

/-- Actual partial homeomorphism, whose forward map remains literally
the supplied radial parameter, rather than a separately chosen extension. -/
def completedSaddleAnnulusRadialInverse
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    OpenPartialHomeomorph ℝ ℝ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((hmono.injOn.mono Ioo_subset_Icc_self).toPartialEquiv β (Ioo a b))
    hβ.continuous.continuousOn
    (completedSaddleAnnulusRadialParameter_openEmbedding hab hβ hmono hleft hright).isOpenMap
    isOpen_Ioo

theorem completedSaddleAnnulusRadialInverse_source
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    (completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright).source = Ioo a b := rfl

theorem completedSaddleAnnulusRadialInverse_target
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    (completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright).target = Ioo A RN :=
  completedSaddleAnnulusRadialParameter_image hab hβ hmono hleft hright

theorem completedSaddleAnnulusRadialInverse_coe
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN) :
    (completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright : ℝ → ℝ) = β := rfl

theorem completedSaddleAnnulusRadialInverse_symm_contDiffOn
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN)
    (hpositive : ∀ u ∈ Ioo a b, 0 < deriv β u) :
    ContDiffOn ℝ ∞ (completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright).symm
      (Ioo A RN) := by
  let e := completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright
  have heFun : (e : ℝ → ℝ) = β := rfl
  have heSource : e.source = Ioo a b := rfl
  have heTarget : e.target = Ioo A RN :=
    completedSaddleAnnulusRadialInverse_target hab hβ hmono hleft hright
  intro y hy
  have hyTarget : y ∈ e.target := by rwa [heTarget]
  have hx : e.symm y ∈ Ioo a b := by simpa only [heSource] using e.map_target hyTarget
  have hd : HasDerivAt e (deriv β (e.symm y)) (e.symm y) := by
    rw [heFun]
    exact (hβ.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hf : ContDiffAt ℝ ∞ e (e.symm y) := by rw [heFun]; exact hβ.contDiffAt
  exact (e.contDiffAt_symm_deriv (hpositive _ hx).ne' hyTarget hd hf).contDiffWithinAt

/-- Construct the exact smooth interval inverse from the same actual
parameter data; no inverse or image conclusion is supplied by the caller. -/
theorem exists_completedSaddleAnnulusRadialInverse
    {β : ℝ → ℝ} {a b A RN : ℝ} (hab : a < b)
    (hβ : ContDiff ℝ ∞ β) (hmono : StrictMonoOn β (Icc a b))
    (hleft : β a = A) (hright : β b = RN)
    (hpositive : ∀ u ∈ Ioo a b, 0 < deriv β u) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = Ioo a b ∧ e.target = Ioo A RN ∧ (e : ℝ → ℝ) = β ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  refine ⟨completedSaddleAnnulusRadialInverse hab hβ hmono hleft hright,rfl,
    completedSaddleAnnulusRadialInverse_target hab hβ hmono hleft hright,rfl,?_⟩
  rw [completedSaddleAnnulusRadialInverse_target hab hβ hmono hleft hright]
  exact completedSaddleAnnulusRadialInverse_symm_contDiffOn hab hβ hmono hleft hright hpositive

end
end TightVer401
