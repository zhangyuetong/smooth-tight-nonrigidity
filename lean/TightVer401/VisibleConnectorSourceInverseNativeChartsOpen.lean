import TightVer401.VisibleConnectorSourceInverseNativeChartsPeriod
import TightVer401.VisibleConnectorSourceInverseNativeChartsClosed
import TightVer401.CompletedSaddleAnnulusUpperChart
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! The actual whole quotient-circle open round annulus. The existing upper
chart supplies the inverse and its smoothness; negation corrects its minus-polar
convention, retaining the SAME positive native round map and physical period. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

private def nativeOpenBeta (u : ℝ) : ℝ := 2*u/Real.pi
private theorem nativeOpenBeta_smooth : ContDiff ℝ ∞ nativeOpenBeta :=
  (contDiff_const.mul contDiff_id).div_const Real.pi
private theorem nativeOpenBeta_mono : StrictMonoOn nativeOpenBeta (Icc (Real.pi/2) Real.pi) := by
  intro a _ b _ hab
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hab (by norm_num)) Real.pi_pos
private theorem nativeOpenBeta_left : nativeOpenBeta (Real.pi/2) = 1 := by
  unfold nativeOpenBeta
  field_simp [Real.pi_pos.ne']
private theorem nativeOpenBeta_right : nativeOpenBeta Real.pi = 2 := by
  unfold nativeOpenBeta
  field_simp [Real.pi_pos.ne']
private theorem nativeOpenBeta_derivative (u : ℝ) : 0 < deriv nativeOpenBeta u := by
  unfold nativeOpenBeta
  rw [deriv_div_const,deriv_const_mul_id]
  exact div_pos (by norm_num) Real.pi_pos

private abbrev nativeOpenUpper := completedSaddleAnnulusUpperChart zero_lt_one
  nativeOpenBeta_smooth nativeOpenBeta_mono nativeOpenBeta_left nativeOpenBeta_right
private def nativeOpenAffine (t : ℝ) : ℝ := Real.pi*(1+t)/2
private def nativeOpenAffineInverse (u : ℝ) : ℝ := 2*u/Real.pi-1
private theorem nativeOpenAffine_inverse (u : ℝ) :
    nativeOpenAffine (nativeOpenAffineInverse u) = u := by
  unfold nativeOpenAffine nativeOpenAffineInverse
  field_simp [Real.pi_pos.ne']
  ring
private theorem nativeOpenAffineInverse_affine (t : ℝ) :
    nativeOpenAffineInverse (nativeOpenAffine t) = t := by
  unfold nativeOpenAffine nativeOpenAffineInverse
  field_simp [Real.pi_pos.ne']
  ring
private theorem nativeOpenBeta_affine (t : ℝ) : nativeOpenBeta (nativeOpenAffine t) = 1+t := by
  unfold nativeOpenBeta nativeOpenAffine
  field_simp [Real.pi_pos.ne']
private theorem nativeOpenAffine_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    nativeOpenAffine t ∈ Ioo (Real.pi/2) Real.pi := by
  unfold nativeOpenAffine
  constructor
  · have hpt : 0 < Real.pi*t := mul_pos Real.pi_pos ht.1
    linarith
  · have hpt : 0 < Real.pi*(1-t) := mul_pos Real.pi_pos (by linarith [ht.2])
    linarith
private theorem nativeOpenAffineInverse_mem {u : ℝ} (hu : u ∈ Ioo (Real.pi/2) Real.pi) :
    nativeOpenAffineInverse u ∈ Ioo (0 : ℝ) 1 := by
  have hd : 1 < 2*u/Real.pi ∧ 2*u/Real.pi < 2 :=
    ⟨(lt_div_iff₀ Real.pi_pos).mpr (by linarith [hu.1]),
      (div_lt_iff₀ Real.pi_pos).mpr (by linarith [hu.2])⟩
  unfold nativeOpenAffineInverse
  constructor <;> linarith [hd.1,hd.2]
private theorem nativeOpen_radius_neg (y : Coord) : planarRadius (-y) = planarRadius y := by
  simp only [planarRadius,Pi.neg_apply,neg_sq]
private def nativeOpenBand : Set Coord := {y | 1 < planarRadius y ∧ planarRadius y < 2}
private theorem nativeOpenBand_open : IsOpen nativeOpenBand :=
  (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
    (isOpen_lt quadraticRadialFillingRadius_continuous continuous_const)
private theorem nativeOpenBand_neg {y : Coord} (hy : y ∈ nativeOpenBand) :
    -y ∈ nativeOpenUpper.source := by
  change 1 < planarRadius (-y) ∧ planarRadius (-y) < 2
  simpa only [nativeOpenBand,Set.mem_setOf_eq,nativeOpen_radius_neg] using hy

private def nativeOpenInput (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × Ioo (0 : ℝ) 1) : AddCircle (2*Real.pi) × ℝ :=
  (visibleConnectorSourceInverseNativePeriodRescale L p.1, nativeOpenAffine p.2)
private theorem nativeOpenInput_mem (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × Ioo (0 : ℝ) 1) : nativeOpenInput L p ∈ nativeOpenUpper.target :=
  ⟨mem_univ _,nativeOpenAffine_mem p.2.property⟩

private theorem nativeOpen_forward_upper (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × Ioo (0 : ℝ) 1) :
    visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ)) =
      -nativeOpenUpper.symm (nativeOpenInput L p) := by
  rcases p with ⟨q,t⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective q
  have hs' : periodProjection L s = q := hs
  rw [← hs']
  rw [visibleConnectorSourceInverse_native_round_representative]
  change saddlePolarChart ![1+(t : ℝ),2*Real.pi*s/L] =
    -completedSaddleAnnulusCylinderPlanePoint
      (nativeOpenBeta (nativeOpenAffine t))
      (visibleConnectorSourceInverseNativePeriodRescale L (periodProjection L s))
  rw [nativeOpenBeta_affine,visibleConnectorSourceInverseNativePeriodRescale_representative,
    completedSaddleAnnulusCylinderPlanePoint_representative]
  simp only [completedSaddleAnnulusPolarPoint,neg_neg,
    quadraticRadialFillingCircle_coord]

private def nativeOpenInverse (L : ℝ) [Fact (0 < L)]
    (y : Coord) : AddCircle L × Ioo (0 : ℝ) 1 := by
  classical
  exact if hy : y ∈ nativeOpenBand then
    ((visibleConnectorSourceInverseNativePeriodRescale L).symm (nativeOpenUpper (-y)).1,
      ⟨nativeOpenAffineInverse (nativeOpenUpper (-y)).2,
        nativeOpenAffineInverse_mem (nativeOpenUpper.map_source (nativeOpenBand_neg hy)).2⟩)
  else (0,⟨1/2,by constructor <;> norm_num⟩)

private theorem nativeOpenInput_inverse (L : ℝ) [Fact (0 < L)]
    {y : Coord} (hy : y ∈ nativeOpenBand) :
    nativeOpenInput L (nativeOpenInverse L y) = nativeOpenUpper (-y) := by
  apply Prod.ext
  · simp only [nativeOpenInput,nativeOpenInverse,dif_pos hy,
      Homeomorph.apply_symm_apply]
  · simp only [nativeOpenInput,nativeOpenInverse,dif_pos hy]
    exact nativeOpenAffine_inverse _

private theorem nativeOpen_forward_mem (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × Ioo (0 : ℝ) 1) :
    visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ)) ∈ nativeOpenBand := by
  have hpositive : 0 < 1+(p.2 : ℝ) := by linarith [p.2.property.1]
  change 1 < planarRadius (visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ))) ∧
    planarRadius (visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ))) < 2
  rw [visibleConnectorSourceInverse_native_round_radius L _ hpositive]
  constructor <;> linarith [p.2.property.1,p.2.property.2]

private theorem nativeOpenInverse_contMDiffOn (L : ℝ) [Fact (0 < L)] :
    ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ (nativeOpenInverse L) nativeOpenBand := by
  intro y hy
  have hUpper : ContMDiffAt 𝓘(ℝ, Coord) nativeProductModel ∞
      (fun z : Coord => nativeOpenUpper (-z)) y := by
    have hs := completedSaddleAnnulusUpperChart_contMDiffOn zero_lt_one nativeOpenBeta_smooth
      nativeOpenBeta_mono nativeOpenBeta_left nativeOpenBeta_right (fun u _ => nativeOpenBeta_derivative u)
    have hneg := nativeOpenBand_neg hy
    exact ((hs (-y) hneg).contMDiffAt (by
      change nativeOpenBand ∈ 𝓝 (-y)
      exact nativeOpenBand_open.mem_nhds (by simpa only [nativeOpenBand,Set.mem_setOf_eq,nativeOpen_radius_neg] using hy))).comp y
      contDiff_id.neg.contDiffAt.contMDiffAt
  have hFirst : ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun z => (nativeOpenInverse L z).1) y := by
    have hs := (visibleConnectorSourceInverseNativePeriodRescale_symm_contMDiff L).contMDiffAt.comp y
      (contMDiff_fst.contMDiffAt.comp y hUpper)
    apply hs.congr_of_eventuallyEq
    filter_upwards [nativeOpenBand_open.mem_nhds hy] with z hz
    simp only [nativeOpenInverse,dif_pos hz,Function.comp_def]
  have hVal : ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞
      (fun z => ((nativeOpenInverse L z).2 : ℝ)) y := by
    have ha : ContDiff ℝ ∞ nativeOpenAffineInverse :=
      ((contDiff_const.mul contDiff_id).div_const Real.pi).sub contDiff_const
    have hs := ha.contMDiff.contMDiffAt.comp y (contMDiff_snd.contMDiffAt.comp y hUpper)
    apply hs.congr_of_eventuallyEq
    filter_upwards [nativeOpenBand_open.mem_nhds hy] with z hz
    simp only [nativeOpenInverse,dif_pos hz,Function.comp_def]
  have hSecond : ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun z => (nativeOpenInverse L z).2) y :=
    (ContMDiffAt.subtypeVal_comp_iff (⟨Ioo (0 : ℝ) 1,isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ)
      (fun z => (nativeOpenInverse L z).2) y).mp hVal
  exact (hFirst.prodMk hSecond).contMDiffWithinAt

/-- Whole native open round annulus, retaining the literal shared positive map. -/
def visibleConnectorSourceInverse_native_round_chart (L : ℝ) [Fact (0 < L)] :
    OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) 1) Coord where
  toFun := fun p => visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ))
  invFun := nativeOpenInverse L
  source := univ
  target := nativeOpenBand
  map_source' := fun p _ => nativeOpen_forward_mem L p
  map_target' := fun _ _ => mem_univ _
  left_inv' := by
    intro p _
    have hy := nativeOpen_forward_mem L p
    have hUpper : nativeOpenUpper (-visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ))) =
        nativeOpenInput L p := by
      rw [nativeOpen_forward_upper,neg_neg]
      exact nativeOpenUpper.right_inv (nativeOpenInput_mem L p)
    apply Prod.ext
    · simp only [nativeOpenInverse,dif_pos hy,hUpper,nativeOpenInput,
        Homeomorph.symm_apply_apply]
    · apply Subtype.ext
      change ((nativeOpenInverse L (visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ)))).2 : ℝ) = p.2
      simp only [nativeOpenInverse,dif_pos hy,hUpper,nativeOpenInput]
      exact nativeOpenAffineInverse_affine _
  right_inv' := by
    intro y hy
    rw [nativeOpen_forward_upper,nativeOpenInput_inverse L hy,
      nativeOpenUpper.left_inv (nativeOpenBand_neg hy),neg_neg]
  open_source := isOpen_univ
  open_target := nativeOpenBand_open
  continuousOn_toFun := ((visibleConnectorSourceInverse_native_round_continuous L).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
  continuousOn_invFun := (nativeOpenInverse_contMDiffOn L).continuousOn

theorem visibleConnectorSourceInverse_native_round_chart_source (L : ℝ) [Fact (0 < L)] :
    (visibleConnectorSourceInverse_native_round_chart L).source = univ := rfl

theorem visibleConnectorSourceInverse_native_round_chart_target (L : ℝ) [Fact (0 < L)] :
    (visibleConnectorSourceInverse_native_round_chart L).target =
      {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} := rfl

theorem visibleConnectorSourceInverse_native_round_chart_apply (L : ℝ) [Fact (0 < L)]
    (p : AddCircle L × Ioo (0 : ℝ) 1) :
    visibleConnectorSourceInverse_native_round_chart L p =
      visibleConnectorSourceInverseNativeRound L (p.1,(p.2 : ℝ)) := rfl

theorem visibleConnectorSourceInverse_native_round_chart_contMDiff (L : ℝ) [Fact (0 < L)] :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ (visibleConnectorSourceInverse_native_round_chart L) := by
  have hVal : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Ioo (0 : ℝ) 1 => (p.2 : ℝ)) :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ))
      (U := (⟨Ioo (0 : ℝ) 1,isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ))).comp contMDiff_snd
  have ha : ContDiff ℝ ∞ nativeOpenAffine :=
    (contDiff_const.mul (contDiff_const.add contDiff_id)).div_const 2
  have hInput : ContMDiff nativeProductModel nativeProductModel ∞ (nativeOpenInput L) :=
    ((visibleConnectorSourceInverseNativePeriodRescale_contMDiff L).comp contMDiff_fst).prodMk
      (ha.contMDiff.comp hVal)
  have hs := (completedSaddleAnnulusUpperChart_symm_contMDiff zero_lt_one nativeOpenBeta_smooth
    nativeOpenBeta_mono nativeOpenBeta_left nativeOpenBeta_right).comp hInput
  have heq : (visibleConnectorSourceInverse_native_round_chart L :
      (AddCircle L × Ioo (0 : ℝ) 1) → Coord) = fun p => -nativeOpenUpper.symm (nativeOpenInput L p) := by
    funext p
    exact nativeOpen_forward_upper L p
  rw [heq]
  exact hs.neg

theorem visibleConnectorSourceInverse_native_round_chart_symm_contMDiffOn (L : ℝ) [Fact (0 < L)] :
    ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
      (visibleConnectorSourceInverse_native_round_chart L).symm
      {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} :=
  nativeOpenInverse_contMDiffOn L

end
end TightVer401
