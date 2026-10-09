import TightVer401.CompletedSaddleAnnulusCylinderMap
import TightVer401.CompletedSaddleAnnulusRadialInverse
import TightVer401.RevolutionEndAngleInverseSmooth
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! The actual upper-strip coordinates of the same resolved cylinder.
The angle, radial inverse, inverse identities and smoothness are constructed
from ordinary scalar parameter data. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem upperChart_phase_lt : Real.pi/2 < Real.pi := by
  linarith [Real.pi_pos]

private theorem upperChart_complex_inverse (y : Coord) :
    seamComplexCoord.symm y = angularDescentComplex y := by
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply,quadraticRadialFillingCoord_complex]

def completedSaddleAnnulusUpperAngle (y : Coord) : AddCircle (2 * Real.pi) :=
  periodProjection (2 * Real.pi) (-seamComplexCoord.symm y).arg

theorem completedSaddleAnnulusUpperAngle_planePoint {r : ℝ} (hr : 0 < r)
    (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusUpperAngle (completedSaddleAnnulusCylinderPlanePoint r q) = q := by
  obtain ⟨θ,rfl⟩ := QuotientAddGroup.mk_surjective q
  change completedSaddleAnnulusUpperAngle
    (completedSaddleAnnulusCylinderPlanePoint r (periodProjection (2 * Real.pi) θ)) = _
  rw [completedSaddleAnnulusCylinderPlanePoint_representative,
    completedSaddleAnnulusUpperAngle,completedSaddleAnnulusPolarPoint_complex]
  simp only [seamComplexCoord.symm_apply_apply,neg_neg]
  change (Complex.arg (quadraticRadialFillingCircle r θ) : Real.Angle) = (θ : Real.Angle)
  rw [← quadraticRadialFillingComplex_coord (quadraticRadialFillingCircle r θ),
    quadraticRadialFillingCircle_coord]
  simpa using (angularDescent_angle_polar (q := ![r,θ]) (by simpa using hr))

theorem completedSaddleAnnulusUpperAngle_reconstruction (y : Coord) :
    completedSaddleAnnulusCylinderPlanePoint (planarRadius y)
      (completedSaddleAnnulusUpperAngle y) = y := by
  rw [completedSaddleAnnulusUpperAngle,
    completedSaddleAnnulusCylinderPlanePoint_representative,
    completedSaddleAnnulusPolarPoint_complex]
  apply seamComplexCoord.symm.injective
  simp only [seamComplexCoord.symm_apply_apply]
  have hr : ‖-seamComplexCoord.symm y‖ = planarRadius y := by
    rw [norm_neg,← quadraticRadialFillingRadius_complex (seamComplexCoord.symm y),
      seamComplexCoord.apply_symm_apply]
  rw [quadraticRadialFillingCircle,circleMap_zero,← hr,
    Complex.norm_mul_exp_arg_mul_I,neg_neg]

private theorem upperChart_complex_nonzero {y : Coord} (hy : 0 < planarRadius y) :
    -seamComplexCoord.symm y ≠ 0 := by
  apply neg_ne_zero.mpr
  apply norm_pos_iff.mp
  rwa [← quadraticRadialFillingRadius_complex (seamComplexCoord.symm y),
    seamComplexCoord.apply_symm_apply]

theorem completedSaddleAnnulusUpperAngle_contMDiffAt {y : Coord}
    (hy : 0 < planarRadius y) :
    ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ completedSaddleAnnulusUpperAngle y := by
  change ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞
    ((fun z : ℂ => periodProjection (2 * Real.pi) z.arg) ∘
      (fun x : Coord => -seamComplexCoord.symm x)) y
  exact (revolutionComplexAngle_contMDiffAt (upperChart_complex_nonzero hy)).comp y
    seamComplexCoord.symm.contDiff.neg.contDiffAt.contMDiffAt

theorem completedSaddleAnnulusCylinderPlanePoint_contMDiff {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ =>
        completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1) := by
  apply contMDiff_pi_space.mpr
  intro i
  have hc : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => revolutionCircleRadial p.1) :=
    revolutionCircleRadial_contMDiff.comp contMDiff_fst
  have hi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i.castSucc).contDiff.contMDiff.comp hc
  exact (hβ.contMDiff.comp contMDiff_snd).neg.mul hi

section Parameter
variable {β : ℝ → ℝ} {A RN : ℝ}
variable (hA : 0 < A) (hβ : ContDiff ℝ ∞ β)
variable (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
variable (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)

private abbrev upperChart_radial :=
  completedSaddleAnnulusRadialInverse upperChart_phase_lt hβ hMono hβA hβRN

def completedSaddleAnnulusUpperChartForward (y : Coord) : AddCircle (2 * Real.pi) × ℝ :=
  (completedSaddleAnnulusUpperAngle y,
    (upperChart_radial hβ hMono hβA hβRN).symm (planarRadius y))

private theorem upperChart_forward_maps :
    MapsTo (completedSaddleAnnulusUpperChartForward hβ hMono hβA hβRN)
      (quadraticRadialFillingOpenAnnulus A RN) (univ ×ˢ Ioo (Real.pi/2) Real.pi) := by
  intro y hy
  refine ⟨mem_univ _,?_⟩
  exact (upperChart_radial hβ hMono hβA hβRN).map_target
    (by rwa [completedSaddleAnnulusRadialInverse_target])

include hA hβ hMono hβA hβRN in
private theorem upperChart_backward_maps :
    MapsTo (fun p : AddCircle (2 * Real.pi) × ℝ =>
      completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1)
      (univ ×ˢ Ioo (Real.pi/2) Real.pi) (quadraticRadialFillingOpenAnnulus A RN) := by
  intro p hp
  have hr : β p.2 ∈ Ioo A RN := by
    have hm := (upperChart_radial hβ hMono hβA hβRN).map_source hp.2
    simpa only [completedSaddleAnnulusRadialInverse_target,
      completedSaddleAnnulusRadialInverse_coe] using hm
  change A < planarRadius (completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1) ∧
    planarRadius (completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1) < RN
  rwa [completedSaddleAnnulusCylinderPlanePoint_radius (hA.trans hr.1)]

include hA in
private theorem upperChart_forward_continuous :
    ContinuousOn (completedSaddleAnnulusUpperChartForward hβ hMono hβA hβRN)
      (quadraticRadialFillingOpenAnnulus A RN) := by
  have ha : ContinuousOn completedSaddleAnnulusUpperAngle
      (quadraticRadialFillingOpenAnnulus A RN) := by
    intro y hy
    exact ((completedSaddleAnnulusUpperAngle_contMDiffAt (hA.trans hy.1)).continuousAt).continuousWithinAt
  have hr : ContinuousOn (fun y : Coord =>
      (upperChart_radial hβ hMono hβA hβRN).symm (planarRadius y))
      (quadraticRadialFillingOpenAnnulus A RN) :=
    (upperChart_radial hβ hMono hβA hβRN).symm.continuousOn.comp
    quadraticRadialFillingRadius_continuous.continuousOn
    (fun y hy => by
      change planarRadius y ∈ (upperChart_radial hβ hMono hβA hβRN).target
      rwa [completedSaddleAnnulusRadialInverse_target])
  exact ha.prodMk hr

/-- Actual upper-strip coordinates, retaining the literal forward and backward maps. -/
def completedSaddleAnnulusUpperChart :
    OpenPartialHomeomorph Coord (AddCircle (2 * Real.pi) × ℝ) where
  toFun := completedSaddleAnnulusUpperChartForward hβ hMono hβA hβRN
  invFun := fun p => completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1
  source := quadraticRadialFillingOpenAnnulus A RN
  target := univ ×ˢ Ioo (Real.pi/2) Real.pi
  map_source' := upperChart_forward_maps hβ hMono hβA hβRN
  map_target' := upperChart_backward_maps hA hβ hMono hβA hβRN
  left_inv' := by
    intro y hy
    have hr := (upperChart_radial hβ hMono hβA hβRN).right_inv
      (show planarRadius y ∈ (upperChart_radial hβ hMono hβA hβRN).target by
        rwa [completedSaddleAnnulusRadialInverse_target])
    change completedSaddleAnnulusCylinderPlanePoint
      (β ((upperChart_radial hβ hMono hβA hβRN).symm (planarRadius y)))
      (completedSaddleAnnulusUpperAngle y) = y
    change β ((upperChart_radial hβ hMono hβA hβRN).symm (planarRadius y)) = planarRadius y at hr
    rw [hr]
    exact completedSaddleAnnulusUpperAngle_reconstruction y
  right_inv' := by
    intro p hp
    have hr : 0 < β p.2 := by
      have hm := upperChart_backward_maps hA hβ hMono hβA hβRN hp
      have hr' := (upperChart_radial hβ hMono hβA hβRN).map_source hp.2
      rw [completedSaddleAnnulusRadialInverse_target] at hr'
      exact hA.trans hr'.1
    apply Prod.ext
    · exact completedSaddleAnnulusUpperAngle_planePoint hr p.1
    · change (upperChart_radial hβ hMono hβA hβRN).symm
        (planarRadius (completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1)) = p.2
      rw [completedSaddleAnnulusCylinderPlanePoint_radius hr]
      exact (upperChart_radial hβ hMono hβA hβRN).left_inv hp.2
  continuousOn_toFun := upperChart_forward_continuous hA hβ hMono hβA hβRN
  continuousOn_invFun := (completedSaddleAnnulusCylinderPlanePoint_contMDiff hβ).continuous.continuousOn
  open_source := (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
    (isOpen_lt quadraticRadialFillingRadius_continuous continuous_const)
  open_target := isOpen_univ.prod isOpen_Ioo

theorem completedSaddleAnnulusUpperChart_source :
    (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).source =
      quadraticRadialFillingOpenAnnulus A RN := rfl

theorem completedSaddleAnnulusUpperChart_target :
    (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).target =
      univ ×ˢ Ioo (Real.pi/2) Real.pi := rfl

theorem completedSaddleAnnulusUpperChart_apply (y : Coord) :
    completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN y =
      (periodProjection (2 * Real.pi) (-seamComplexCoord.symm y).arg,
        (completedSaddleAnnulusRadialInverse upperChart_phase_lt hβ hMono hβA hβRN).symm
          (planarRadius y)) := rfl

theorem completedSaddleAnnulusUpperChart_symm_apply (p : AddCircle (2 * Real.pi) × ℝ) :
    (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm p =
      completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1 := rfl

theorem completedSaddleAnnulusUpperChart_contMDiffOn
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) :
    ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
      (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN)
      (quadraticRadialFillingOpenAnnulus A RN) := by
  intro y hy
  have hrad : ContDiffAt ℝ ∞ planarRadius y := by
    apply planarRadius_contDiffOn.contDiffAt
    exact (isOpen_lt continuous_const ((continuous_apply 0).pow 2 |>.add
      ((continuous_apply 1).pow 2))).mem_nhds (Real.sqrt_pos.mp (hA.trans hy.1))
  have hi := completedSaddleAnnulusRadialInverse_symm_contDiffOn upperChart_phase_lt
    hβ hMono hβA hβRN hPositive
  have hInv : ContDiffAt ℝ ∞ (upperChart_radial hβ hMono hβA hβRN).symm (planarRadius y) :=
    (hi _ hy).contDiffAt (isOpen_Ioo.mem_nhds hy)
  exact ((completedSaddleAnnulusUpperAngle_contMDiffAt (hA.trans hy.1)).prodMk
    (hInv.comp y hrad).contMDiffAt).contMDiffWithinAt

theorem completedSaddleAnnulusUpperChart_symm_contMDiff :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞
      (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm :=
  completedSaddleAnnulusCylinderPlanePoint_contMDiff hβ

/-- Compose the actual upper annulus coordinates with the same actual gradient map. -/
def completedSaddleAnnulusUpperSupportChart (e : OpenPartialHomeomorph Coord Coord) :
    OpenPartialHomeomorph Coord (AddCircle (2 * Real.pi) × ℝ) :=
  e.trans (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN)

theorem completedSaddleAnnulusUpperSupportChart_source (e : OpenPartialHomeomorph Coord Coord)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN) :
    (completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e).source = e.source := by
  rw [completedSaddleAnnulusUpperSupportChart,OpenPartialHomeomorph.trans_source]
  apply inter_eq_left.mpr
  intro p hp
  change e p ∈ (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).source
  simpa only [completedSaddleAnnulusUpperChart_source,← hTarget] using e.map_source hp

theorem completedSaddleAnnulusUpperSupportChart_target (e : OpenPartialHomeomorph Coord Coord)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN) :
    (completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e).target =
      univ ×ˢ Ioo (Real.pi/2) Real.pi := by
  rw [completedSaddleAnnulusUpperSupportChart,OpenPartialHomeomorph.trans_target]
  apply inter_eq_left.mpr
  intro p hp
  change (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm p ∈ e.target
  simpa only [completedSaddleAnnulusUpperChart_source,← hTarget] using
    (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).map_target hp

theorem completedSaddleAnnulusUpperSupportChart_contMDiffOn {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) :
    ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
      (completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e) e.source ∧
    ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞
      (completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e).symm
      (univ ×ˢ Ioo (Real.pi/2) Real.pi) := by
  have he : ContDiffOn ℝ ∞ e e.source :=
    (planarGradient_contDiffOn hG e.open_source).congr heG
  constructor
  · change ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
      ((completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN) ∘ e) e.source
    exact (completedSaddleAnnulusUpperChart_contMDiffOn hA hβ hMono hβA hβRN hPositive).comp
      he.contMDiffOn (fun p hp => by
        change e p ∈ quadraticRadialFillingOpenAnnulus A RN
        rw [← hTarget]
        exact e.map_source hp)
  · change ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞
      (e.symm ∘ (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm)
      (univ ×ˢ Ioo (Real.pi/2) Real.pi)
    exact hi.contMDiffOn.comp
      (completedSaddleAnnulusUpperChart_symm_contMDiff hA hβ hMono hβA hβRN).contMDiffOn
      (fun p hp => by
        change (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm p ∈ e.target
        rw [hTarget]
        exact (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).map_target hp)

include hA hβ hMono hβA hβRN in
/-- The literal constructed cylinder in the upper strip is the same actual upper graph. -/
theorem completedSaddleAnnulusCylinderMap_upperGraph
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) (d0 dInfinity : ℝ)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ univ ×ˢ Ioo (Real.pi/2) Real.pi) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p =
      completedSaddleAnnulusUpperGraph G e dInfinity
        (completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1) := by
  have hy := upperChart_backward_maps hA hβ hMono hβA hβRN hp
  rw [completedSaddleAnnulusCylinderMap,completedSaddleAnnulusCylinderPhase_upper hp.2.1.le,
    if_neg (not_le_of_gt hp.2.1),completedSaddleAnnulusHeightResolved_eq_interior hy]
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective p.1
  dsimp only
  rw [← hθ]
  change β p.2 • revolutionCircleRadial (periodProjection (2 * Real.pi) θ) +
    (dInfinity-completedSaddleAnnulusGraphHeight G e
      (completedSaddleAnnulusCylinderPlanePoint (β p.2) (periodProjection (2 * Real.pi) θ))) •
      revolutionAxis = completedSaddleAnnulusUpperGraph G e dInfinity
        (completedSaddleAnnulusCylinderPlanePoint (β p.2) (periodProjection (2 * Real.pi) θ))
  rw [completedSaddleAnnulusCylinderPlanePoint_representative,
    revolutionCircleRadial_representative,completedSaddleAnnulusUpperGraph_polar]

/-- Exact support-coordinate identity for c1, without an incoming cylinder-output premise. -/
theorem completedSaddleAnnulusUpperSupportChart_support {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (d0 dInfinity : ℝ)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {p : Coord} (hp : p ∈ e.source) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β
      (completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e p) =
      -planarSupportMap G p + dInfinity • revolutionAxis := by
  have hep : e p ∈ quadraticRadialFillingOpenAnnulus A RN := by
    simpa only [← hTarget] using e.map_source hp
  have hc := (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).map_source hep
  change completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β
    (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN (e p)) = _
  rw [completedSaddleAnnulusCylinderMap_upperGraph hA hβ hMono hβA hβRN G e d0 dInfinity hc]
  change completedSaddleAnnulusUpperGraph G e dInfinity
    ((completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).symm
      (completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN (e p))) = _
  rw [(completedSaddleAnnulusUpperChart hA hβ hMono hβA hβRN).left_inv hep,
    completedSaddleAnnulusUpperGraph_support e heG dInfinity (e.map_source hp),e.left_inv hp]

end Parameter
end
end TightVer401
