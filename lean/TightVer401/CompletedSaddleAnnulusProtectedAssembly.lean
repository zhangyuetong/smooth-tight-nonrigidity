import TightVer401.CompletedSaddleAnnulusCylinderAssembly
import TightVer401.CompletedSaddleAnnulusProtectedTransfer
import TightVer401.CompletedSaddleAnnulusGeometryOutput
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Protected geometry for the same actual constructed saddle cylinder.
Original support coordinates are restricted to the ordinary unchanged open
region; actual scalar agreement there supplies the required support germ. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Actual scalar agreement on an actual open neighborhood gives the literal
scalar germ, without an incoming unchanged-germ package. -/
theorem completedSaddleAnnulusProtected_scalar_germ {G G0 : Coord → ℝ}
    {W : Set Coord} (hW : IsOpen W) (hEq : EqOn G G0 W) {y : Coord} (hy : y ∈ W) :
    G =ᶠ[𝓝 y] G0 := by
  filter_upwards [hW.mem_nhds hy] with x hx
  exact hEq hx

/-- Restrict the original actual support chart to the actual unchanged
open region by an ordinary open identity restriction. -/
def completedSaddleAnnulusOriginalSupportRestriction
    {T w : ℝ} [Fact (0 < T)]
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0:ℝ) w) Coord)
    (W : Set Coord) (hW : IsOpen W) :
    OpenPartialHomeomorph (AddCircle T × Ioo (0:ℝ) w) Coord :=
  c0.trans (OpenPartialHomeomorph.ofSet W hW)

/-- Construct the protected band for the SAME literal cylinder from actual
support coordinates and actual unchanged scalar data. -/
def completedSaddleAnnulusProtectedBand_from_data
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (K : Set (AddCircle T × Ioo (0:ℝ) w))
    {G G0 : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hβDerivative : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0:ℝ) w) Coord)
    (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
    (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
    (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
    (hK : K ⊆ c0.source) {W : Set Coord} (hW : IsOpen W) (hWe : W ⊆ e.source)
    (hKW : c0 '' K ⊆ W) (hEq : EqOn G G0 W) :
    CompletedSaddleAnnulusProtectedBand d
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) K dInfinity := by
  let c := completedSaddleAnnulusOriginalSupportRestriction c0 W hW
  let c1 := completedSaddleAnnulusUpperSupportChart hA hβ hMono hβA hβRN e
  have hcSource : c.source = c0.source ∩ c0 ⁻¹' W := rfl
  have hcTarget : c.target = W ∩ c0.target := rfl
  have hcFun : (c : (AddCircle T × Ioo (0:ℝ) w) → Coord) = c0 := rfl
  have hcInv : (c.symm : Coord → (AddCircle T × Ioo (0:ℝ) w)) = c0.symm := rfl
  have hc1Source : c1.source = e.source :=
    completedSaddleAnnulusUpperSupportChart_source hA hβ hMono hβA hβRN e hTarget
  have hc1Target : c1.target = univ ×ˢ Ioo (Real.pi/2) Real.pi :=
    completedSaddleAnnulusUpperSupportChart_target hA hβ hMono hβA hβRN e hTarget
  have hSmooth := completedSaddleAnnulusUpperSupportChart_contMDiffOn hA hβ hMono hβA hβRN
    e hTarget hG hi heG hβDerivative
  apply completedSaddleAnnulusProtectedBand_of_support_coordinates d
    (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) K dInfinity G0 G c c1
  · intro p hp
    rw [OpenPartialHomeomorph.trans_source]
    have hpW : c0 p ∈ W := hKW ⟨p,hp,rfl⟩
    refine ⟨by rw [hcSource]; exact ⟨hK hp,hpW⟩,?_⟩
    rw [hc1Source]
    exact hWe hpW
  · rw [hc1Target]
    intro p hp
    refine ⟨mem_univ _,?_⟩
    exact ⟨lt_trans (by positivity : (0:ℝ) < Real.pi/2) hp.2.1,hp.2.2⟩
  · rw [hcFun,hcSource]
    exact hc0.mono inter_subset_left
  · rw [hcInv,hcTarget]
    exact hci0.mono inter_subset_right
  · rw [hc1Source]
    exact hSmooth.1
  · rw [hc1Target]
    exact hSmooth.2
  · intro p hp
    rw [hcSource] at hp
    exact hBand p hp.1
  · intro p hp
    have hpW : c p ∈ W := by
      have hpc : p ∈ c.source := hp.1
      rw [hcSource] at hpc
      exact hpc.2
    exact completedSaddleAnnulusProtected_scalar_germ hW hEq hpW
  · intro p hp
    rw [hc1Source] at hp
    exact completedSaddleAnnulusUpperSupportChart_support hA hβ hMono hβA hβRN
      e d0 dInfinity hTarget heG hp

/-- Actual strict height bounds throughout the same constructed open strip.
This includes the neck, whose resolved height is the actual inner boundary value. -/
theorem completedSaddleAnnulusCylinderMap_height_separation
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN μ B ε L d0 dInfinity : ℝ}
    (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ) (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
      G p = RN*planarRadius p-μ*planarRadius p^2/2+d0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A*planarRadius p-B/planarRadius p+dInfinity)
    {β : ℝ → ℝ} (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ univ ×ˢ Ioo (0:ℝ) Real.pi) :
    -(dInfinity-d0) < completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 ∧
      completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 < dInfinity-d0 := by
  have hHeight := completedSaddleAnnulusActualHeight_resolution e hA hARN hμ hB hε hL
    hSource hTarget hG hi heG hQuadratic hInfinity
  have hClosed := Ioo_subset_Icc_self hp.2
  have hr := completedSaddleAnnulusCylinderMap_radius_mem hMono hβA hβRN hClosed
  have hrpos := hA.trans_le hr.1
  let y := completedSaddleAnnulusCylinderPlanePoint (β (completedSaddleAnnulusCylinderPhase p.2)) p.1
  have hyr : planarRadius y = β (completedSaddleAnnulusCylinderPhase p.2) :=
    completedSaddleAnnulusCylinderPlanePoint_radius hrpos p.1
  have hyrRN : planarRadius y < RN := by
    rw [hyr,← hβRN]
    apply hMono (completedSaddleAnnulusCylinderPhase_mem hClosed)
      (show Real.pi ∈ Icc (Real.pi/2) Real.pi from ⟨by linarith [Real.pi_pos],le_rfl⟩)
    change max p.2 (Real.pi-p.2) < Real.pi
    exact max_lt hp.2.2 (by linarith [hp.2.1])
  have hyClosed : y ∈ quadraticRadialFillingClosedAnnulus A RN := by
    change A ≤ planarRadius y ∧ planarRadius y ≤ RN
    simpa only [hyr,mem_Icc] using hr
  let Z := completedSaddleAnnulusHeightResolved A RN d0 dInfinity
    (completedSaddleAnnulusGraphHeight G e) y
  have hzTop : Z ≤ dInfinity := (hHeight.2.2.2.2 y hyClosed).2
  have hzBottom : d0 < Z := by
    by_cases hInner : planarRadius y = A
    · change d0 < completedSaddleAnnulusHeightResolved A RN d0 dInfinity
        (completedSaddleAnnulusGraphHeight G e) y
      rw [completedSaddleAnnulusHeightResolved_inner_boundary hInner]
      exact hHeight.2.2.1
    · have hyOpen : y ∈ quadraticRadialFillingOpenAnnulus A RN :=
        ⟨lt_of_le_of_ne hyClosed.1 (Ne.symm hInner),hyrRN⟩
      exact (hHeight.2.2.2.1 y hyOpen).1
  have hv : completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p 2 =
      if p.2 ≤ Real.pi/2 then Z-dInfinity else dInfinity-Z := by
    simp [completedSaddleAnnulusCylinderMap,revolutionCircleRadial,revolutionAxis,Z,y]
    all_goals split_ifs <;> simp
  rw [hv]
  split_ifs <;> constructor <;> linarith [hHeight.2.2.1]

section OrdinaryData
variable {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
variable (K : Set (AddCircle T × Ioo (0:ℝ) w))
variable {G G0 : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
variable {A RN μ B ε L d0 dInfinity : ℝ}
variable (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ) (hB : 0 < B) (hε : 0 < ε) (hL : 0 < L)
variable (hSource : e.source = {p : Coord | 0 < planarRadius p})
variable (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
variable (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
variable (heG : ∀ p ∈ e.source, e p = planarGradient G p)
variable (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
variable (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
  G p = RN*planarRadius p-μ*planarRadius p^2/2+d0)
variable (hInfinity : ∀ p : Coord, L < planarRadius p →
  G p = A*planarRadius p-B/planarRadius p+dInfinity)
variable (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0:ℝ) w) Coord)
variable (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
variable (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
variable (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
variable (hK : K ⊆ c0.source) {W : Set Coord} (hW : IsOpen W) (hWe : W ⊆ e.source)
variable (hKW : c0 '' K ⊆ W) (hEq : EqOn G G0 W)

include e hA hARN hμ hB hε hL hSource hTarget hG hi heG hNeg hQuadratic hInfinity
  c0 hc0 hci0 hBand hK hW hWe hKW hEq in
/-- Construct the genuine protected geometry output from SAME ordinary G/e
data and actual original support coordinates; no output package is a premise. -/
theorem exists_completedSaddleAnnulusGeometryOutput :
    d0 < dInfinity ∧ ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧ StrictMonoOn β (Icc (Real.pi/2) Real.pi) ∧
      β (Real.pi/2) = A ∧ β Real.pi = RN ∧
      (∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) ∧
      β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2) ∧
      β =ᶠ[𝓝 Real.pi]
        (fun u => RN-2*Real.sqrt (μ*(dInfinity-d0))*Real.cos (u/2)) ∧
      ∃ Q : CompletedSaddleAnnulusGeometryOutput d K RN μ (dInfinity-d0),
        Q.cylinder.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β ∧
        Q.verticalOffset = dInfinity := by
  obtain ⟨hHeight,β,hβ,hMono,hβA,hβRN,hβDerivative,hβNeck,hβNorth,
    D,hLiteral,hSigns,hZero,hCurvature⟩ :=
    exists_completedSaddleAnnulusCylinderInput e hA hARN hμ hB hε hL hSource hTarget
      hG hi heG hQuadratic hInfinity hNeg
  let P := completedSaddleAnnulusProtectedBand_from_data (d0 := d0) (dInfinity := dInfinity)
    d K e hA hTarget hG hi heG
    hβ hMono hβA hβRN hβDerivative c0 hc0 hci0 hBand hK hW hWe hKW hEq
  let PD : CompletedSaddleAnnulusProtectedBand d D.saddle K dInfinity := by
    rw [hLiteral]
    exact P
  let Q : CompletedSaddleAnnulusGeometryOutput d K RN μ (dInfinity-d0) := {
    cylinder := D
    verticalOffset := dInfinity
    protectedBand := PD
    height_separation := by
      intro p hp
      rw [hLiteral]
      exact completedSaddleAnnulusCylinderMap_height_separation e hA hARN hμ hB hε hL
        hSource hTarget hG hi heG hQuadratic hInfinity hMono hβA hβRN hp
    curvature_neg := by
      intro p hp
      rw [← nativeProductPlane_coordinate_curvature D.saddle p]
      exact hCurvature p hp }
  exact ⟨hHeight,β,hβ,hMono,hβA,hβRN,hβDerivative,hβNeck,hβNorth,Q,hLiteral,rfl⟩

end OrdinaryData
end
end TightVer401
