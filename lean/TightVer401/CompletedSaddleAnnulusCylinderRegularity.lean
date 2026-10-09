import TightVer401.CompletedSaddleAnnulusCylinderMap

/-! Actual native interior smoothness of the constructed resolved-height
cylinder. The native differential rank application remains separate. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def completedSaddleAnnulusCylinderPolarMap (β : ℝ → ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Coord :=
  completedSaddleAnnulusCylinderPlanePoint (β p.2) p.1

theorem completedSaddleAnnulusCylinderPolarMap_contMDiff {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ (completedSaddleAnnulusCylinderPolarMap β) := by
  have hRadius : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => β p.2) :=
    hβ.contMDiff.comp contMDiff_snd
  have hRad : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p : AddCircle (2 * Real.pi) × ℝ => revolutionCircleRadial p.1) :=
    revolutionCircleRadial_contMDiff.comp contMDiff_fst
  apply contMDiff_pi_space.mpr
  intro i
  exact hRadius.neg.mul
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i.castSucc).contDiff.contMDiff.comp hRad)

private theorem completedSaddleAnnulusCylinderPolarMap_mem
    {A RN : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (Real.pi/2) Real.pi) :
    completedSaddleAnnulusCylinderPolarMap β (q,u) ∈ quadraticRadialFillingOpenAnnulus A RN := by
  have hmid : Real.pi/2 ∈ Icc (Real.pi/2) Real.pi := ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hend : Real.pi ∈ Icc (Real.pi/2) Real.pi := ⟨by linarith [Real.pi_pos],le_rfl⟩
  have hucc : u ∈ Icc (Real.pi/2) Real.pi := ⟨hu.1.le,hu.2.le⟩
  have hlow : A < β u := by rw [← hβA]; exact hMono hmid hucc hu.1
  have hhigh : β u < RN := by rw [← hβRN]; exact hMono hucc hend hu.2
  change A < planarRadius (completedSaddleAnnulusCylinderPlanePoint (β u) q) ∧
    planarRadius (completedSaddleAnnulusCylinderPlanePoint (β u) q) < RN
  rw [completedSaddleAnnulusCylinderPlanePoint_radius (hA.trans hlow)]
  exact ⟨hlow,hhigh⟩

private theorem completedSaddleAnnulusUpperGraph_native_polar (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity r : ℝ)
    (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusUpperGraph G e dInfinity (completedSaddleAnnulusCylinderPlanePoint r q) =
      r • revolutionCircleRadial q +
        (dInfinity-completedSaddleAnnulusGraphHeight G e
          (completedSaddleAnnulusCylinderPlanePoint r q)) • revolutionAxis := by
  ext i
  fin_cases i <;> simp [completedSaddleAnnulusUpperGraph,
    completedSaddleAnnulusCylinderPlanePoint,revolutionCircleRadial,revolutionAxis]

private theorem completedSaddleAnnulusLowerGraph_native_polar (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (dInfinity r : ℝ)
    (q : AddCircle (2 * Real.pi)) :
    completedSaddleAnnulusLowerGraph G e dInfinity (completedSaddleAnnulusCylinderPlanePoint r q) =
      r • revolutionCircleRadial q +
        (completedSaddleAnnulusGraphHeight G e
          (completedSaddleAnnulusCylinderPlanePoint r q)-dInfinity) • revolutionAxis := by
  ext i
  fin_cases i <;> simp [completedSaddleAnnulusLowerGraph,
    completedSaddleAnnulusCylinderPlanePoint,revolutionCircleRadial,revolutionAxis]

/-- Away from the neck the actual upper sheet is literally the actual
smooth Cartesian graph composed with its native polar map. -/
theorem completedSaddleAnnulusCylinderMap_upper_germ
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p.2 ∈ Ioo (Real.pi/2) Real.pi) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β =ᶠ[𝓝 p]
      completedSaddleAnnulusUpperGraph G e dInfinity ∘ completedSaddleAnnulusCylinderPolarMap β := by
  have hV : IsOpen {s : AddCircle (2 * Real.pi) × ℝ |
      Real.pi/2 < s.2 ∧ s.2 < Real.pi} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  filter_upwards [hV.mem_nhds hp] with s hs
  have hy := completedSaddleAnnulusCylinderPolarMap_mem hA hMono hβA hβRN s.1 hs
  change completedSaddleAnnulusCylinderPlanePoint (β s.2) s.1 ∈
    quadraticRadialFillingOpenAnnulus A RN at hy
  change β (completedSaddleAnnulusCylinderPhase s.2) • revolutionCircleRadial s.1 +
    (if s.2 ≤ Real.pi/2 then completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) (completedSaddleAnnulusCylinderPlanePoint
        (β (completedSaddleAnnulusCylinderPhase s.2)) s.1)-dInfinity else dInfinity-
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity (completedSaddleAnnulusGraphHeight G e)
        (completedSaddleAnnulusCylinderPlanePoint (β (completedSaddleAnnulusCylinderPhase s.2)) s.1)) •
          revolutionAxis = _
  rw [completedSaddleAnnulusCylinderPhase_upper hs.1.le,if_neg (not_le_of_gt hs.1),
    completedSaddleAnnulusHeightResolved_eq_interior hy]
  exact (completedSaddleAnnulusUpperGraph_native_polar G e dInfinity (β s.2) s.1).symm

/-- The actual lower sheet uses the reflected real phase, with the same
actual gradient graph and the same potential/inverse. -/
theorem completedSaddleAnnulusCylinderMap_lower_germ
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p.2 ∈ Ioo 0 (Real.pi/2)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β =ᶠ[𝓝 p]
      completedSaddleAnnulusLowerGraph G e dInfinity ∘
        completedSaddleAnnulusCylinderPolarMap (fun u => β (Real.pi-u)) := by
  have hV : IsOpen {s : AddCircle (2 * Real.pi) × ℝ |
      0 < s.2 ∧ s.2 < Real.pi/2} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  filter_upwards [hV.mem_nhds hp] with s hs
  have hu : Real.pi-s.2 ∈ Ioo (Real.pi/2) Real.pi := ⟨by linarith,by linarith⟩
  have hy := completedSaddleAnnulusCylinderPolarMap_mem hA hMono hβA hβRN s.1 hu
  change completedSaddleAnnulusCylinderPlanePoint (β (Real.pi-s.2)) s.1 ∈
    quadraticRadialFillingOpenAnnulus A RN at hy
  change β (completedSaddleAnnulusCylinderPhase s.2) • revolutionCircleRadial s.1 +
    (if s.2 ≤ Real.pi/2 then completedSaddleAnnulusHeightResolved A RN d0 dInfinity
      (completedSaddleAnnulusGraphHeight G e) (completedSaddleAnnulusCylinderPlanePoint
        (β (completedSaddleAnnulusCylinderPhase s.2)) s.1)-dInfinity else dInfinity-
      completedSaddleAnnulusHeightResolved A RN d0 dInfinity (completedSaddleAnnulusGraphHeight G e)
        (completedSaddleAnnulusCylinderPlanePoint (β (completedSaddleAnnulusCylinderPhase s.2)) s.1)) •
          revolutionAxis = _
  rw [completedSaddleAnnulusCylinderPhase_lower hs.2.le,if_pos hs.2.le,
    completedSaddleAnnulusHeightResolved_eq_interior hy]
  exact (completedSaddleAnnulusLowerGraph_native_polar G e dInfinity (β (Real.pi-s.2)) s.1).symm

/-- Actual native infinity smoothness of the constructed cylinder throughout
its open strip. The quadratic puncture data is not needed for this interior
smoothness substep; neck data and actual graph smoothness suffice. -/
theorem completedSaddleAnnulusCylinderMap_contMDiffOn
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2)) :
    ContMDiffOn nativeProductModel 𝓘(ℝ, Ambient) ∞
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (univ ×ˢ Ioo (0 : ℝ) Real.pi) := by
  have hGraphs := completedSaddleAnnulusGraphs_contDiffOn e dInfinity hG hi
  have hUpper : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞
      (completedSaddleAnnulusUpperGraph G e dInfinity) e.target :=
    contMDiffOn_iff_contDiffOn.mpr hGraphs.1
  have hLower : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞
      (completedSaddleAnnulusLowerGraph G e dInfinity) e.target :=
    contMDiffOn_iff_contDiffOn.mpr hGraphs.2
  have hPolar := completedSaddleAnnulusCylinderPolarMap_contMDiff hβ
  have hReflect : ContDiff ℝ ∞ (fun u => β (Real.pi-u)) :=
    hβ.comp (contDiff_const.sub contDiff_id)
  have hPolarReflect := completedSaddleAnnulusCylinderPolarMap_contMDiff hReflect
  intro p hp
  by_cases hm : p.2 = Real.pi/2
  · have hNeckUniform := completedSaddleAnnulusCylinderMap_neck_germ (d0 := d0) e hA hARN hB hL
      hSource hTarget heG hInfinity hβNeck
    have ht : Tendsto (fun s : AddCircle (2 * Real.pi) × ℝ => s.2) (𝓝 p) (𝓝 (Real.pi/2)) := by
      simpa only [hm] using (continuous_snd : Continuous
        (fun s : AddCircle (2 * Real.pi) × ℝ => s.2)).tendsto p
    have hNeck : completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β =ᶠ[𝓝 p]
        (fun s => (A+B*(s.2-Real.pi/2)^2) • revolutionCircleRadial s.1 +
          (2*B*(s.2-Real.pi/2)) • revolutionAxis) := by
      filter_upwards [ht.eventually hNeckUniform] with s hs
      exact hs s.1
    have hRadial : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
        (fun s : AddCircle (2 * Real.pi) × ℝ => A+B*(s.2-Real.pi/2)^2) :=
      contMDiff_const.add (contMDiff_const.mul ((contMDiff_snd.sub contMDiff_const).pow 2))
    have hVertical : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
        (fun s : AddCircle (2 * Real.pi) × ℝ => 2*B*(s.2-Real.pi/2)) :=
      contMDiff_const.mul (contMDiff_snd.sub contMDiff_const)
    have hModel : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
        (fun s : AddCircle (2 * Real.pi) × ℝ =>
          (A+B*(s.2-Real.pi/2)^2) • revolutionCircleRadial s.1 +
            (2*B*(s.2-Real.pi/2)) • revolutionAxis) :=
      (hRadial.smul (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
        (hVertical.smul contMDiff_const)
    exact ((hModel p).congr_of_eventuallyEq hNeck).contMDiffWithinAt
  · rcases lt_or_gt_of_ne hm with hlo | hhi
    · have hu : p.2 ∈ Ioo 0 (Real.pi/2) := ⟨hp.2.1,hlo⟩
      have hRefU : Real.pi-p.2 ∈ Ioo (Real.pi/2) Real.pi := ⟨by linarith,by linarith [hp.2.1]⟩
      have hy : completedSaddleAnnulusCylinderPolarMap (fun u => β (Real.pi-u)) p ∈ e.target := by
        rw [hTarget]
        exact completedSaddleAnnulusCylinderPolarMap_mem hA hMono hβA hβRN p.1 hRefU
      have hSmooth := (hLower.contMDiffAt (e.open_target.mem_nhds hy)).comp p (hPolarReflect p)
      exact (hSmooth.congr_of_eventuallyEq
        (completedSaddleAnnulusCylinderMap_lower_germ G e hA hMono hβA hβRN hu)).contMDiffWithinAt
    · have hu : p.2 ∈ Ioo (Real.pi/2) Real.pi := ⟨hhi,hp.2.2⟩
      have hy : completedSaddleAnnulusCylinderPolarMap β p ∈ e.target := by
        rw [hTarget]
        exact completedSaddleAnnulusCylinderPolarMap_mem hA hMono hβA hβRN p.1 hu
      have hSmooth := (hUpper.contMDiffAt (e.open_target.mem_nhds hy)).comp p (hPolar p)
      exact (hSmooth.congr_of_eventuallyEq
        (completedSaddleAnnulusCylinderMap_upper_germ G e hA hMono hβA hβRN hu)).contMDiffWithinAt

end
end TightVer401

