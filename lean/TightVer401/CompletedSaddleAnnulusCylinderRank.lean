import TightVer401.CompletedSaddleAnnulusCylinderRegularity
import TightVer401.RevolutionEndImmersion

/-! Actual differential rank for the same native cylinder. Polar rank is
calculated from actual derivatives; quotient transport and neck immersion
reuse retained actual geometry. No rank-output package is supplied. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private def completedSaddleAnnulusPolarRankRepresentative (β : ℝ → ℝ) (p : ℝ × ℝ) : Coord :=
  ![-β p.2 * Real.cos p.1,-β p.2 * Real.sin p.1]

private theorem completedSaddleAnnulusPolarRankRepresentative_contDiff
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (completedSaddleAnnulusPolarRankRepresentative β) := by
  have hb := hβ.comp (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2))
  have hc := Real.contDiff_cos.comp (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
  have hs := Real.contDiff_sin.comp (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hb.neg.mul hc
  · exact hb.neg.mul hs
private theorem completedSaddleAnnulusPolarRankRepresentative_fderiv
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (p v : ℝ × ℝ) :
    fderiv ℝ (completedSaddleAnnulusPolarRankRepresentative β) p v =
      ![-deriv β p.2 * v.2 * Real.cos p.1 + β p.2 * v.1 * Real.sin p.1,
        -deriv β p.2 * v.2 * Real.sin p.1 - β p.2 * v.1 * Real.cos p.1] := by
  let D0 : (ℝ × ℝ) →L[ℝ] ℝ :=
    (-deriv β p.2 * Real.cos p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (β p.2 * Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
  let D1 : (ℝ × ℝ) →L[ℝ] ℝ :=
    (-deriv β p.2 * Real.sin p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (-β p.2 * Real.cos p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hb := (hβ.differentiable (by simp) p.2).hasDerivAt.hasFDerivAt.comp p
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hc := (Real.hasDerivAt_cos p.1).hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hs := (Real.hasDerivAt_sin p.1).hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hd0 : HasFDerivAt (fun x : ℝ × ℝ => -β x.2 * Real.cos x.1) D0 p := by
    convert! hb.neg.mul hc using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro w
    simp [D0,smul_eq_mul,Function.comp_apply]
    <;> ring
  have hd1 : HasFDerivAt (fun x : ℝ × ℝ => -β x.2 * Real.sin x.1) D1 p := by
    convert! hb.neg.mul hs using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro w
    simp [D1,smul_eq_mul,Function.comp_apply]
    <;> ring
  have hd : HasFDerivAt (completedSaddleAnnulusPolarRankRepresentative β)
      (ContinuousLinearMap.pi ![D0,D1]) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hd0
    · exact hd1
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [D0,D1,smul_eq_mul] <;> ring

private theorem completedSaddleAnnulusPolarRankRepresentative_injective
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (p : ℝ × ℝ)
    (hRadius : β p.2 ≠ 0) (hDerivative : deriv β p.2 ≠ 0) :
    Function.Injective (fderiv ℝ (completedSaddleAnnulusPolarRankRepresentative β) p) := by
  intro v w he
  have hz : fderiv ℝ (completedSaddleAnnulusPolarRankRepresentative β) p (v-w) = 0 := by
    simp [map_sub,he]
  rw [completedSaddleAnnulusPolarRankRepresentative_fderiv hβ] at hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] at h0 h1
  have hTrig := Real.sin_sq_add_cos_sq p.1
  have hu : deriv β p.2 * (v-w).2 = 0 := by
    linear_combination -(Real.cos p.1)*h0 -(Real.sin p.1)*h1 -
      (deriv β p.2 * (v-w).2)*hTrig
  have hθ : β p.2 * (v-w).1 = 0 := by
    linear_combination (Real.sin p.1)*h0 -(Real.cos p.1)*h1 -
      (β p.2 * (v-w).1)*hTrig
  apply sub_eq_zero.mp
  exact Prod.ext ((mul_eq_zero.mp hθ).resolve_left hRadius)
    ((mul_eq_zero.mp hu).resolve_left hDerivative)

/-- The actual negative-polar preferred-chart representative. -/
def completedSaddleAnnulusCylinderPolarCoordinate (β : ℝ → ℝ) (θ : ℝ)
    (x : Coord) : Coord :=
  completedSaddleAnnulusCylinderPlanePoint (β (x 1))
    (periodProjection (2 * Real.pi) (θ+x 0))

private def completedSaddleAnnulusPolarRankShift (θ : ℝ) (x : Coord) : ℝ × ℝ :=
  (θ,0) + revolutionProductCoordinates.symm x

private theorem completedSaddleAnnulusCylinderPolarCoordinate_raw (β : ℝ → ℝ) (θ : ℝ) :
    completedSaddleAnnulusCylinderPolarCoordinate β θ =
      completedSaddleAnnulusPolarRankRepresentative β ∘ completedSaddleAnnulusPolarRankShift θ := by
  funext x
  rw [completedSaddleAnnulusCylinderPolarCoordinate,
    completedSaddleAnnulusCylinderPlanePoint_representative]
  ext i
  fin_cases i <;> simp [completedSaddleAnnulusPolarPoint,
    quadraticRadialFillingCircle_coord,saddlePolarChart,
    completedSaddleAnnulusPolarRankRepresentative,completedSaddleAnnulusPolarRankShift,
    revolutionProductCoordinates]

/-- Actual global smoothness of the real negative-polar chart. -/
theorem completedSaddleAnnulusCylinderPolarCoordinate_contDiff
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (θ : ℝ) :
    ContDiff ℝ ∞ (completedSaddleAnnulusCylinderPolarCoordinate β θ) := by
  rw [completedSaddleAnnulusCylinderPolarCoordinate_raw]
  exact (completedSaddleAnnulusPolarRankRepresentative_contDiff hβ).comp
    (contDiff_const.add revolutionProductCoordinates.symm.contDiff)

/-- Actual real-chart differential injection from the actual nonzero radial
and angular coefficients. No chart-rank premise is supplied. -/
theorem completedSaddleAnnulusCylinderPolarCoordinate_fderiv_injective
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (θ : ℝ) (x : Coord)
    (hRadius : β (x 1) ≠ 0) (hDerivative : deriv β (x 1) ≠ 0) :
    Function.Injective (fderiv ℝ (completedSaddleAnnulusCylinderPolarCoordinate β θ) x) := by
  have hShift : HasFDerivAt (completedSaddleAnnulusPolarRankShift θ)
      revolutionProductCoordinates.symm.toContinuousLinearMap x :=
    revolutionProductCoordinates.symm.hasFDerivAt.const_add (θ,0)
  have hRank : Function.Injective (fderiv ℝ
      (completedSaddleAnnulusPolarRankRepresentative β)
      (completedSaddleAnnulusPolarRankShift θ x)) := by
    apply completedSaddleAnnulusPolarRankRepresentative_injective hβ
    · simpa [completedSaddleAnnulusPolarRankShift,revolutionProductCoordinates] using hRadius
    · simpa [completedSaddleAnnulusPolarRankShift,revolutionProductCoordinates] using hDerivative
  rw [completedSaddleAnnulusCylinderPolarCoordinate_raw,
    fderiv_comp x ((completedSaddleAnnulusPolarRankRepresentative_contDiff hβ).differentiable
      (by simp) _) hShift.differentiableAt,hShift.fderiv]
  exact hRank.comp revolutionProductCoordinates.symm.injective
/-- Actual quotient-cylinder polar rank from actual radial and angular
columns, transported through the retained circle projection. -/
theorem completedSaddleAnnulusCylinderPolarMap_mfderiv_injective
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (p : AddCircle (2 * Real.pi) × ℝ)
    (hRadius : β p.2 ≠ 0) (hDerivative : deriv β p.2 ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Coord)
      (completedSaddleAnnulusCylinderPolarMap β) p) := by
  have hRawEq : completedSaddleAnnulusCylinderPolarMap β ∘ revolutionCylinderProjection =
      completedSaddleAnnulusPolarRankRepresentative β := by
    funext s
    ext i
    fin_cases i <;> simp [completedSaddleAnnulusCylinderPolarMap,
      revolutionCylinderProjection,completedSaddleAnnulusCylinderPlanePoint,
      revolutionCircleRadial_representative,revolutionRadial,
      completedSaddleAnnulusPolarRankRepresentative]
  have hRawRank (s : ℝ × ℝ) (hr : β s.2 ≠ 0) (hd : deriv β s.2 ≠ 0) :
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Coord)
        (completedSaddleAnnulusCylinderPolarMap β ∘ revolutionCylinderProjection) s) := by
    rw [hRawEq]
    change Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord)
      (completedSaddleAnnulusPolarRankRepresentative β) s)
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod,mfderiv_eq_fderiv]
    exact completedSaddleAnnulusPolarRankRepresentative_injective hβ s hr hd
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective p.1
  let s : ℝ × ℝ := (θ,p.2)
  have hs : revolutionCylinderProjection s = p := Prod.ext hθ rfl
  have hComp := mfderiv_comp s
    ((completedSaddleAnnulusCylinderPolarMap_contMDiff hβ
      (revolutionCylinderProjection s)).mdifferentiableAt (by simp))
    ((revolutionCylinderProjection_contMDiff s).mdifferentiableAt (by simp))
  intro v w he
  obtain ⟨v',hv⟩ := revolutionCylinderProjection_mfderiv_surjective s v
  obtain ⟨w',hw⟩ := revolutionCylinderProjection_mfderiv_surjective s w
  have hLift : mfderiv nativeProductModel 𝓘(ℝ, Coord)
      (completedSaddleAnnulusCylinderPolarMap β ∘ revolutionCylinderProjection) s v' =
      mfderiv nativeProductModel 𝓘(ℝ, Coord)
        (completedSaddleAnnulusCylinderPolarMap β ∘ revolutionCylinderProjection) s w' := by
    rw [hComp]
    change mfderiv nativeProductModel 𝓘(ℝ, Coord)
        (completedSaddleAnnulusCylinderPolarMap β) (revolutionCylinderProjection s)
        (mfderiv nativeProductModel nativeProductModel revolutionCylinderProjection s v') =
      mfderiv nativeProductModel 𝓘(ℝ, Coord)
        (completedSaddleAnnulusCylinderPolarMap β) (revolutionCylinderProjection s)
        (mfderiv nativeProductModel nativeProductModel revolutionCylinderProjection s w')
    rw [hv,hw,hs]
    exact he
  have hEqual := hRawRank s hRadius hDerivative hLift
  rw [← hv,← hw,hEqual]

private def completedSaddleAnnulusNeckRankChange (B : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : AddCircle (2 * Real.pi) × ℝ :=
  (p.1,2*B*(p.2-Real.pi/2))

private theorem completedSaddleAnnulusNeckRankChange_contMDiff (B : ℝ) :
    ContMDiff nativeProductModel nativeProductModel ∞ (completedSaddleAnnulusNeckRankChange B) :=
  contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_snd.sub contMDiff_const))

private theorem completedSaddleAnnulusNeckRankChange_mfderiv (B : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) (v : ℝ × ℝ) :
    mfderiv nativeProductModel nativeProductModel (completedSaddleAnnulusNeckRankChange B) p v =
      (v.1,2*B*v.2) := by
  have hT : ContDiff ℝ ∞ (fun u : ℝ => 2*B*(u-Real.pi/2)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  have hd : HasDerivAt (fun u : ℝ => 2*B*(u-Real.pi/2)) (2*B) p.2 := by
    simpa using ((hasDerivAt_id p.2).sub_const (Real.pi/2)).const_mul (2*B)
  change mfderiv nativeProductModel nativeProductModel
    (Prod.map id (fun u : ℝ => 2*B*(u-Real.pi/2))) p v = _
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((hT.contMDiff p.2).mdifferentiableAt (by simp)),mfderiv_id,
    mfderiv_eq_fderiv,hd.hasFDerivAt.fderiv]
  with_unfolding_all change (v.1,v.2*(2*B)) = (v.1,2*B*v.2)
  congr 1
  ring

private theorem completedSaddleAnnulusNeckRankChange_injective
    {B : ℝ} (hB : 0 < B) (p : AddCircle (2 * Real.pi) × ℝ) :
    Function.Injective (mfderiv nativeProductModel nativeProductModel
      (completedSaddleAnnulusNeckRankChange B) p) := by
  intro v w he
  rw [completedSaddleAnnulusNeckRankChange_mfderiv,
    completedSaddleAnnulusNeckRankChange_mfderiv] at he
  apply Prod.ext
  · have hh := congrArg Prod.fst he
    exact hh
  · have hh := congrArg Prod.snd he
    exact mul_left_cancel₀ (mul_pos (by norm_num : (0:ℝ)<2) hB).ne' hh

private theorem completedSaddleAnnulusNeckRank_model
    {A B : ℝ} (hB : 0 < B) :
    revolutionEndCircleFull (fun z => A+z^2/(4*B)) ∘ completedSaddleAnnulusNeckRankChange B =
      (fun p : AddCircle (2 * Real.pi) × ℝ =>
        (A+B*(p.2-Real.pi/2)^2) • revolutionCircleRadial p.1 +
          (2*B*(p.2-Real.pi/2)) • revolutionAxis) := by
  funext p
  simp only [Function.comp_apply]
  unfold revolutionEndCircleFull completedSaddleAnnulusNeckRankChange
  congr 1
  field_simp [hB.ne']
  <;> ring

private theorem completedSaddleAnnulus_rank_of_graph_composition
    {F : Coord → Ambient} {V : Set Coord} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V)
    {φ : AddCircle (2 * Real.pi) × ℝ → Coord}
    (hφ : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ φ)
    (p : AddCircle (2 * Real.pi) × ℝ) (hp : φ p ∈ V)
    (hRankF : Function.Injective (fderiv ℝ F (φ p)))
    (hRankφ : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Coord) φ p)) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F ∘ φ) p) := by
  have hDF := ((hF _ hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hMDF : MDifferentiableAt 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F (φ p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hDF
  rw [mfderiv_comp p hMDF ((hφ p).mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  exact hRankF.comp hRankφ

private theorem completedSaddleAnnulus_rank_polar_target
    {A RN : ℝ} (hA : 0 < A) (e : OpenPartialHomeomorph Coord Coord)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    {β : ℝ → ℝ} (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (Real.pi/2) Real.pi) :
    0 < β u ∧ completedSaddleAnnulusCylinderPolarMap β (q,u) ∈ e.target := by
  have hm : Real.pi/2 ∈ Icc (Real.pi/2) Real.pi := ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hn : Real.pi ∈ Icc (Real.pi/2) Real.pi := ⟨by linarith [Real.pi_pos],le_rfl⟩
  have hucc : u ∈ Icc (Real.pi/2) Real.pi := ⟨hu.1.le,hu.2.le⟩
  have hlow : A < β u := by rw [← hβA]; exact hMono hm hucc hu.1
  have hhigh : β u < RN := by rw [← hβRN]; exact hMono hucc hn hu.2
  have hpos : 0 < β u := hA.trans hlow
  refine ⟨hpos,?_⟩
  rw [hTarget]
  change A < planarRadius (completedSaddleAnnulusCylinderPlanePoint (β u) q) ∧
    planarRadius (completedSaddleAnnulusCylinderPlanePoint (β u) q) < RN
  rw [completedSaddleAnnulusCylinderPlanePoint_radius hpos]
  exact ⟨hlow,hhigh⟩

/-- Actual full interior native differential injectivity for the constructed
cylinder. All ranks follow from actual scalar data and actual derivatives. -/
theorem completedSaddleAnnulusCylinderMap_mfderiv_injective
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
    (hβDerivative : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2)) :
    ∀ p ∈ (univ ×ˢ Ioo (0 : ℝ) Real.pi),
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) p) := by
  have hGraphs := completedSaddleAnnulusGraphs_contDiffOn e dInfinity hG hi
  have hPolar := completedSaddleAnnulusCylinderPolarMap_contMDiff hβ
  have hReflect : ContDiff ℝ ∞ (fun u => β (Real.pi-u)) :=
    hβ.comp (contDiff_const.sub contDiff_id)
  have hPolarReflect := completedSaddleAnnulusCylinderPolarMap_contMDiff hReflect
  intro p hp
  by_cases hm : p.2 = Real.pi/2
  · let Q : ℝ → ℝ := fun z => A+z^2/(4*B)
    have hQ : ContDiff ℝ ∞ Q := contDiff_const.add ((contDiff_id.pow 2).div_const (4*B))
    have hNeckUniform := completedSaddleAnnulusCylinderMap_neck_germ (d0 := d0) e hA hARN hB hL
      hSource hTarget heG hInfinity hβNeck
    have ht : Tendsto (fun s : AddCircle (2 * Real.pi) × ℝ => s.2) (𝓝 p) (𝓝 (Real.pi/2)) := by
      simpa only [hm] using (continuous_snd : Continuous
        (fun s : AddCircle (2 * Real.pi) × ℝ => s.2)).tendsto p
    have hNeck : completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β =ᶠ[𝓝 p]
        revolutionEndCircleFull Q ∘ completedSaddleAnnulusNeckRankChange B := by
      filter_upwards [ht.eventually hNeckUniform] with s hs
      rw [completedSaddleAnnulusNeckRank_model (A := A) hB]
      exact hs s.1
    have hQPoint : Q (completedSaddleAnnulusNeckRankChange B p).2 ≠ 0 := by
      simpa [Q,completedSaddleAnnulusNeckRankChange,hm] using hA.ne'
    have hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient)
        (revolutionEndCircleFull Q) (completedSaddleAnnulusNeckRankChange B p) :=
      ((revolutionEndCircleFull_contMDiff hQ _).mdifferentiableAt (by simp))
    have hChange : MDifferentiableAt nativeProductModel nativeProductModel
        (completedSaddleAnnulusNeckRankChange B) p :=
      ((completedSaddleAnnulusNeckRankChange_contMDiff B p).mdifferentiableAt (by simp))
    rw [hNeck.mfderiv_eq,mfderiv_comp p hF hChange]
    exact (revolutionEndCircleFull_mfderiv_injective hQ _ hQPoint).comp
      (completedSaddleAnnulusNeckRankChange_injective hB p)
  · rcases lt_or_gt_of_ne hm with hlo | hhi
    · have hu : p.2 ∈ Ioo 0 (Real.pi/2) := ⟨hp.2.1,hlo⟩
      have hRefU : Real.pi-p.2 ∈ Ioo (Real.pi/2) Real.pi := ⟨by linarith,by linarith [hp.2.1]⟩
      have hData := completedSaddleAnnulus_rank_polar_target hA e hTarget hMono hβA hβRN p.1 hRefU
      have hy : completedSaddleAnnulusCylinderPolarMap (fun u => β (Real.pi-u)) p ∈ e.target := hData.2
      have hd : deriv (fun u => β (Real.pi-u)) p.2 = -deriv β (Real.pi-p.2) := by
        have hChain := ((hβ.differentiable (by simp) (Real.pi-p.2)).hasDerivAt).comp p.2
          ((hasDerivAt_id p.2).const_sub Real.pi)
        simpa [Function.comp_def] using hChain.deriv
      have hRefDerivative : deriv (fun u => β (Real.pi-u)) p.2 ≠ 0 := by
        rw [hd]
        exact neg_ne_zero.mpr (hβDerivative _ hRefU).ne'
      have hRankPolar := completedSaddleAnnulusCylinderPolarMap_mfderiv_injective hReflect p
        hData.1.ne' hRefDerivative
      have hRankGraph := (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hy).2
      rw [(completedSaddleAnnulusCylinderMap_lower_germ G e hA hMono hβA hβRN hu).mfderiv_eq]
      exact completedSaddleAnnulus_rank_of_graph_composition e.open_target hGraphs.2 hPolarReflect p
        hy hRankGraph hRankPolar
    · have hu : p.2 ∈ Ioo (Real.pi/2) Real.pi := ⟨hhi,hp.2.2⟩
      have hData := completedSaddleAnnulus_rank_polar_target hA e hTarget hMono hβA hβRN p.1 hu
      have hRankPolar := completedSaddleAnnulusCylinderPolarMap_mfderiv_injective hβ p
        hData.1.ne' (hβDerivative _ hu).ne'
      have hRankGraph := (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hData.2).1
      rw [(completedSaddleAnnulusCylinderMap_upper_germ G e hA hMono hβA hβRN hu).mfderiv_eq]
      exact completedSaddleAnnulus_rank_of_graph_composition e.open_target hGraphs.1 hPolar p
        hData.2 hRankGraph hRankPolar

end
end TightVer401


