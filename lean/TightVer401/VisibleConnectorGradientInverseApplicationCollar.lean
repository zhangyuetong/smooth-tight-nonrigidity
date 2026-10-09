import TightVer401.AnnularDegreeGradient
import Mathlib.Topology.Separation.Hausdorff

/-! Compact collar enlargement for the actual gradient of the SAME supplied
potential. No connector construction or completed-potential package is needed. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Enlarge compact injectivity and strict actual Hessian sign to one smooth
open inverse collar of the actual global gradient of `G`. -/
theorem visibleConnectorGradientInverseApplication_exists_collar
    {G : Coord → ℝ} {U K : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hNeg : ∀ p ∈ K, (planarHessian G p).det < 0)
    (hInj : InjOn (planarGradient G) K) :
    ∃ E : OpenPartialHomeomorph Coord Coord,
      K ⊆ E.source ∧ E.source ⊆ U ∧
      ContDiffOn ℝ ∞ G E.source ∧
      (∀ p ∈ E.source, (planarHessian G p).det < 0) ∧
      (E : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ E E.source ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      planarGradient G '' K ⊆ E.target ∧
      E.target = planarGradient G '' E.source := by
  let V := U ∩ (fun p => (planarHessian G p).det) ⁻¹' Iio (0 : ℝ)
  have hV : IsOpen V :=
    (planarHessian_det_contDiffOn hG hU).continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hKV : K ⊆ V := fun p hp => ⟨hKU hp,hNeg p hp⟩
  have hCont : ∀ p ∈ K, ContinuousAt (planarGradient G) p := by
    intro p hp
    exact (planarGradient_contDiffOn hG hU).contDiffAt
      (hU.mem_nhds (hKU hp)) |>.continuousAt
  have hLocal : ∀ p ∈ K, ∃ W ∈ 𝓝 p, InjOn (planarGradient G) W := by
    intro p hp
    obtain ⟨e,he,_heU,hef,_hei⟩ := planarGradient_exists_smooth_local_inverse_at
      hG hU (hKU hp) (hNeg p hp).ne
    refine ⟨e.source,e.open_source.mem_nhds he,?_⟩
    rw [← hef]
    exact e.injOn
  obtain ⟨W,hW,hKW,hIW⟩ := hInj.exists_isOpen_superset hK hCont hLocal
  let Z := W ∩ V
  have hZ : IsOpen Z := hW.inter hV
  have hKZ : K ⊆ Z := fun p hp => ⟨hKW hp,hKV hp⟩
  have hZU : Z ⊆ U := fun _ hp => hp.2.1
  have hGZ := hG.mono hZU
  have hNZ : ∀ p ∈ Z, (planarHessian G p).det < 0 := fun _ hp => hp.2.2
  have hIZ : InjOn (planarGradient G) Z := hIW.mono inter_subset_left
  have hGradZ := planarGradient_contDiffOn hGZ hZ
  have hJ : ∀ p ∈ Z, annularJacobian (planarGradient G) p ≠ 0 := by
    intro p hp
    rw [annularGradientJacobian_eq_hessian_det hGZ hZ hp]
    exact (hNZ p hp).ne
  have hUnique : ∀ y ∈ planarGradient G '' Z,
      ∃! p, p ∈ Z ∧ planarGradient G p = y := by
    rintro y ⟨p,hp,hpy⟩
    refine ⟨p,⟨hp,hpy⟩,?_⟩
    intro q hq
    exact hIZ hq.1 hp (hq.2.trans hpy.symm)
  obtain ⟨E,hEs,hEt,hEf,hEi⟩ := annular_exists_smooth_image_inverse hZ hGradZ hJ hUnique
  refine ⟨E,?_,?_,?_,?_,hEf,?_,hEi,?_,?_⟩
  · simpa only [hEs] using hKZ
  · simpa only [hEs] using hZU
  · simpa only [hEs] using hGZ
  · simpa only [hEs] using hNZ
  · simpa only [hEf,hEs] using hGradZ
  · rw [hEt]
    exact image_mono hKZ
  · simpa only [hEs] using hEt

/-- An earlier actual gradient inverse is retained on its full target whenever
its source lies in the compact set included in the enlarged collar. -/
theorem visibleConnectorGradientInverseApplication_collar_agrees
    {G : Coord → ℝ} {K : Set Coord}
    {E e0 : OpenPartialHomeomorph Coord Coord}
    (hKE : K ⊆ E.source) (hE : (E : Coord → Coord) = planarGradient G)
    (he0K : e0.source ⊆ K) (he0 : EqOn e0 (planarGradient G) e0.source) :
    e0.target ⊆ E.target ∧ EqOn E e0 e0.source ∧
      EqOn E.symm e0.symm e0.target := by
  have hForward : ∀ y ∈ e0.target, E (e0.symm y) = y := by
    intro y hy
    calc
      E (e0.symm y) = planarGradient G (e0.symm y) := congrFun hE _
      _ = e0 (e0.symm y) := (he0 (e0.map_target hy)).symm
      _ = y := e0.right_inv hy
  refine ⟨?_,?_,?_⟩
  · intro y hy
    rw [← hForward y hy]
    exact E.map_source (hKE (he0K (e0.map_target hy)))
  · intro p hp
    exact (congrFun hE p).trans (he0 hp).symm
  · intro y hy
    calc
      E.symm y = E.symm (E (e0.symm y)) := congrArg E.symm (hForward y hy).symm
      _ = e0.symm y := E.left_inv (hKE (he0K (e0.map_target hy)))

end
end TightVer401
