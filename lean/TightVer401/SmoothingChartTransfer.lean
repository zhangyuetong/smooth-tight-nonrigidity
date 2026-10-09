import TightVer401.SmoothingLocalChartExistence

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology

def smoothingChartPotential (e : OpenPartialHomeomorph Coord Coord) (H : Coord → ℝ)
    (x : Coord) : ℝ := H (e.symm x)

theorem smoothingChartPotential_contDiffOn (e : OpenPartialHomeomorph Coord Coord)
    {H : Coord → ℝ} (hH : ContDiff ℝ ∞ H)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (smoothingChartPotential e H) e.target := by
  intro x hx
  exact hH.contDiffAt.comp_contDiffWithinAt x (hInv x hx)

theorem smoothingChartPotential_germ (e : OpenPartialHomeomorph Coord Coord)
    (H : Coord → ℝ) {p : Coord} (hp : p ∈ e.source) :
    (fun q => smoothingChartPotential e H (e q)) =ᶠ[𝓝 p] H := by
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  change H (e.symm (e q))=H q
  rw [e.left_inv hq]

/-- Corrected saddle Hessians transfer to the actual Euclidean Hessian through
an actual smooth inverse chart, even though that inverse is only locally smooth. -/
theorem smoothingChartPotential_saddle (e : OpenPartialHomeomorph Coord Coord)
    {H : Coord → ℝ} (hE : ContDiff ℝ ∞ (e : Coord → Coord))
    (hH : ContDiff ℝ ∞ H) (hInv : ContDiffOn ℝ ∞ e.symm e.target)
    {p : Coord} (hp : p ∈ e.source)
    (hJ : (seamCoordinateJacobian e p).det ≠ 0)
    (hneg : (seamCorrectedHessian e H p).det < 0) :
    (planarHessian (smoothingChartPotential e H) (e p)).det < 0 := by
  have ht : e p ∈ e.target := e.map_source hp
  obtain ⟨F,hF,hg,_⟩ := exists_smooth_collar_extension e.open_target
    (isClosed_singleton : IsClosed ({e p} : Set Coord))
    (singleton_subset_iff.mpr ht)
    (smoothingChartPotential_contDiffOn e hH hInv) (0 : ℝ)
  have hGerm : F =ᶠ[𝓝 (e p)] smoothingChartPotential e H := by
    simpa only [nhdsSet_singleton] using hg
  have hComp : (fun q => F (e q)) =ᶠ[𝓝 p] H := by
    filter_upwards [(e.continuousAt hp).eventually hGerm,e.open_source.mem_nhds hp] with q hq hs
    rw [hq]
    change H (e.symm (e q))=H q
    rw [e.left_inv hs]
  have hCorr := smoothing_correctedHessian_germ (e : Coord → Coord) hComp
  rw [← hCorr] at hneg
  have hnF := (seamCorrectedHessian_comp_saddle_iff hF hE hJ).mp hneg
  rw [smoothing_planarHessian_germ hGerm] at hnF
  exact hnF

theorem smoothingChartPotential_side_germ (e : OpenPartialHomeomorph Coord Coord)
    {H F : Coord → ℝ} {p : Coord} (hp : p ∈ e.source)
    (h : H =ᶠ[𝓝 p] F) :
    smoothingChartPotential e H =ᶠ[𝓝 (e p)] smoothingChartPotential e F := by
  have hc := e.continuousAt_symm (e.map_source hp)
  have he : H =ᶠ[𝓝 (e.symm (e p))] F := by simpa only [e.left_inv hp] using h
  exact hc.eventually he

end
end TightVer401
