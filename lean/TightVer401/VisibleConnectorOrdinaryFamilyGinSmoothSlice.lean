import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.SeamCompactCollar
import Mathlib.Algebra.Order.ToIntervalMod

/-! Smooth fixed-rho slices of the SAME eta-fixed displaced Gin family.
The uniform domain is derived from the actual open visibility domain, its
axis membership and physical periodicity; displaced visibility is not granted. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Construct one uniform displacement margin in the actual Gin visibility
domain, valid over ALL physical parameters and both signs of rho. -/
theorem visibleConnectorOrdinaryFamily_Gin_uniform_visibility_strip
    {L R eta : ℝ} (hL : 0 < L)
    {Gin : Coord → ℝ} {U : Set Coord} {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ U)
    (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s) :
    ∃ delta > 0, ∀ rho s, |rho| ≤ delta →
      (rho, s) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0 := by
  obtain ⟨hpc, hDU, hgc, hV, hVsub, haxis, hW,
    hpcL, hgcL, hWL, hperiodV, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  let swap : Coord → ℝ × ℝ := fun q => (q 1, q 0)
  have hswap : Continuous swap := by dsimp [swap]; fun_prop
  have hopen : IsOpen (swap ⁻¹' visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) :=
    hV.preimage hswap
  have haxis' : ∀ s ∈ Icc (0 : ℝ) L,
      (![s, 0] : Coord) ∈ swap ⁻¹' visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0 := by
    intro s _
    exact haxis s
  obtain ⟨delta, hdelta, hstrip⟩ := seam_compact_axis_open_collar isCompact_Icc hopen haxis'
  refine ⟨delta, hdelta, ?_⟩
  intro rho s hrho
  have hs : toIcoMod hL 0 s ∈ Icc (0 : ℝ) L :=
    Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hm := hstrip (toIcoMod hL 0 s) hs rho hrho
  change (rho, toIcoMod hL 0 s) ∈
    visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0 at hm
  have hepc : visibleConnectorGinDisplacedPosition p w0 (rho, s) =
      visibleConnectorGinDisplacedPosition p w0 (rho, toIcoMod hL 0 s) := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
    exact (hpcL rho).zsmul (toIcoDiv hL 0 s) _
  have hegc : visibleConnectorGinDisplacedGradient Gin p w0 (rho, s) =
      visibleConnectorGinDisplacedGradient Gin p w0 (rho, toIcoMod hL 0 s) := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
    exact (hgcL rho).zsmul (toIcoDiv hL 0 s) _
  change visibleConnectorGinDisplacedPosition p w0 (rho, s) ∈ U ∧
    R < ‖Complex.I * angularDescentComplex (visibleConnectorGinDisplacedGradient Gin p w0 (rho, s))‖
  rw [hepc, hegc]
  exact hm

/-- Every rho in the constructed margin gives globally smooth actual pc/gc/wc
and pc stays in SAME Gin U. The SAME eta and the actual periodic curves survive. -/
theorem visibleConnectorOrdinaryFamily_Gin_uniform_smooth_slices
    {L R eta : ℝ} (hL : 0 < L)
    {Gin : Coord → ℝ} {U : Set Coord} {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ U)
    (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s) :
    ∃ delta > 0, ∀ rho, |rho| ≤ delta →
      ContDiff ℝ ∞ (fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)) ∧
      ContDiff ℝ ∞ (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (rho, s)) ∧
      ContDiff ℝ ∞ (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)) ∧
      (∀ s, visibleConnectorGinDisplacedPosition p w0 (rho, s) ∈ U) ∧
      (∀ s, R < ‖Complex.I * angularDescentComplex
        (visibleConnectorGinDisplacedGradient Gin p w0 (rho, s))‖) ∧
      Periodic (fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)) L ∧
      Periodic (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (rho, s)) L ∧
      Periodic (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)) L := by
  obtain ⟨hpc, hDU, hgc, hV, hVsub, haxis, hW,
    hpcL, hgcL, hWL, hperiodV, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  obtain ⟨delta, hdelta, hstrip⟩ := visibleConnectorOrdinaryFamily_Gin_uniform_visibility_strip
    hL hR hU hGin hp hw0 hpL hw0L hpU hgamma hmargin hw0same
  refine ⟨delta, hdelta, ?_⟩
  intro rho hrho
  have hslice : ContDiff ℝ ∞ (fun s : ℝ => (rho, s)) := contDiff_const.prodMk contDiff_id
  have hsliceV : MapsTo (fun s : ℝ => (rho, s)) univ
      (visibleConnectorGinDisplacedVisibilityDomain Gin U R p w0) :=
    fun s _ => hstrip rho s hrho
  have hsliceDU : MapsTo (fun s : ℝ => (rho, s)) univ
      (visibleConnectorGinDisplacedDomain U p w0) := fun s hs => hVsub (hsliceV hs)
  have hpc' := hpc.comp hslice
  have hgc' : ContDiff ℝ ∞ (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (rho, s)) :=
    contDiffOn_univ.mp (hgc.comp hslice.contDiffOn hsliceDU)
  have hW' : ContDiff ℝ ∞ (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)) :=
    contDiffOn_univ.mp (hW.comp hslice.contDiffOn hsliceV)
  refine ⟨hpc', hgc', hW', ?_, ?_, hpcL rho, hgcL rho, hWL rho⟩
  · intro s
    exact (hstrip rho s hrho).1
  · intro s
    exact (hstrip rho s hrho).2

end
end TightVer401
