import TightVer401.FermiSupportAsymptoticDomain
import TightVer401.ExitPositiveGraphDomain

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiSupport_graph_saddle_radius {κ v : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hv : ContDiff ℝ ∞ v)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) :
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ r ∈ Icc (0 : ℝ) P,
      exitGraphCurve v δ r ∈ U ∧
      (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H (exitGraphCurve v δ r)).det < 0 := by
  obtain ⟨W,hW,hWU,hWs,hf,hdet,hquad⟩ :=
    exists_fermiSupport_asymptotic_domain hκ hU hH hscale hseam hzero hpos
  obtain ⟨e,he,hbound⟩ := exitGraphCurve_uniform_domain hv hW (fun r _ => hWs r)
  exact ⟨e,he,fun δ hδ r hr => ⟨hWU (hbound r hr δ hδ.le),
    hdet _ (hbound r hr δ hδ.le)⟩⟩

end
end TightVer401
