import TightVer401.FermiSupportLocalSeam

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiSupport_contDiffOn {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0) :
    ContDiffOn ℝ ∞ (fermiSupportL κ H) U ∧
    ContDiffOn ℝ ∞ (fermiSupportM κ H) U ∧
    ContDiffOn ℝ ∞ (fermiSupportN H) U := by
  have hh := (fermiNormalScale_contDiff hκ).contDiffOn (s := U)
  have hh0 := partial_contDiffOn hh hU 0
  have hh1 := partial_contDiffOn hh hU 1
  have hH0 := partial_contDiffOn hH hU 0
  have hH1 := partial_contDiffOn hH hU 1
  have hH00 := partial_contDiffOn hH0 hU 0
  have hH01 := partial_contDiffOn hH1 hU 0
  have hH11 := partial_contDiffOn hH1 hU 1
  exact ⟨((hH00.sub ((hh0.div hh hscale).mul hH0)).add ((hh.mul hh1).mul hH1)).add
      (hH.mul (hh.pow 2)),
    hH01.sub ((hh1.div hh hscale).mul hH0), hH11.add hH⟩

theorem fermiSupport_seam_contDiff {F : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hseam : ∀ r : ℝ, (![r,0] : Coord) ∈ U) :
    ContDiff ℝ ∞ (fun r => F ![r,0]) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (![r,0] : Coord)) := by
    have hc : ContDiff ℝ ∞ (fun r : ℝ => r • (Pi.single 0 1 : Coord)) :=
      contDiff_id.smul contDiff_const
    convert! hc using 1
    funext r
    ext i
    fin_cases i <;> simp
  rw [contDiff_iff_contDiffAt]
  intro r
  exact ((hF _ (hseam r)).contDiffAt (hU.mem_nhds (hseam r))).comp r hs.contDiffAt

theorem fermiSupport_seam_hasDerivAt {F : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {r : ℝ}
    (hr : (![r,0] : Coord) ∈ U) :
    HasDerivAt (fun s => F ![s,0]) (coordPartial 0 F ![r,0]) r := by
  have hd := ((hF _ hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp)
  have hs : HasDerivAt (fun s : ℝ => (![s,0] : Coord)) (Pi.single 0 1) r := by
    have hc := (hasDerivAt_id r).smul_const (Pi.single 0 1 : Coord)
    convert! hc using 1
    · funext s
      ext i
      fin_cases i <;> simp
    · simp
  have hc := hd.hasFDerivAt.comp_hasDerivAt r hs
  have he : (F ∘ (fun s : ℝ => (![s,0] : Coord))) = (fun s => F ![s,0]) := rfl
  rw [he] at hc
  exact hc

end
end TightVer401
