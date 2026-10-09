import TightVer401.SmoothingSeamPeriodicity
import OAI.Analysis.CircleDomains.Topology.CollarExtension

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology

def smoothingNormalCutoff (r : ℝ) (hr : 0 < r) (p : Coord) : ℝ :=
  momentControlBump 0 (r/2) (half_pos hr) (p 1)

def smoothingNormalExtension (r : ℝ) (hr : 0 < r) (F : Coord → ℝ) (p : Coord) : ℝ :=
  smoothingNormalCutoff r hr p*F p

theorem smoothingNormalCutoff_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (smoothingNormalCutoff r hr) :=
  (momentControlBump 0 (r/2) (half_pos hr)).contDiff.comp (contDiff_apply ℝ ℝ 1)

theorem smoothingNormalCutoff_zero (r : ℝ) (hr : 0 < r) {p : Coord} (hp : r/2 ≤ |p 1|) :
    smoothingNormalCutoff r hr p=0 := by
  apply (momentControlBump 0 (r/2) (half_pos hr)).zero_of_le_dist
  simpa only [momentControlBump,Real.dist_eq,sub_zero] using hp

theorem smoothingNormalCutoff_one (r : ℝ) (hr : 0 < r) {p : Coord} (hp : |p 1| ≤ r/4) :
    smoothingNormalCutoff r hr p=1 := by
  apply (momentControlBump 0 (r/2) (half_pos hr)).one_of_mem_closedBall
  change dist (p 1) 0 ≤ (r/2)/2
  rw [Real.dist_eq,sub_zero]
  linarith

/-- OpenAI's actual collar-cutoff extension, with an explicit normal cutoff
chosen to preserve any period along the seam. -/
theorem smoothingNormalExtension_contDiff (r : ℝ) (hr : 0 < r) {F : Coord → ℝ}
    (hF : ContDiffOn ℝ ∞ F {p : Coord | |p 1| < r}) :
    ContDiff ℝ ∞ (smoothingNormalExtension r hr F) := by
  have hU : IsOpen {p : Coord | |p 1| < r} := isOpen_lt (continuous_apply 1 |>.abs) continuous_const
  have hO : IsOpen {p : Coord | r/2 < |p 1|} := isOpen_lt continuous_const (continuous_apply 1 |>.abs)
  have hsub : {p : Coord | |p 1| < r}ᶜ ⊆ {p : Coord | r/2 < |p 1|} := by
    intro p hp
    change ¬ |p 1| < r at hp
    change r/2 < |p 1|
    linarith [le_of_not_gt hp]
  have hz : ∀ᶠ p in 𝓝ˢ ({p : Coord | |p 1| < r}ᶜ), smoothingNormalCutoff r hr p=0 := by
    filter_upwards [hO.mem_nhdsSet.mpr hsub] with p hp
    exact smoothingNormalCutoff_zero r hr (le_of_lt hp)
  have hc := contDiff_collar_cutoff hU hF (smoothingNormalCutoff_contDiff r hr) hz (0 : ℝ)
  change ContDiff ℝ ∞ (fun p : Coord => smoothingNormalCutoff r hr p*F p)
  simpa only [zero_add,sub_zero] using hc

theorem smoothingNormalExtension_germ (r : ℝ) (hr : 0 < r) (F : Coord → ℝ)
    {p : Coord} (hp : |p 1| < r/4) : smoothingNormalExtension r hr F =ᶠ[𝓝 p] F := by
  have hO : IsOpen {q : Coord | |q 1| < r/4} := isOpen_lt (continuous_apply 1 |>.abs) continuous_const
  filter_upwards [hO.mem_nhds hp] with q hq
  change |q 1| < r/4 at hq
  simp [smoothingNormalExtension,smoothingNormalCutoff_one r hr hq.le]

theorem smoothingNormalExtension_periodic (r : ℝ) (hr : 0 < r) {F : Coord → ℝ}
    (L : ℝ) (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (p : Coord) :
    smoothingNormalExtension r hr F (smoothingSeamShift L p)=smoothingNormalExtension r hr F p := by
  unfold smoothingNormalExtension
  rw [hperiod]
  rfl

end
end TightVer401
