import TightVer401.SmoothingFlatModel
import TightVer401.SmoothingProfilePatch

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def smoothingFlatPatch (F G : Coord → ℝ) (δ : ℝ) (hδ : 0 < δ) (h : ℝ) : Coord → ℝ :=
  smoothingNormalModel (smoothingPatchedProfile δ hδ h) G (smoothingFlatRemainder (F-G))

def smoothingFlatOriginal (F G : Coord → ℝ) (p : Coord) : ℝ :=
  if p 1 ≤ 0 then G p else F p

theorem smoothingFlatPatch_contDiff {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (δ : ℝ) (hδ : 0 < δ) (h : ℝ) :
    ContDiff ℝ ∞ (smoothingFlatPatch F G δ hδ h) :=
  smoothingNormalModel_contDiff (smoothingPatchedProfile_contDiff δ hδ h) hG
    (smoothingFlatRemainder_contDiff (hF.sub hG))

theorem smoothingFlatOriginal_eq {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) (p : Coord) :
    smoothingFlatOriginal F G p = G p+(max (p 1) 0)^2*smoothingFlatRemainder (F-G) p := by
  have hd := smoothing_flat_taylor_factor (hF.sub hG) hzero hfirst p
  change F p-G p=(p 1)^2*smoothingFlatRemainder (F-G) p at hd
  unfold smoothingFlatOriginal
  split_ifs with hp
  · simp [max_eq_right hp]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hp))]
    linarith

theorem smoothingFlatPatch_old_germ (F G : Coord → ℝ) (δ : ℝ) (hδ : 0 < δ)
    {h : ℝ} (hh : 0 < h) {p : Coord} (hp : p 1 < -δ) :
    smoothingFlatPatch F G δ hδ h =ᶠ[𝓝 p] G := by
  have hg := (smoothingPatchedProfile_zero_germ δ hδ hh hp).comp_tendsto
    ((continuous_apply 1).tendsto p)
  filter_upwards [hg] with q hq
  change smoothingPatchedProfile δ hδ h (q 1)=0 at hq
  simp [smoothingFlatPatch,smoothingNormalModel,hq]

theorem smoothingFlatPatch_new_germ {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) (δ : ℝ) (hδ : 0 < δ)
    {h : ℝ} (hh : 0 < h) (hδh : δ ≤ h) {p : Coord} (hp : 2*h < p 1) :
    smoothingFlatPatch F G δ hδ h =ᶠ[𝓝 p] F := by
  have hg := (smoothingPatchedProfile_square_germ δ hδ hh hδh hp).comp_tendsto
    ((continuous_apply 1).tendsto p)
  filter_upwards [hg] with q hq
  change smoothingPatchedProfile δ hδ h (q 1)=(q 1)^2 at hq
  have hd := smoothing_flat_taylor_factor (hF.sub hG) hzero hfirst q
  change F q-G q=(q 1)^2*smoothingFlatRemainder (F-G) q at hd
  change G q+smoothingPatchedProfile δ hδ h (q 1)*smoothingFlatRemainder (F-G) q=F q
  rw [hq]
  linarith

theorem smoothingFlatPatch_value_bound {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) (δ : ℝ) (hδ : 0 < δ)
    (h : ℝ) {p : Coord} {M : ℝ} (hM : |smoothingFlatRemainder (F-G) p| ≤ M) :
    |smoothingFlatPatch F G δ hδ h p-smoothingFlatOriginal F G p| ≤ 7*δ^2*M := by
  rw [smoothingFlatOriginal_eq hF hG hzero hfirst]
  have he : smoothingFlatPatch F G δ hδ h p-
      (G p+(max (p 1) 0)^2*smoothingFlatRemainder (F-G) p) =
      (smoothingPatchedProfile δ hδ h (p 1)-(max (p 1) 0)^2)*smoothingFlatRemainder (F-G) p := by
    unfold smoothingFlatPatch smoothingNormalModel
    ring
  rw [he,abs_mul]
  exact mul_le_mul (smoothingPatchedProfile_uniform_value_error δ hδ h (p 1)) hM
    (abs_nonneg _) (by positivity)

end
end TightVer401
