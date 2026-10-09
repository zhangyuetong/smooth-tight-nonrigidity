import TightVer401.CurveL1StabilityLocal
import TightVer401.CurveL1StabilitySeparation

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_speedCurve_L1_representative_threshold {L : ℝ} (hL : 0 < L)
    (P : ℝ → E) (hP : Continuous P) (hne : ∀ x, P x ≠ 0)
    (b : ℝ → ℝ) (hb : Continuous b) (hbperiod : Function.Periodic (speedCurve b P) L)
    (hbinj : Set.InjOn (speedCurve b P) (Ico 0 L)) :
    ∃ η > 0, ∀ a : ℝ → ℝ, Continuous a → (∀ x, 0 < a x) →
      Function.Periodic (speedCurve a P) L →
      (∫ x in 0..L, |a x - b x|) < η → Set.InjOn (speedCurve a P) (Ico 0 L) := by
  obtain ⟨δ, hδ, _, hdir⟩ := exists_speedCurve_tangent_radius hL P hP hne
  obtain ⟨M, hM, hbound⟩ := exists_speedCurve_uniform_bound P hP L
  have hcb : Continuous (speedCurve b P) := rawPrimitive_continuous (hb.smul hP)
  have hperiod0 : speedCurve b P L = speedCurve b P 0 := by simpa only [zero_add] using hbperiod 0
  obtain ⟨ρ, hρ, hsep⟩ := exists_speedCurve_distant_separation hδ (speedCurve b P) hcb hbinj hperiod0
  refine ⟨ρ / (4 * M), div_pos hρ (by positivity), ?_⟩
  intro a ha hapos haperiod hsmall
  have hlocal (x) (hx : x ∈ Icc 0 L) :
      Set.InjOn (speedCurve a P) (Ioo (x - δ) (x + δ)) := by
    apply speedCurve_local_injective ha hP hapos
    intro t ht
    apply hdir x hx t
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hordered (x y) (hx : x ∈ Ico 0 L) (hy : y ∈ Ico 0 L) (hxy : x < y) :
      speedCurve a P x ≠ speedCurve a P y := by
    intro he
    have hxC : x ∈ Icc 0 L := ⟨hx.1, hx.2.le⟩
    have hyC : y ∈ Icc 0 L := ⟨hy.1, hy.2.le⟩
    by_cases hnear : y - x < δ
    · have hxx : x ∈ Ioo (x - δ) (x + δ) := by constructor <;> linarith
      have hyx : y ∈ Ioo (x - δ) (x + δ) := by constructor <;> linarith
      have heq := hlocal x hxC hxx hyx he
      linarith
    by_cases hwrap : L - (y - x) < δ
    · have hyy : y ∈ Ioo (y - δ) (y + δ) := by constructor <;> linarith
      have hshift : x + L ∈ Ioo (y - δ) (y + δ) := by constructor <;> linarith [hx.1, hy.2]
      have he' : speedCurve a P y = speedCurve a P (x + L) := he.symm.trans (haperiod x).symm
      have heq := hlocal y hyC hyy hshift he'
      linarith [hx.1, hy.2]
    · have hg : δ ≤ |x - y| := by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]; linarith
      have hw : |x - y| ≤ L - δ := by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]; linarith
      have hρgap := hsep x hxC y hyC hg hw
      have hbx := speedCurve_uniform_norm_sub_le ha hb hP hM.le hbound hxC
      have hby := speedCurve_uniform_norm_sub_le ha hb hP hM.le hbound hyC
      have heq : speedCurve b P x - speedCurve b P y =
          (speedCurve b P x - speedCurve a P x) + (speedCurve a P y - speedCurve b P y) := by
        rw [he]; abel
      have hnorm : ‖speedCurve b P x - speedCurve b P y‖ ≤
          2 * M * ∫ t in 0..L, |a t - b t| := by
        rw [heq]
        apply (norm_add_le _ _).trans
        have hn := add_le_add (by simpa only [norm_sub_rev] using hbx) hby
        nlinarith [hn]
      have hs := (lt_div_iff₀ (show 0 < 4 * M by positivity)).mp hsmall
      nlinarith
  intro x hx y hy he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact hordered x y hx hy hxy he
  · exact hordered y x hy hx hyx he.symm

end
end TightVer401
