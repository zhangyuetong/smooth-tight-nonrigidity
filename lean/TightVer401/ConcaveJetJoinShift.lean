import TightVer401.ConcaveJetJoinGlobal
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem jetSecondDeriv_add (q : ℝ → ℝ) (a x : ℝ) :
    deriv (deriv (fun t => q (t + a))) x = deriv (deriv q) (x + a) := by
  have he : deriv (fun t => q (t + a)) = fun t => deriv q (t + a) :=
    funext (deriv_comp_add_const q a)
  rw [he, deriv_comp_add_const]

theorem jetSecondDeriv_sub (q : ℝ → ℝ) (a x : ℝ) :
    deriv (deriv (fun t => q (t - a))) x = deriv (deriv q) (x - a) := by
  have he : deriv (fun t => q (t - a)) = fun t => deriv q (t - a) :=
    funext (deriv_comp_sub_const q a)
  rw [he, deriv_comp_sub_const]

theorem exists_concaveJetJoin_global_interval {A c B : ℝ} (hc : c ∈ Ioo A B)
    {qL qR : ℝ → ℝ} (hqL : ContDiff ℝ ∞ qL) (hqR : ContDiff ℝ ∞ qR)
    (hv : qL c = qR c) (hd : deriv qL c = deriv qR c)
    (hnegL : ∀ x ∈ Icc A B, deriv (deriv qL) x < 0)
    (hnegR : ∀ x ∈ Icc A B, deriv (deriv qR) x < 0) :
    ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ x ∈ Icc A B, deriv (deriv Q) x < 0) ∧
      (∃ α > A, EqOn Q qL (Iio α)) ∧
      (∃ β < B, EqOn Q qR (Ioi β)) := by
  let ql := fun x => qL (x + A)
  let qr := fun x => qR (x + A)
  have hql : ContDiff ℝ ∞ ql := hqL.comp (contDiff_id.add contDiff_const)
  have hqr : ContDiff ℝ ∞ qr := hqR.comp (contDiff_id.add contDiff_const)
  have hc' : c - A ∈ Ioo 0 (B - A) := by constructor <;> linarith [hc.1, hc.2]
  have hv' : ql (c - A) = qr (c - A) := by simpa [ql, qr] using hv
  have hd' : deriv ql (c - A) = deriv qr (c - A) := by
    simpa only [ql, qr, deriv_comp_add_const, sub_add_cancel] using hd
  have hnL : ∀ x ∈ Icc 0 (B - A), deriv (deriv ql) x < 0 := by
    intro x hx
    rw [jetSecondDeriv_add]
    exact hnegL _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hnR : ∀ x ∈ Icc 0 (B - A), deriv (deriv qr) x < 0 := by
    intro x hx
    rw [jetSecondDeriv_add]
    exact hnegR _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨Q, hQ, hnQ, ⟨α, hα, heL⟩, ⟨β, hβ, heR⟩⟩ :=
    exists_concaveJetJoin_global hc' hql hqr hv' hd' hnL hnR
  refine ⟨fun x => Q (x - A), hQ.comp (contDiff_id.sub contDiff_const), ?_,
    ⟨α + A, by linarith, ?_⟩, ⟨β + A, by linarith, ?_⟩⟩
  · intro x hx
    rw [jetSecondDeriv_sub]
    exact hnQ _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro x hx
    change x < α + A at hx
    have he := heL (show x - A ∈ Iio α by change x - A < α; linarith)
    simpa [ql] using he
  · intro x hx
    change β + A < x at hx
    have he := heR (show x - A ∈ Ioi β by change β < x - A; linarith)
    simpa [qr] using he

end
end TightVer401
