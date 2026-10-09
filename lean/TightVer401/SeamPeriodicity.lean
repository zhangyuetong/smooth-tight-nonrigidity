import TightVer401.SmoothingSeamPeriodicity
import TightVer401.SeamCompactCollar
import Mathlib.Algebra.Order.ToIntervalMod

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix

theorem seamCoordinateJacobian_periodic {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ)
    (L : ℝ) (hp : ∀ p, Φ (smoothingSeamShift L p)=Φ p) (p : Coord) :
    seamCoordinateJacobian Φ (smoothingSeamShift L p)=seamCoordinateJacobian Φ p := by
  ext a i
  apply smoothing_seam_partial_periodic ((contDiff_apply ℝ ℝ a).comp hΦ) L
  exact fun q => congrFun (hp q) a

theorem seamChartConnection_periodic {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ)
    (L : ℝ) (hp : ∀ p, Φ (smoothingSeamShift L p)=Φ p) (k i j : Fin 2) (p : Coord) :
    seamChartConnection Φ k i j (smoothingSeamShift L p)=seamChartConnection Φ k i j p := by
  unfold seamChartConnection
  rw [seamCoordinateJacobian_periodic hΦ L hp]
  have hh (a : Fin 2) : planarHessian (fun q => Φ q a) (smoothingSeamShift L p)=
      planarHessian (fun q => Φ q a) p := by
    ext i j
    exact smoothing_seam_hessian_periodic (F := fun q => Φ q a)
      ((contDiff_apply ℝ ℝ a).comp hΦ) L (fun q => congrFun (hp q) a) p i j
  simp only [hh]

theorem seamCorrectedHessian_periodic {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) (L : ℝ)
    (hpΦ : ∀ p, Φ (smoothingSeamShift L p)=Φ p)
    (hpF : ∀ p, F (smoothingSeamShift L p)=F p) (p : Coord) :
    seamCorrectedHessian Φ F (smoothingSeamShift L p)=seamCorrectedHessian Φ F p := by
  ext i j
  unfold seamCorrectedHessian
  rw [smoothing_seam_hessian_periodic hF L hpF]
  simp only [seamChartConnection_periodic hΦ L hpΦ,smoothing_seam_partial_periodic hF L hpF]

theorem seam_periodic_eq_representative {V : Type*} {F : ℝ → V} {L : ℝ}
    (hL : 0 < L) (hp : Function.Periodic F L) (s : ℝ) :
    F s=F (toIcoMod hL 0 s) := by
  conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
  exact hp.zsmul (toIcoDiv hL 0 s) _

/-- An actual period and compactness give a regular collar along the entire seam. -/
theorem seamCoordinateJacobian_periodic_regular_collar {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {L : ℝ} (hL : 0 < L)
    (hp : ∀ p, Φ (smoothingSeamShift L p)=Φ p)
    (hJ : ∀ s, (seamCoordinateJacobian Φ (![s,0])).det ≠ 0) :
    ∃ r > 0, ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian Φ (![s,t])).det ≠ 0 := by
  obtain ⟨r,hr,hreg⟩ := seamCoordinateJacobian_compact_regular_collar hΦ
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) L)) (fun s _ => hJ s)
  refine ⟨r,hr,fun s t ht => ?_⟩
  have hs : toIcoMod hL 0 s ∈ Icc (0 : ℝ) L := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hp' : Function.Periodic (fun u : ℝ => (seamCoordinateJacobian Φ (![u,t])).det) L := by
    intro u
    exact congrArg Matrix.det (seamCoordinateJacobian_periodic hΦ L hp (![u,t]))
  rw [seam_periodic_eq_representative hL hp' s]
  exact hreg _ hs t ht

end
end TightVer401
