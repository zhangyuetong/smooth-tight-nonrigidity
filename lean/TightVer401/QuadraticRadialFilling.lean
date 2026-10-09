import TightVer401.QuadraticFillerCartesian
import TightVer401.QuadraticRadialFillingJets
import TightVer401.QuadraticRadialFillingGlue
import TightVer401.QuadraticRadialFillingBoundary
import TightVer401.QuadraticRadialFillingExteriorCollar

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators

/-- The analytic quadratic filling of an actual incoming exterior potential.
Boundary functions, their smoothness and periodicity, the Cartesian filler,
matching Cartesian jets and seam smoothing are all derived. The coefficient
can exceed any prescribed bound. Global gradient injectivity is separate. -/
theorem exists_quadratic_radial_filling {R : ℝ} (hR : 0 < R)
    {F : Coord → ℝ} {U N : Set Coord} (hU : IsOpen U) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hF : ContDiffOn ℝ ∞ F U)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ))
    (M₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (M : ℝ) (H : Coord → ℝ), M₀ < M ∧ 0 < M ∧
      ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      ∀ x ∈ quadraticRadialFillingDomain R U,
        |H x - relativeSaddlePiecewise {y | planarRadius y < R}
          (quadraticFillerCartesianPotential R M (quadraticRadialFillingValueTrace F R)
            (quadraticRadialFillingRadialTrace F R)) F x| < η ∧
        ‖planarGradient H x - planarGradient (relativeSaddlePiecewise
          {y | planarRadius y < R}
          (quadraticFillerCartesianPotential R M (quadraticRadialFillingValueTrace F R)
            (quadraticRadialFillingRadialTrace F R)) F) x‖ < η := by
  obtain ⟨hh,hb⟩ := quadraticRadialFilling_traces_contDiff hF hU hCircleU
  have hhper := quadraticRadialFilling_valueTrace_periodic F R
  have hbper := quadraticRadialFilling_radialTrace_periodic hF hU hCircleU
  obtain ⟨hbpos,htrace⟩ := quadraticRadialFilling_traces_positive hF hU hR hCircleU
    hRadial hTangential
  obtain ⟨M,A,Uf,hM₀,hM,hDef,_hSmooth,_hPolar,_hSaddle,hJet,hInner,hUf,
      _hSub,hA,hDisk,hnegA⟩ := exists_quadratic_cartesian_filler hR hh hb hhper hbper
        hbpos htrace M₀
  have hGradient (θ : ℝ) : planarGradient A (saddlePolarChart ![R,θ]) =
      planarGradient F (saddlePolarChart ![R,θ]) := by
    obtain ⟨hi0,hi1⟩ := quadraticRadialFilling_cartesian_gradient hF hU hR hCircleU θ
    ext i
    fin_cases i
    · exact (hJet θ).2.1.trans hi0.symm
    · exact (hJet θ).2.2.trans hi1.symm
  obtain ⟨H,hH,hNeg,hExt,hRad,hClose⟩ := quadraticRadialFilling_glue hR hU hUf hN
    hCircleU hCircleN hDisk hF hA hnegF (fun x hx => (hnegA x hx).1)
    (fun θ => (hJet θ).1) hGradient hInner hη
  refine ⟨M,H,hM₀,hM,hH,hNeg,hExt,hRad,?_⟩
  simpa only [hDef] using hClose

end
end TightVer401
