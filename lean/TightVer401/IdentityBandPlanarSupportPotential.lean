import TightVer401.IdentityBandPlanarSupportBand
import TightVer401.IdentityBandCentralSupportCompatibility

/-! The protected support annulus coupled to a specified actual potential.
This is an output predicate: actual reconstruction identifies the specified
potential with the already constructed one on its open image, retaining the
same charts, bending field and precise protected support. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- All constructed core data for this actual potential. This removes only
the initial existential potential from `IdentityBandPlanarSupportAnnulus`. -/
def IdentityBandPlanarSupportWithPotential {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) (G : Coord → ℝ) : Prop :=
  ∃ e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
    ∃ h : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
    ∃ g : OpenPartialHomeomorph Coord Coord,
    e.source = univ ∧ e.target = range (identityBandPlanarSource (d.bandSphereGauss (b := w))) ∧
    (e : _ → Coord) = identityBandPlanarSource (d.bandSphereGauss (b := w)) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ e ∧
    ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
    h.source = univ ∧ h.target = range (fun p : AddCircle T × Ioo (0 : ℝ) w => identityBandPlanarHorizontalCLM (d.bandMap p)) ∧
    (h : _ → Coord) = (fun p => identityBandPlanarHorizontalCLM (d.bandMap p)) ∧
    ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ h.symm h.target ∧
    ContDiffOn ℝ ∞ G e.target ∧ (∀ p, planarSupportMap G (e p) = d.bandMap p) ∧
    g.source = e.target ∧ g.target = h.target ∧ EqOn g (planarGradient G) g.source ∧
    ContDiffOn ℝ ∞ g g.source ∧ ContDiffOn ℝ ∞ g.symm g.target ∧
    ∃ he : e.source = univ,
      ∃ hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0,
      ∃ δ > 0, δ < w ∧
      ∃ hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w,
      ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        IsBandBending d.bandMap Y ∧ HasCompactSupport Y ∧ (∃ p, Y p ≠ 0) ∧
        IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target ∧
        (let Z := identityBandPlanarRegionField e he Y
         HasCompactSupport Z ∧ (∃ q, Z q ≠ 0) ∧
           (Subtype.val : e.target → Coord) '' tsupport Z = e '' tsupport Y ∧
           (Subtype.val : e.target → Coord) '' tsupport Z ⊆
             range (e ∘ identityFlowBandInclusion d hbalance 0 hinside))

/-- Forgetting the specified potential recovers the constructed core annulus. -/
theorem identityBandPlanarSupportWithPotential_annulus {T w : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G : Coord → ℝ}
    (h : IdentityBandPlanarSupportWithPotential d w G) :
    IdentityBandPlanarSupportAnnulus d w := ⟨G, h⟩

/-- Any actual smooth potential reconstructing the same band carries the
already constructed core charts and the very same protected bending field.
Reconstruction proves equality on the actual image, including derivative germs;
no new inverse or independent potential is supplied as an assumption. -/
theorem identityBandPlanarSupport_with_actual_potential {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) {Gnew : Coord → ℝ}
    (hcore : IdentityBandPlanarSupportAnnulus d w)
    (hnew : ContDiffOn ℝ ∞ Gnew
      (range (identityBandPlanarSource (d.bandSphereGauss (b := w)))))
    (hnewrec : ∀ p : AddCircle T × Ioo (0 : ℝ) w,
      planarSupportMap Gnew (identityBandPlanarSource (d.bandSphereGauss (b := w)) p) =
        d.bandMap p) : IdentityBandPlanarSupportWithPotential d w Gnew := by
  obtain ⟨Gold, e, h, g, heS, heT, heF, heD, heI, hhS, hhT, hhF, hhI,
    hGold, hrec, hgS, hgT, hgF, hgD, hgI, he, hbalance, δ, hδ, hδw,
    hinside, Y, hY, hcompact, hnonzero, hbend, hregion⟩ := hcore
  have hGnew : ContDiffOn ℝ ∞ Gnew e.target := by
    rw [heT]
    exact hnew
  have hrecnew : ∀ p : AddCircle T × Ioo (0 : ℝ) w,
      planarSupportMap Gnew (e p) = d.bandMap p := by
    intro p
    simpa only [heF] using hnewrec p
  have hmap : EqOn (planarSupportMap Gnew) (planarSupportMap Gold) e.target := by
    intro q hq
    have hn := hrecnew (e.symm q)
    have ho := hrec (e.symm q)
    rw [e.right_inv hq] at hn ho
    exact hn.trans ho.symm
  have hgrad : EqOn (planarGradient Gnew) (planarGradient Gold) e.target := by
    intro q hq
    ext i
    have hc := congrArg (fun u : Ambient => u (Fin.castSucc i)) (hmap hq)
    fin_cases i <;> simpa [planarGradient, planarSupportMap] using hc
  have hgnew : EqOn g (planarGradient Gnew) g.source := by
    intro q hq
    exact (hgF hq).trans (hgrad (hgS ▸ hq)).symm
  have hbendnew : IsInfinitesimalBendingOn (planarSupportMap Gnew) (Y ∘ e.symm) e.target := by
    refine ⟨hbend.1, ?_⟩
    intro q hq i j
    have hpot := (identityBand_planar_potential_overlap e.open_target hmap hq).1
    have hemap : planarSupportMap Gnew =ᶠ[𝓝 q] planarSupportMap Gold := by
      filter_upwards [hpot, hpot.eventuallyEq_nhds] with z hz hzg
      unfold planarSupportMap
      simp only [coordPartial, hzg.fderiv_eq (𝕜 := ℝ), hz]
    have hd := hemap.fderiv_eq (𝕜 := ℝ)
    unfold strain coordPartial
    rw [hd]
    exact hbend.2 q hq i j
  exact ⟨e, h, g, heS, heT, heF, heD, heI, hhS, hhT, hhF, hhI,
    hGnew, hrecnew, hgS, hgT, hgnew, hgD, hgI, he, hbalance, δ, hδ, hδw,
    hinside, Y, hY, hcompact, hnonzero, hbendnew, hregion⟩

end
end TightVer401
