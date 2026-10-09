import TightVer401.QuadraticFillerDescent
import TightVer401.VisibleConnectorLocalPotential

/-! Actual raw ruling data descended to the punctured Cartesian source. The
round annulus 1 ≤ r ≤ 2 uses physical s=L*theta/(2*pi) and u=(r-1)*h(s).
No source inverse, ordering, saddle sign, or incoming scalar germ is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Physical periodic parameter represented by the actual angle. -/
def visibleConnectorPhysicalParameter (L theta : ℝ) : ℝ := L * theta / (2 * Real.pi)

def visibleConnectorPolarSource (L : ℝ) (p w : ℝ → Coord) (h : ℝ → ℝ)
    (q : Coord) : Coord :=
  p (visibleConnectorPhysicalParameter L (q 1)) +
    ((q 0 - 1) * h (visibleConnectorPhysicalParameter L (q 1))) •
      w (visibleConnectorPhysicalParameter L (q 1))

def visibleConnectorPolarHeight (L : ℝ) (g : ℝ → ℝ) (gamma w : ℝ → Coord)
    (h : ℝ → ℝ) (q : Coord) : ℝ :=
  g (visibleConnectorPhysicalParameter L (q 1)) +
    ((q 0 - 1) * h (visibleConnectorPhysicalParameter L (q 1))) *
      (gamma (visibleConnectorPhysicalParameter L (q 1)) ⬝ᵥ
        w (visibleConnectorPhysicalParameter L (q 1)))

/-- Componentwise reuse of the proved scalar angular descent. -/
def visibleConnectorCartesianSource (L : ℝ) (p w : ℝ → Coord) (h : ℝ → ℝ)
    (z : Coord) : Coord := fun i =>
  angularDescentPotential (fun q => visibleConnectorPolarSource L p w h q i) z

def visibleConnectorCartesianHeight (L : ℝ) (g : ℝ → ℝ) (gamma w : ℝ → Coord)
    (h : ℝ → ℝ) : Coord → ℝ :=
  angularDescentPotential (visibleConnectorPolarHeight L g gamma w h)

theorem visibleConnectorPhysicalParameter_shift (L theta : ℝ) :
    visibleConnectorPhysicalParameter L (theta + 2 * Real.pi) =
      visibleConnectorPhysicalParameter L theta + L := by
  unfold visibleConnectorPhysicalParameter
  calc
    L * (theta + 2 * Real.pi) / (2 * Real.pi) =
        L * theta / (2 * Real.pi) + L * ((2 * Real.pi) / (2 * Real.pi)) := by ring
    _ = L * theta / (2 * Real.pi) + L := by rw [div_self Real.two_pi_pos.ne', mul_one]

theorem visibleConnectorPolarSource_contDiff {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (visibleConnectorPolarSource L p w h) := by
  have hs : ContDiff ℝ ∞ (fun q : Coord => visibleConnectorPhysicalParameter L (q 1)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const _
  have hu : ContDiff ℝ ∞ (fun q : Coord =>
      (q 0 - 1) * h (visibleConnectorPhysicalParameter L (q 1))) :=
    ((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul (hh.comp hs)
  exact (hp.comp hs).add (hu.smul (hw.comp hs))

theorem visibleConnectorPolarHeight_contDiff {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : ContDiff ℝ ∞ g) (hgamma : ContDiff ℝ ∞ gamma)
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (visibleConnectorPolarHeight L g gamma w h) := by
  have hs : ContDiff ℝ ∞ (fun q : Coord => visibleConnectorPhysicalParameter L (q 1)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const _
  have hu : ContDiff ℝ ∞ (fun q : Coord =>
      (q 0 - 1) * h (visibleConnectorPhysicalParameter L (q 1))) :=
    ((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul (hh.comp hs)
  have hd : ContDiff ℝ ∞ (fun q : Coord =>
      gamma (visibleConnectorPhysicalParameter L (q 1)) ⬝ᵥ
        w (visibleConnectorPhysicalParameter L (q 1))) := by
    simp only [dotProduct, Fin.sum_univ_two]
    exact (((contDiff_apply ℝ ℝ 0).comp (hgamma.comp hs)).mul
      ((contDiff_apply ℝ ℝ 0).comp (hw.comp hs))).add
      (((contDiff_apply ℝ ℝ 1).comp (hgamma.comp hs)).mul
        ((contDiff_apply ℝ ℝ 1).comp (hw.comp hs)))
  exact (hg.comp hs).add (hu.mul hd)

theorem visibleConnectorPolarSource_periodic {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : Periodic p L) (hw : Periodic w L) (hh : Periodic h L) (r theta : ℝ) :
    visibleConnectorPolarSource L p w h ![r, theta + 2 * Real.pi] =
      visibleConnectorPolarSource L p w h ![r, theta] := by
  simp only [visibleConnectorPolarSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    visibleConnectorPhysicalParameter_shift]
  rw [hp (visibleConnectorPhysicalParameter L theta), hw (visibleConnectorPhysicalParameter L theta),
    hh (visibleConnectorPhysicalParameter L theta)]

theorem visibleConnectorPolarHeight_periodic {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : Periodic g L) (hgamma : Periodic gamma L)
    (hw : Periodic w L) (hh : Periodic h L) (r theta : ℝ) :
    visibleConnectorPolarHeight L g gamma w h ![r, theta + 2 * Real.pi] =
      visibleConnectorPolarHeight L g gamma w h ![r, theta] := by
  simp only [visibleConnectorPolarHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    visibleConnectorPhysicalParameter_shift]
  rw [hg (visibleConnectorPhysicalParameter L theta), hgamma (visibleConnectorPhysicalParameter L theta),
    hw (visibleConnectorPhysicalParameter L theta), hh (visibleConnectorPhysicalParameter L theta)]

/-- Exact actual source pullback, including every positive radial value. -/
theorem visibleConnectorCartesianSource_polar {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : Periodic p L) (hw : Periodic w L) (hh : Periodic h L)
    {q : Coord} (hq : 0 < q 0) :
    visibleConnectorCartesianSource L p w h (saddlePolarChart q) =
      visibleConnectorPolarSource L p w h q := by
  ext i
  exact angularDescentPotential_polar
    (fun r theta => congrFun (visibleConnectorPolarSource_periodic hp hw hh r theta) i) hq

theorem visibleConnectorCartesianHeight_polar {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : Periodic g L) (hgamma : Periodic gamma L)
    (hw : Periodic w L) (hh : Periodic h L) {q : Coord} (hq : 0 < q 0) :
    visibleConnectorCartesianHeight L g gamma w h (saddlePolarChart q) =
      visibleConnectorPolarHeight L g gamma w h q :=
  angularDescentPotential_polar (visibleConnectorPolarHeight_periodic hg hgamma hw hh) hq

/-- The explicitly defined actual Cartesian functions are smooth off the
origin and have the SAME raw source/height formulas on the polar cylinder. -/
theorem visibleConnector_cartesian_descent {L : ℝ} (_hL : 0 < L)
    {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) :
    ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h) {z | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianHeight L g gamma w h) {z | 0 < planarRadius z} ∧
      EqOn (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart)
        (visibleConnectorPolarSource L p w h) {q | 0 < q 0} ∧
      EqOn (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart)
        (visibleConnectorPolarHeight L g gamma w h) {q | 0 < q 0} := by
  refine ⟨?_, ?_, fun q hq => visibleConnectorCartesianSource_polar hpL hwL hhL hq,
    fun q hq => visibleConnectorCartesianHeight_polar hgL hgammaL hwL hhL hq⟩
  · apply contDiffOn_pi.mpr
    intro i
    exact angularDescentPotential_contDiffOn
      ((contDiff_apply ℝ ℝ i).comp (visibleConnectorPolarSource_contDiff hp hw hh))
      (fun r theta => congrFun (visibleConnectorPolarSource_periodic hpL hwL hhL r theta) i)
  · exact angularDescentPotential_contDiffOn
      (visibleConnectorPolarHeight_contDiff hg hgamma hw hh)
      (visibleConnectorPolarHeight_periodic hgL hgammaL hwL hhL)

/-- Actual local equality is available before differentiating; it does not
identify a Cartesian derivative with an uncorrected polar derivative. -/
theorem visibleConnectorCartesianSource_polar_germ {L : ℝ} {p w : ℝ → Coord}
    {h : ℝ → ℝ} (hp : Periodic p L) (hw : Periodic w L) (hh : Periodic h L)
    {q : Coord} (hq : 0 < q 0) :
    (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart) =ᶠ[𝓝 q]
      visibleConnectorPolarSource L p w h := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hq] with x hx
  exact visibleConnectorCartesianSource_polar hp hw hh hx

theorem visibleConnectorCartesianHeight_polar_germ {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : Periodic g L) (hgamma : Periodic gamma L)
    (hw : Periodic w L) (hh : Periodic h L) {q : Coord} (hq : 0 < q 0) :
    (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart) =ᶠ[𝓝 q]
      visibleConnectorPolarHeight L g gamma w h :=
  angularDescentPotential_polar_germ (visibleConnectorPolarHeight_periodic hg hgamma hw hh) hq

theorem visibleConnectorCartesianSource_polar_derivatives {L : ℝ} {p w : ℝ → Coord}
    {h : ℝ → ℝ} (hp : Periodic p L) (hw : Periodic w L) (hh : Periodic h L)
    {q : Coord} (hq : 0 < q 0) :
    fderiv ℝ (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart) q =
        fderiv ℝ (visibleConnectorPolarSource L p w h) q ∧
      fderiv ℝ (fderiv ℝ (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart)) q =
        fderiv ℝ (fderiv ℝ (visibleConnectorPolarSource L p w h)) q := by
  have he := visibleConnectorCartesianSource_polar_germ hp hw hh hq
  refine ⟨he.fderiv_eq, ?_⟩
  have hd : fderiv ℝ (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart)
      =ᶠ[𝓝 q] fderiv ℝ (visibleConnectorPolarSource L p w h) := by
    filter_upwards [he.eventuallyEq_nhds] with x hx
    exact hx.fderiv_eq
  exact hd.fderiv_eq

theorem visibleConnectorCartesianHeight_polar_derivatives {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : Periodic g L) (hgamma : Periodic gamma L)
    (hw : Periodic w L) (hh : Periodic h L) {q : Coord} (hq : 0 < q 0) :
    fderiv ℝ (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart) q =
        fderiv ℝ (visibleConnectorPolarHeight L g gamma w h) q ∧
      fderiv ℝ (fderiv ℝ (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart)) q =
        fderiv ℝ (fderiv ℝ (visibleConnectorPolarHeight L g gamma w h)) q := by
  have he := visibleConnectorCartesianHeight_polar_germ hg hgamma hw hh hq
  refine ⟨he.fderiv_eq, ?_⟩
  have hd : fderiv ℝ (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart)
      =ᶠ[𝓝 q] fderiv ℝ (visibleConnectorPolarHeight L g gamma w h) := by
    filter_upwards [he.eventuallyEq_nhds] with x hx
    exact hx.fderiv_eq
  exact hd.fderiv_eq

/-- Component Hessians are the Hessians of the actual source pullback. -/
theorem visibleConnectorCartesianSource_polar_component_hessian {L : ℝ}
    {p w : ℝ → Coord} {h : ℝ → ℝ} (hp : Periodic p L) (hw : Periodic w L)
    (hh : Periodic h L) {q : Coord} (hq : 0 < q 0) (a : Fin 2) :
    planarHessian (fun x => visibleConnectorCartesianSource L p w h (saddlePolarChart x) a) q =
      planarHessian (fun x => visibleConnectorPolarSource L p w h x a) q :=
  angularDescentPotential_polar_planarHessian
    (fun r theta => congrFun (visibleConnectorPolarSource_periodic hp hw hh r theta) a) hq

theorem visibleConnectorCartesianHeight_polar_hessian {L : ℝ} {g h : ℝ → ℝ}
    {gamma w : ℝ → Coord} (hg : Periodic g L) (hgamma : Periodic gamma L)
    (hw : Periodic w L) (hh : Periodic h L) {q : Coord} (hq : 0 < q 0) :
    planarHessian (visibleConnectorCartesianHeight L g gamma w h ∘ saddlePolarChart) q =
      planarHessian (visibleConnectorPolarHeight L g gamma w h) q :=
  angularDescentPotential_polar_planarHessian
    (visibleConnectorPolarHeight_periodic hg hgamma hw hh) hq

end
end TightVer401