import TightVer401.AnnularDegreeLocal
import TightVer401.AnnularDegreeJordan
import TightVer401.SeamNormalCoordinates
import TightVer401.PlanarGradientInverse
import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreen
import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization

/-! Ordinary annular map, boundary-winding and gradient interfaces.
These are definitions only. They import no annular counting, Green proof,
global inverse theorem, or pending contract. The actual proofs import these
same definitions; downstream pending consumers can use the stable types.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff

/-- The actual circle argument of the displacement from a target point. -/
def annularArgumentPullback (f : ℂ → ℂ) (y : ℂ) (z : ℂ) : UnitAddCircle :=
  normalizedArgument (f z - y)

/-- The first coefficient of the actual pulled-back angular differential. -/
def annularAngularFormP (f : ℂ → ℂ) (y : ℂ) (z : ℂ) : ℝ :=
  circleFDeriv (annularArgumentPullback f y) z 1

/-- The second coefficient of the actual pulled-back angular differential. -/
def annularAngularFormQ (f : ℂ → ℂ) (y : ℂ) (z : ℂ) : ℝ :=
  circleFDeriv (annularArgumentPullback f y) z Complex.I

/-- The actual map written in the existing complex coordinates. -/
def annularComplexConjugate (F : Coord → Coord) : ℂ → ℂ :=
  seamComplexCoord.symm ∘ F ∘ seamComplexCoord

def annularJordanBoundary (Houter Hinner : ℂ ≃ₜ ℂ) : Set ℂ :=
  frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner)

def annularCoordJordanClosure (Houter Hinner : ℂ ≃ₜ ℂ) : Set Coord :=
  seamComplexCoord '' annularJordanClosure Houter Hinner

def annularCoordJordanInterior (Houter Hinner : ℂ ≃ₜ ℂ) : Set Coord :=
  seamComplexCoord '' annularJordanInterior Houter Hinner

/-- Actual winding sum on the induced annulus boundary. Both source disk
contours are positive; the inner boundary has the opposite induced orientation.
The image curves may have vanishing differential rank. -/
def annularBoundaryIntegral (F : Coord → Coord) (γouter γinner : ℝ → ℂ) (y : ℂ) : ℝ :=
  planarFormIntegral (annularAngularFormP (annularComplexConjugate F) y)
    (annularAngularFormQ (annularComplexConjugate F) y) γouter -
  planarFormIntegral (annularAngularFormP (annularComplexConjugate F) y)
    (annularAngularFormQ (annularComplexConjugate F) y) γinner

/-- Ordinary one-point boundary winding data for either component assignment.
`swap = true` means the outer source curve maps onto the inner target curve.
The two raw disk windings agree; the induced annular orientations are opposite.
There is no global image, injectivity, degree identity, or full-profile premise. -/
def AnnularDegreeOrdinaryBoundaryClaim : Prop :=
  ∀ (Ho Hi To Ti : ℂ ≃ₜ ℂ) (γo γi : ℝ → ℂ),
    PositiveJordanParametrization Ho γo →
    PositiveJordanParametrization Hi γi →
    closure (jordanInterior Hi) ⊆ jordanInterior Ho →
    closure (jordanInterior Ti) ⊆ jordanInterior To →
    ∀ (F : Coord → Coord) (O : Set Coord), IsOpen O → ContDiffOn ℝ ∞ F O →
      annularCoordJordanClosure Ho Hi ⊆ O →
      ∀ (s : ℤ), (s = 1 ∨ s = -1) →
        (∀ x ∈ annularCoordJordanInterior Ho Hi,
          0 < (s : ℝ) * annularJacobian F x) →
        ∀ (swap : Bool)
          (Bo : frontier (jordanInterior Ho) ≃ₜ
            frontier (jordanInterior (if swap then Ti else To)))
          (Bi : frontier (jordanInterior Hi) ≃ₜ
            frontier (jordanInterior (if swap then To else Ti))),
          (∀ x, (Bo x : ℂ) = annularComplexConjugate F x) →
          (∀ x, (Bi x : ℂ) = annularComplexConjugate F x) →
          ∀ (w : ℝ), |w| = 1 →
            planarFormIntegral
              (annularAngularFormP (annularComplexConjugate F) ((if swap then Ti else To) 0))
              (annularAngularFormQ (annularComplexConjugate F) ((if swap then Ti else To) 0)) γo = w →
            planarFormIntegral
              (annularAngularFormP (annularComplexConjugate F) ((if swap then To else Ti) 0))
              (annularAngularFormQ (annularComplexConjugate F) ((if swap then To else Ti) 0)) γi = w →
            ∃ e : OpenPartialHomeomorph Coord Coord,
              e.source = annularCoordJordanInterior Ho Hi ∧
              e.target = annularCoordJordanInterior To Ti ∧
              (e : Coord → Coord) = F ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
              ∃ H : annularCoordJordanClosure Ho Hi ≃ₜ annularCoordJordanClosure To Ti,
                ∀ x, (H x : Coord) = F x

/-- Actual gradient specialization with interior Hessian sign only. -/
def AnnularDegreeGradientClaim : Prop :=
  ∀ (Ho Hi To Ti : ℂ ≃ₜ ℂ) (γo γi : ℝ → ℂ),
    PositiveJordanParametrization Ho γo →
    PositiveJordanParametrization Hi γi →
    closure (jordanInterior Hi) ⊆ jordanInterior Ho →
    closure (jordanInterior Ti) ⊆ jordanInterior To →
    ∀ (G : Coord → ℝ) (O : Set Coord), IsOpen O → ContDiffOn ℝ ∞ G O →
      annularCoordJordanClosure Ho Hi ⊆ O →
      ∀ (s : ℤ), (s = 1 ∨ s = -1) →
        (∀ x ∈ annularCoordJordanInterior Ho Hi,
          0 < (s : ℝ) * (planarHessian G x).det) →
        ∀ (swap : Bool)
          (Bo : frontier (jordanInterior Ho) ≃ₜ
            frontier (jordanInterior (if swap then Ti else To)))
          (Bi : frontier (jordanInterior Hi) ≃ₜ
            frontier (jordanInterior (if swap then To else Ti))),
          (∀ x, (Bo x : ℂ) = annularComplexConjugate (planarGradient G) x) →
          (∀ x, (Bi x : ℂ) = annularComplexConjugate (planarGradient G) x) →
          ∀ (w : ℝ), |w| = 1 →
            planarFormIntegral
              (annularAngularFormP (annularComplexConjugate (planarGradient G)) ((if swap then Ti else To) 0))
              (annularAngularFormQ (annularComplexConjugate (planarGradient G)) ((if swap then Ti else To) 0)) γo = w →
            planarFormIntegral
              (annularAngularFormP (annularComplexConjugate (planarGradient G)) ((if swap then To else Ti) 0))
              (annularAngularFormQ (annularComplexConjugate (planarGradient G)) ((if swap then To else Ti) 0)) γi = w →
            ∃ e : OpenPartialHomeomorph Coord Coord,
              e.source = annularCoordJordanInterior Ho Hi ∧
              e.target = annularCoordJordanInterior To Ti ∧
              (e : Coord → Coord) = (planarGradient G) ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
              ∃ H : annularCoordJordanClosure Ho Hi ≃ₜ annularCoordJordanClosure To Ti,
                ∀ x, (H x : Coord) = (planarGradient G) x

end
end TightVer401
