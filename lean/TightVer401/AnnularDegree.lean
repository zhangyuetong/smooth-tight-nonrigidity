import TightVer401.AnnularDegreeCount
import TightVer401.AnnularDegreeExclusion
import TightVer401.AnnularDegreeLocalInverse
import TightVer401.AnnularDegreeLocalJacobian
import TightVer401.AnnularDegreeWinding
import TightVer401.AnnularDegreeGreen
import TightVer401.AnnularDegreeJordan
import TightVer401.AnnularDegreeLocalSign
import TightVer401.AnnularDegreeFormula
import TightVer401.AnnularDegreeGlobal
import TightVer401.AnnularDegreeBoundaryWinding
import TightVer401.AnnularDegreeBoundaryHomeomorphs
import TightVer401.AnnularDegreeCriterion

/-!
Prerequisites for ver500 `lem:degree` and blueprint `R.degree`.

The actual derivative gives local inversion/openness and finite fibers off the
boundary image. The signed count is formed from those actual fibers. Winding
uses the pinned OpenAI normalized argument and covering lift. Annular Green
excision is derived from the pinned proved Green formulas on the two source
Jordan disks, with the same extended one-form on both.

The actual angular pullback and its local contributions are constructed in
`AnnularDegreeFormula`: disjoint small disks around the finite actual fiber
give the boundary winding sum as the common actual Jacobian sign times its
cardinality. Source orientation is calibrated by actual argument increments.
The global inverse assembly derives unique interior fibers, excludes boundary
hits by actual local openness and constructs the smooth interior inverse and
compact-closure homeomorphism. The public interface below has only geometric,
smoothness, actual Jacobian and actual boundary-winding hypotheses.
-/

namespace TightVer401

/-- ver500 `lem:degree`: actual winding counts actual regular preimages;
boundary differential rank is permitted to degenerate. -/
theorem annular_degree_global_diffeomorphism : AnnularDegreeOrdinaryBoundaryClaim :=
  annular_degree_ordinary_boundary_criterion_core

end TightVer401
