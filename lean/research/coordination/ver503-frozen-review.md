# ver503 frozen DOM/DESC source review

Reviewed read-only against fetched publication base a37ab10a84e607bc5962e8880a60544bad7af222.
The old engine is formalization/ver401; publication engine is lean, namespace
TightVer401. Git blob identity was used rather than working-file appearance.
Historical ver500 audits provide provenance only; the ver503 integration must
compile and audit its own current source before receiving integration credit.

## Minimum reviewed source changes

| Module suffix after TightVer401 | Proof commit | SHA256 | Action |
|---|---|---|---|
| VisibleConnectorGradientOrderWitnessApplication | 1bb393a397ecdf914a0d8b6fc5262fec2f776ec5 | cab7743cbe79cdd7640b29fcf2e86e8fe62d3e9687020be0b9cd06958231ae59 | add |
| VisibleConnectorSourceOrder | 77108914d607362c637104e80cdb9dc1f581abb7 | d915e6f10dc3018a8ce0b679770bebb87220b32eaf2a1a1d9fed5bc701efd2e2 | add |
| VisibleConnectorSourceOrderRound | 2c1bc5b113fc891e7a77265355b240d09fa05dfc | c710f55a4ab6462fee7e2d1ebe87a6330af4935708274e05bc05818b1221c3a1 | add |
| VisibleConnectorSourceOrderPhysical | f424885a65712589fd9dcecf30e01ca8d95d2c0f | b3294e324d7b699aff309f6c2e4bfb02975d60b2810ef3e29e375896332faaae | add |
| VisibleConnectorDisplacedSeamPhaseSigns | 5e31cde9afc8ab7b5b84b8c2e69ab73ce35ce738 | 97c035f524f9c17e55b68497d4ac06d57466b78df856dbfe3a97e5006fd821e5 | replace older version |
| VisibleConnectorDisplacedSeamRebase | bb13fe18e218af4b5d9b040de2d94ab5df3da0b5 | 5bb2fee3619c9efec4ff33346a9181862631c622da132a9c7557b163a4dcbfe4 | add |

Minimal new root imports are GradientOrderWitnessApplication,
SourceOrderPhysical and DisplacedSeamRebase. Preserve the existing PhaseSigns
import. Existing GradientOrder, GradientOrderApplication and
GradientOrderPhysical are exact publication/frozen DOM Git blob matches;
replacing them would add no new proof. All20 audited DESC manifest source rows
were compared:18 match publication, only PhaseSigns and Rebase differ or are absent.

## Audits and consumer obligations

DOM final source-order root/report e4f5290fde3d85c00d3dd19ff2af332956138360:
PASS1156 modules/15261 declarations, 2026-10-09T01:39:22.747767UTC,
certificate SHA256 2af4e2f3bcfcadd552b3994fd8e737100a437dd67bdba93664f289a2549bbc2c.
Gradient witness was audited in a4e27462984efa048f5037e02ca3aa38149f2be1:
PASS1153/15255; the final audit preserves its source and all prior types.
DESC final root/report8dc92175abac03d17b2b793730d85ba3bafd9938:
PASS1046/14625, 2026-10-09T01:38:26.014886UTC. Both report zero admissions and
custom axioms. Exact public types are retained in frozen final manifests.

| Export / construction | Exact consumer and SAME-object inputs | Remaining ordinary premises |
|---|---|---|
| visibleConnectorSourceOrder_retained_incoming_terminal | OrdinaryData.source_nesting; SAME actual F/O, original D.incoming.p, terminal T.p and caller-selected positive fills | Actual closed-round coverage, positive Jacobian, honest boundary equations, positive Jordan fills and source range disjointness |
| visibleConnectorGradientOrder_retained_incoming_terminal | OrdinaryData.gradient_nesting; SAME final G/U, retained D/T and four caller-selected fills | Derived source nesting, closed source annulus in U, negative Hessian, full open Gin equality neighborhood and gradient boundary disjointness |
| visibleConnectorDisplaced_exists_uniform_phase_signs | Incoming rebasing/seam producer; SAME existential native e | Caller retains its actual central solution/source, smooth joint phase/height, shifts/periods and zero-axis values; compatible eta/rho choices still require construction |
| visibleConnector_rebase_source/height/gradient and companions | Incoming seam matching; SAME old ruling and affine old height b(s)+u*d(s) | Actual Delta nonzero and a',d nonzero where needed; actual original curve/scalar identification and open Gin germ remain obligations |

The positive/signed SourceOrder proof uses actual signed counts. Its round
specialization proves round1<round2 nesting internally. Although it imports
SourceInverseGlobal for retained helpers, it does not invoke that global inverse
theorem or assume desired terminal/incoming nesting. The gradient witness derives
actual incoming final-gradient equality from the FULL open Gin germ; first jets
alone do not supply it. No independent inverse, scalar or fill is reselected.

## Relative smoothing and pending snapshot

All six RelativeSaddle sources adopted by DESC commit
b3f8649a2b51cfd9a8165970488aadd3348b10c8 exactly match publication AND old
integration root: Collar, ErrorControl, ExteriorDomains, Jets, Piecewise,
Smoothing. No replacement is needed. Their locally uncompiled DESC adoption is
separate from the old root's prior compiled validation; fresh source validation
is still required in ver503.

The13 IncomingGin sources at517608135b817ed86f860776bbf0cf50b0a7f302 were
absent publication and explicitly UNCOMPILED. They are preserved as exact Git
bytes under ../../pending/IncomingGin5176081, outside certified module imports.
Every SHA256 was checked against the final DESC checkpoint; that directory has
its own README and provenance manifest. This preservation grants no proof credit.

Open producer gates remain: actual selected source/core placement; one compatible
eta/rho family with SAME native e and Cartesian E distinguished; displaced seam
embedding and scalar/gradient matching; displaced terminal C1/Jordan/nonzero/norm
margins; full fixed V with Vraw subset SAME E.target; exactly one relative on_sides
application producing H, open Gin/raw-terminal equality neighborhoods, closed-band
negative Hessian; populated actual H/U/F/O OrdinaryData family; rebuilt gradient
inverse for final H; completion/saddle/torus/final pair applications.
SelectedSourceGeometryPhase was historically scope-blocked but is now explicitly
authorized by the ver503 request. It remains an original construction obligation.

No compiler or proof-source edits were performed by this review. Only this review,
minimal final provenance documents and the pending exact-source preservation were
written. No bulk logs, build artifacts or historical kernel reports were copied.
