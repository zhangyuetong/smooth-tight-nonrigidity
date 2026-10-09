# Two elementary background proofs requested 2026-10-10

Historical planning/checkpoint record, superseded by the [completed formalization report](../../formalization-report.md) and current [audit snapshot](../../audit/snapshot.json). Earlier status statements below refer to their dated source checkpoints.

The user asked to prove the two simple classical propositions: noncircular ellipse-axis recognition and smooth reparameterization of equal embedded images. Full current-source verification **PASS** at `3a8f551901af2d613bd0950df4ee11fff462f79f` on `2026-10-09T18:31:19.661370+00:00` (Audit: 166.665 seconds). Both EXACT closed proof inhabitants and ONLY `ClassicalExternalResults` before the ultimate first existential are checked. The closure has no admissions or custom axioms; exactly two external statements remain. Historical source `07a2980` certified the earlier four-statement theorem. This follow-up is COMPLETE.

## Exact interfaces and owners

- tooling_migration owns `TightVer401/MarkerEllipseAxesRecognitionProof.lean`: `markerEllipseAxesRecognition_proved : MarkerEllipseAxesRecognition`, no premises. Recognize the unique enclosing-ball center and longest endpoint pair, then use Euclidean orthogonality to derive all three coordinate signs.
- frozen_review owns `TightVer401/ClassicalEmbeddingSmoothFactor.lean`: recover actual smoothness of a continuous factor from smooth composition with a map having an injective differential. Construct a continuous-linear left inverse of that differential and apply the existing square inverse-function theorem. This fills a missing pinned-library convenience bridge without an external grant.
- migration_review owns `TightVer401/ClassicalEmbeddedReparamProof.lean`: `classicalEmbeddedImageReparametrization_proved : ClassicalEmbeddedImageReparametrizationClaim`, no premises. Equal ranges and actual embeddings give a source homeomorphism; local charts and the smooth-factor lemma prove its two directions smooth.
- root owns imports, ultimate theorem, registry, coverage/verifier, blueprint, documentation and audits. Root is sole compiler writer. Subagents never compile or edit shared files.

## Exact final consumer

`exists_noncongruent_isometric_tight_tori_pair_of_classical` supplies these two proved claims to `actualSeed_exists_markedTorus_pair_of_ordinary_connector_family`. Its only remaining parameter will be `background : ClassicalExternalResults`, containing positive-Gauss tightness and equal-image fixed-open uniqueness. No original seed, field, clock, graph, scalar, inverse, completed tuple or full meridian is selected anew.

## Validation and scope

Directly compile each new proof leaf, then the final theorem. The full current-source verifier must audit the exact proof inhabitants and final theorem, retain only the two remaining registered external statements, and reject admissions/custom axioms. Publish the new source-bound certificate and preserve four-statement historical provenance. Extension/Cantor scope remains deferred.
