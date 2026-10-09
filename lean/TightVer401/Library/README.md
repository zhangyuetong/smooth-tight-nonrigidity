# Reusable Lean results

These entry points organize existing proofs by their mathematical use. They add no declarations and preserve the `TightVer401` namespace, original source files, hypotheses and attribution. Import a single group for a focused interface, or `TightVer401.Library` for the complete collection including the torus construction.

| Entry point | Main uses | Representative exports |
|---|---|---|
| [Calculus](Calculus.lean) | Recover smoothness through an injective differential, necessary Hessian tests, local inverses and regular values | `classicalEmbedding_contDiffAt_factor`, `localMax_fderiv_fderiv_apply_nonpos`, `gaussTightness_dense_regular_values` |
| [Topology](Topology.lean) | Connected strict superlevels, stability under uniform approximation, punctured spheres and inversion on Jordan annuli | `height_superlevel_isPreconnected_of_unique_localMax`, `height_superlevel_isPreconnected_of_uniform_approximants`, `annular_degree_global_diffeomorphism` |
| [Analysis](Analysis.lean) | Finite moments, constrained smooth perturbations, nonlinear periods, scalar ODEs and periodic curves | `finite_moment_period_prescription_smooth_circle`, `scalarLinearODE_endpoint`, `riccati_solutions_unique`, `periodic_nonconstant_derivative_signs` |
| [Riemannian](Riemannian.lean) | Genuine intrinsic distance, tangent isometries and compact fixed-open rigidity | `connected_emetric_edist_ne_top`, `riemannianEDist_homeomorph_eq_of_tangent_enorm`, `isometry_eq_id_of_fixed_open_compact` |
| [Differential geometry](DifferentialGeometry.lean) | Support potentials, Legendre transport, ruled surfaces, relative saddle smoothing and height cuts | `sphereSupportMap_curvature`, `planarLegendre_hessian`, `ruled_supported_kernel`, `exists_relative_saddle_smoothing_on_sides` |
| [Construction](Construction.lean) | The actual seed, coherent connector family, completed support, marking and first torus pair | `exists_noncongruent_isometric_tight_tori_pair` |

For example:

```lean
import TightVer401.Library.Calculus
import TightVer401.Library.Topology

#check TightVer401.classicalEmbedding_contDiffAt_factor
#check TightVer401.localMax_fderiv_fderiv_apply_nonpos
#check TightVer401.height_superlevel_isPreconnected_of_uniform_approximants
```

The smallest general results are useful outside this construction. A C² real function on a real normed space has a nonpositive Hessian in every direction at a local maximum. Arbitrarily close uniform approximations preserve preconnected strict superlevels, with no continuity or compactness assumption on the underlying function or space. On a compact locally connected space, a continuous function with at most one local maximum has preconnected strict superlevels. Smooth factor recovery uses an injective differential, a complete outer domain and a finite-dimensional outer target. Tangent-norm preservation by a C¹ homeomorphism with C¹ inverse preserves the actual Riemannian path distance.

Larger packages retain more structure. Moment prescription uses periodic functions and a square-root response; curve embedding stability keeps the direction field fixed and speeds positive; annular inversion requires genuine Jordan boundaries and degree data; saddle smoothing requires matching jets and explicit sign hypotheses. These conditions are part of the theorem interfaces.

Some geometric modules also contain adapters for the registered torus atlas. Intrinsic metric-space packaging uses existing Mathlib constructors, and regular-value selection uses the pinned Sard theorem. The [formalization report](../../formalization-report.md) distinguishes substantive project proofs, adapters, inherited foundations and possible future library extractions. Potential extractions are not upstream submissions.

Current proof certification is recorded in [the source-bound audit](../../audit/snapshot.json). The complete manuscript coverage remains a separate [scope register](../../coverage.json).
