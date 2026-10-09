# Gauss tightness worker — exact claim proved

Worktree: `ver503-gauss-tightness`; branch `codex/ver503-gauss-tightness`; base `7483524763ca77fb8d86d4974424fbc6ecafee3f`.

Status: CLOSED, current-source kernel checked. The exact export is `TightVer401.classicalPositiveGaussTightness_proved : ClassicalPositiveGaussTightnessClaim` in `lean/TightVer401/ClassicalPositiveGaussTightnessProof.lean`. No extra premise, grant, admission, custom axiom, outward-normal convention, or zero-curvature-area condition was introduced. The final claim is the unchanged definition from `ClassicalExternal.lean`. Original constructions, manuscript, pins, registry, shared Audit and shared final-pair sources remain untouched.

Final consumer: integration's exact positive-Gauss theorem parameter in the final nonrigid-torus pair route. Import `TightVer401.ClassicalPositiveGaussTightnessProof` and supply `classicalPositiveGaussTightness_proved` to that parameter. It consumes the SAME actual native embedding X, global smooth unit normal N with actual native differential orthogonality, entire positive-curvature source, and supplied Gauss partial homeomorphism to the sphere minus the finite E. The theorem retains the exact original smooth chart/inverse premises even though its proof needs only the chart's topological and same-normal contracts.

## Validation

Private command: dot-source `scripts/worktree-environment.ps1`, then `python scripts/build.py --module TightVer401.ClassicalPositiveGaussAudit --jobs 1`.

- Final proof DIRECT PASS 51.513s, source SHA256 `8be6b05eb071bd1c409b2b2de1dc87e327f6010effb601ac9977fbe7087b9a9e`, olean SHA256 `2b51832c19497e9cc87f580c41c1021f8831e97d86c1fd3cd83fe46e0a4d816b`.
- Dedicated final audit DIRECT PASS 49.687s, source SHA256 `6a0a7453fb0b5efad78ed9b5f220dca2ff85a03fbd8b4e39a3e1a44c3c1b19bd`, log SHA256 `a3ee6df7834433aa5108b3b77f3c24ff591063fc2392eb84ea145e82ffada45d`. Its successful build report is `lean/build-logs/TightVer401.ClassicalPositiveGaussAudit.build.json`.
- Printed axiom closure: `[propext, Classical.choice, Quot.sound]` only.
- Lean 4.33.0-rc1, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, pinned OAI `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, source-compatibility profile.
- Required baseline `python scripts/verify.py --jobs 1` is running; final result will be appended before freeze.

All new geometric leaves were actually compiled in this checkout. Unchanged dependency caches were copied into empty PRIVATE targets using the documented `-SeedCache -SeedEngine .../ver503-integration/lean` command, then validated by source/dependency/object hashes. Copied certificates alone received no proof credit. The root was the only compiler writer; three scoped subagents edited exclusive source leaves only. The shared dependency cache remained read only. The initial sandbox launcher failure was recovered with approved escalation; it is not a blocker.

## Same-object proof chain

1. `GaussTightnessCriticalNormal`: Fermat and the pinned one-dimensional normal-space result imply a unit local-height-maximum direction is either sign of the actual normal.
2. `GaussTightnessRegularValues` and `GaussTightnessSphereRegular`: actual critical images are null by pinned Sard; one Bool-indexed Sard application handles BOTH normal signs on the SAME global Coord cover. No intersection-of-arbitrary-dense-sets inference occurs.
3. `HeightTightnessSecondDerivative`, `GaussTightnessHeightHessian`, `GaussTightnessDifferential`, `GaussTightnessMaximumCurvature`, `GaussTightnessMaximumTrace`: actual regular height maxima have negative semidefinite actual height Hessian, nonzero actual II determinant, positive intrinsic K, and actual trace signs distinguishing both normal signs.
4. `ClassicalPositiveGaussConnected`: finite-punctured sphere preconnectedness transported through the supplied actual Gauss partial homeomorphism gives preconnectedness of the ENTIRE native positive-curvature region.
5. `GaussTightnessNativeCharts` and `GaussTightnessNativeSign`: actual smooth quotient representatives, ENTIRE-domain chart translation, actual immersion and unit normal at every coordinate, and actual native II continuity descended through the open-surjective quotient cover.
6. `GaussTightnessDefiniteSign` and `GaussTightnessNativeMaximumUnique`: det-positive symmetric actual II has nonzero trace, its sign is constant on the entire positive source, hence local maxima have the same actual normal sign; same-object Gauss injectivity gives unique local maximum.
7. `GaussTightnessNativeRegular`: dense sphere regular directions transfer through the actual global smooth quotient cover to the exact native normal differential at coordinate zero.
8. Root-owned `HeightSuperlevelConnected.lean` (unchanged source copied from commit `6c2cc8c`) converts unique local maxima to connected strict superlevels of the SAME actual height on the compact locally connected native torus. Its inclusion is an existing root dependency, not a worker-owned replacement.
9. `HeightTightnessSphereDirections`: compact uniform perturbation with a raised threshold extends connected strict superlevels to every sphere direction; Riesz duality and exact image equality yield `IsTightImage X` for every open halfspace. The zero functional uses connectedness of the actual source.
10. `ClassicalPositiveGaussTightnessProof`: closes the exact unchanged claim; existing native plane atlas supplies local connectedness without altering the native differential model.

The unused generic ambient-direction draft was removed; only checked final-closure source remains. Integration must rebuild this source in its own checkout before awarding integrated final-pair credit. This worker does not claim the final pair itself.
