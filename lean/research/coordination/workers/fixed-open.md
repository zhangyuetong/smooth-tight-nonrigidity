# Fixed-open worker — complete

Checked checkout: `C:/Users/gzhan/Documents/ChatGPT/tight_another_review/ver503-fixed-open`.
Branch: `codex/ver503-fixed-open`; base: `7483524`.
Frozen production-source commit: `eca1ae5507108b087bf708bc6523c7b8facc1a2d`.
Validation completed: `2026-10-09T19:17:54.897760+00:00`.

## Exact achieved theorem

```lean
TightVer401.classicalCoincidentEmbeddingFixedOpen_proved :
  TightVer401.ClassicalCoincidentEmbeddingFixedOpenClaim
```

This is the EXACT closed statement in `ClassicalExternal.lean`: actual native infinity-smooth embeddings X,Y of the connected compact torus, pointwise equal actual native induced forms, equal entire images, and agreement on a nonempty open U imply X=Y. No background parameter, new grant, custom axiom, admission, or replacement construction assumption remains in this theorem.

Final-proof consumer: root's canonical `exists_noncongruent_isometric_tight_tori_pair_of_classical`, replacing ONLY the existing `ClassicalExternalResults.coincidentEmbeddingFixedOpen` statement. Root owns all canonical imports, registry/coverage/theorem assembly and the final full integration audit. Worker changes no original construction source, paper, pin, existing contract or shared declaration.

## SAME-object proof chain

1. `classicalEmbeddedImageReparametrization_proved` provides ONE actual smooth homeomorphism e and its smooth inverse, with literal Y(e p)=X p.
2. `ClassicalCoincidentEmbeddingDifferential.lean` differentiates that SAME identity and applies the given equality of actual induced forms. The forward differential preserves tangent ENorm in the actual induced RiemannianBundle of SAME Y. Y injectivity and the SAME open agreement imply e fixes U.
3. `NativeEmbeddingMetricIsometryDistance.lean` proves the general C1-path integral and intrinsic-infimum preservation theorem `riemannianEDist_homeomorph_eq_of_tangent_enorm`. It derives inverse norm preservation through the actual differentiated inverse identity, with explicit base-point norm-instance transport.
4. Native/Plane intrinsic-distance transport uses SAME Y throughout. `nativeProductPlaneImmersionMetric Y hY.1 hY.2.1` constructs the genuine smooth positive Plane metric. `NativeEmbeddingMetricIsometrySpace.lean` constructs its finite intrinsic MetricSpace from the actual C1-path infimum on a connected source, retaining the original topology definitionally. Local MetricSpace, EMetricSpace, PseudoMetricSpace and PseudoEMetricSpace are explicitly selected to avoid the existing product-distance instances.
5. This actual intrinsic distance makes SAME e an Isometry. The pinned OpenAI-backed `isometry_eq_id_of_fixed_open_compact` at n=2 gives e=id, so Y∘e=X gives X=Y.

No chordal/product distance is identified with the induced intrinsic distance. The general metric and distance leaves are useful upstream candidates; publication is left to root.

## Frozen new files and exact consumers

- `ClassicalCoincidentEmbeddingFixedOpenProof.lean`: exact closed theorem above; canonical first-pair/background-reduction consumer.
- `ClassicalCoincidentEmbeddingDifferential.lean`: `classicalCoincident_plane_contMDiff`, `classicalCoincident_native_mfderiv`, `classicalCoincident_native_inducedForm`, `classicalCoincident_native_enorm`, `classicalCoincident_reparam_fixedOn`; consumed by the exact final proof with SAME X,Y,e,U.
- `NativeEmbeddingMetricIsometryDistance.lean`: actual path-infimum monotonicity, base-point tangent ENorm transport, inverse norm preservation, and `riemannianEDist_homeomorph_eq_of_tangent_enorm`; consumed with SAME Y-induced native bundle and SAME e.
- `NativeEmbeddingMetricIsometrySpace.lean`: connected finite edist, `connectedRiemannianMetricSpace`, original-topology and actual-riemannianEDist identities, and IsRiemannianManifold compatibility; consumed with SAME Y-induced Plane bundle.
- `ClassicalCoincidentEmbeddingFixedOpenAudit.lean`: worker-local exact-type example and axiom prints. Exclude this worker audit from canonical imports.

All three source-only subagents wrote exclusive new leaves; parent was the sole compiler writer. No peer chat messaging or push.

## Current-source validation

`python scripts/build.py --module TightVer401.ClassicalCoincidentEmbeddingFixedOpenAudit --jobs 1` passed under the dot-sourced `scripts/worktree-environment.ps1`.

Exact final proof compiled: 57.374 s. Worker audit compiled: 49.756 s. The whole imported source closure (155 pinned/local modules) was independently checked against the build report for source and compatibility-source hashes, compiled object hashes, dependency hashes and compiler log hashes. Code-only scanning found no sorry/admit/axiom/unsafe/implemented_by tokens. The exact closed theorem's transitive axioms are ONLY `[propext, Classical.choice, Quot.sound]`; the generic distance theorem and metric compatibility theorem have the same allowed set.

Source-closure SHA256: `a0bf82245ac76c4493fcf888a2fccd2441996b8d6269196ba242cf45eff307c7`.
Worker-audit log SHA256: `2370ed78ef324be09fc54a69b510be0ec41f0c03bb14321be3651fda0c9e586b`.
Worker build-report SHA256: `d77c48f9edccf2776aa81067bed4e345fd4d88f974bca6726e3333883156b677`.

Private build report: `lean/build-logs/TightVer401.ClassicalCoincidentEmbeddingFixedOpenAudit.build.json`.
Private compiler audit: `lean/build-logs/TightVer401.ClassicalCoincidentEmbeddingFixedOpenAudit.log`.
These are generated evidence and are not committed. Copied cache outputs were only private seeds; current-source/hash-checked compilation and this exact audit establish proof credit.

Paper/paper.tex, target-lock.json, upstream-lock.json, schoenflies-lock.json, lean-toolchain and lakefile.toml match the base checkpoint unchanged. No canonical full-audit/coverage update was performed by this worker; root must validate its integrated current sources and new reduced theorem header.

## Checked source SHA256

- `ClassicalCoincidentEmbeddingDifferential.lean`: `3e97056fd354fb8b8f96bd2d302ba44e818057cfd6314062703aae9c1410e2a0`.
- `ClassicalCoincidentEmbeddingFixedOpenAudit.lean`: `2cc38d6fff832490ae217389668577f79de4c5e726a1e76a9e18d05660e7f00c`.
- `ClassicalCoincidentEmbeddingFixedOpenProof.lean`: `b6b88def11837a1398c8d9220070be91b4813cba45a2ad2c64f695fad0f09efa`.
- `NativeEmbeddingMetricIsometryDistance.lean`: `3b01559b710ffcfe059512ec3dcc8e6cd64898ca857390bb0bdbdba0a66825bc`.
- `NativeEmbeddingMetricIsometrySpace.lean`: `858d18f18bc37fa9cf9ba1a5c62fd155c0de86bdcf72f120d1bfebab4786b1cd`.

## Continuation

Assigned proof achieved; no remaining worker proof obligation or blocker. Root can integrate the frozen production leaves, import the final proof, supply the exact closed fixed-open term internally, reduce its canonical ultimate theorem to only the positive-Gauss statement, and run its full current-source audit. The worker-local audit is optional separate evidence and must not be added to canonical imports. Full-paper, noncompact/boundary fixed-open generalizations, and extension/Cantor scope receive no new completion claim.
