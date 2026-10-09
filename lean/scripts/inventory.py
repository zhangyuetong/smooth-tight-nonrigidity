"""Keep proof coverage tied to the exact active manuscript and reviewed handoff."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = json.loads((ROOT / "target-lock.json").read_text(encoding="utf-8-sig"))
SOURCE = ROOT.parent / TARGET["manuscript"]

def main():
    data = SOURCE.read_bytes()
    lock = json.loads((ROOT / "target-lock.json").read_text(encoding="utf-8-sig"))
    if hashlib.sha256(data).hexdigest() != lock["sha256"]:
        raise SystemExit("Manuscript changed: review and repin the active target before updating coverage.")
    text = data.decode("utf-8-sig")
    claims = []
    pattern = r"\\begin\{(theorem|proposition|lemma|corollary)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}"
    for match in re.finditer(pattern, text, re.S):
        line = text[:match.start()].count("\n") + 1
        labels = re.findall(r"\\label\{([^}]+)\}", match[3])
        claims.append({"environment": match[1], "title": match[2] or "",
                       "labels": labels, "source_line": line, "statement_tex": match[0],
                       "status": "pending", "proved_declarations": [], "scope_notes": []})
    for row in claims:
        if "thm:branch" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = ["TightVer401.Manifold.finite_sign_metric", "TightVer401.finite_sign_metric",
                                          "TightVer401.Manifold.infinite_sign_metric"]
            row["scope_notes"] = ["Finite and countable formulas on an actual charted surface into three-space with pairwise disjoint topological supports.",
                                  "Smooth convergence is explicit locally uniform convergence of values and every actual coordinate jet on extended chart targets. The chart bridge derives convergence of actual manifold differentials; no derivative-limit conclusion is assumed.",
                                  "This metric identity does not assert embedding, tightness, image noncongruence or existence of the bending inputs."]
        if "thm:ruled" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.ruled_supported_kernel",
                "TightVer401.ruled_band_supported_bending_iff_period_zero",
                "TightVer401.ruled_band_supported_kernel_classification_any_primitive",
                "TightVer401.ruled_band_profile_supported",
                "TightVer401.periodic_ruled_cutoff",
                "TightVer401.compact_band_support_uniform_bounds",
                "TightVer401.bandCoordinateLift_contDiff",
                "TightVer401.bandCoordinateLift_zero_strain",
                "TightVer401.supported_ruled_vector_period_zero",
                "TightVer401.supported_ruled_vector_has_profile",
                "TightVer401.periodic_bandProfile_injective"]
            row["scope_notes"] = [
                "Full necessity, sufficiency and unique displayed profile classification on the actual period quotient circle times the open one-sided band, for every positive band width.",
                "Inputs are only smooth periodic curve/frame functions, orthonormality, the manuscript frame derivative equations and nowhere-zero torsion. The actual manifold differential defines zero strain; no bending, support, transport or classification conclusion is assumed.",
                "Arbitrary compactly supported quotient bendings lift and extend smoothly by zero; compactness derives strict uniform transverse bounds and the actual uu strain eliminates the transverse component. The remaining actual strain implies transport, the period obstruction and reconstruction.",
                "The actual OpenAI integral produces a periodic primitive from the zero period. The cutoff is an attained maximum. Classification holds for every periodic primitive, including its arbitrary additive constant, and admits exactly smooth compact profiles with topological support strictly above that cutoff.",
                "This conditional local theorem does not construct a global closed curve/frame satisfying the hypotheses or a tight surface completion; those remain separate manuscript targets."]
        if "prop:support" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.sphere_gauss_decomposition",
                "TightVer401.sphereSupportMap_differential",
                "TightVer401.sphereSupportMap_differential_injective",
                "TightVer401.sphereSupportMap_isUnitNormal",
                "TightVer401.sphereSupportMap_inducedMetric",
                "TightVer401.sphereSupportMap_secondFundamental",
                "TightVer401.sphereSupportMap_curvature",
                "TightVer401.sphereSupportMap_converse_local",
                "TightVer401.sphereTangentFrame_onto",
                "TightVer401.sphereHemisphere_metric",
                "TightVer401.sphereHemisphereChart_covers",
                "TightVer401.sphereSupportMap_coordinate_change",
                "TightVer401.globalSphereSupport_chart",
                "TightVer401.globalSphereSupport_contMDiff",
                "TightVer401.globalSphereSupport_chartOn",
                "TightVer401.globalSphereSupport_on_hemisphereOn",
                "TightVer401.globalSphereSupport_contMDiffOn",
                "TightVer401.globalSphereSupport_chart_geometryOn",
                "TightVer401.globalSphereSupport_manifold_geometryOn",
                "TightVer401.sphereSupportMap_curvature_at",
                "TightVer401.gaussManifold_exists_smooth_local_inverse",
                "TightVer401.gaussManifold_image_isOpen",
                "TightVer401.gaussImage_inverse",
                "TightVer401.gaussImage_support_exists",
                "TightVer401.gaussMap_differential_injective",
                "TightVer401.gaussMap_exists_smooth_inverse_coordinates",
                "TightVer401.gaussSupport_reconstruction_local"]
            row["scope_notes"] = [
                "The actual unit-sphere constraint gives tangent orthogonality and the second form minus the round metric. OpenAI's proved Gauss decomposition supplies the actual spherical connection.",
                "The gradient is defined from the inverse round metric and actual coordinate derivatives of H. Its smoothness and gradient pairings are proved. Differentiating those pairings proves the support-map differential is the actual covariant Hessian plus H times the identity.",
                "A nonzero determinant proves the support-map differential injective, with actual normal Q, induced metric B g-inverse B-transpose, second form minus B, and intrinsic curvature the reciprocal determinant of the actual raised-index endomorphism, via OpenAI's Gauss equation.",
                "An arbitrary smooth map whose actual normal is Q reconstructs from H = inner(X,Q) on each sphere coordinate domain. Actual orthonormal tangent frames and OpenAI hemisphere charts cover the genuine two-sphere; their metrics are derived from their proved injective differentials.",
                "The actual chain rule proves coordinate invariance of the spherical gradient and support map. Centered OpenAI charts define a support map smooth on every arbitrary open sphere domain where the height is smooth, with the same local formulas and no extension hypothesis outside that domain.",
                "The actual global support map has all the differential and fundamental-form formulas in every open-domain hemisphere chart. Curvature at an invertible point follows by shrinking to its derived open nonzero-determinant neighborhood; invertibility of the whole original domain is not assumed.",
                "For every smooth boundaryless surface with the coordinate-plane model, the actual manifold derivative and ordinary inverse function theorem derive local Gauss inverses. Their target neighborhoods prove the Gauss image open; injectivity joins the local inverses into a smooth inverse with both inverse identities.",
                "The actual manifold chain rule and normal equation derive a smooth height on the full Gauss image and the representation of the original immersion there. The existence statement also includes the empty-source case. No inverse, open-image or reconstruction package is assumed."]
        if "lem:fixed-open" in row["labels"]:
            row["status"] = "partial"
            row["proved_declarations"] = ["TightVer401.isometry_eq_id_of_fixed_open_compact"]
            row["scope_notes"] = ["Compact connected boundaryless case with an actual smooth Riemannian metric inducing distance, using OpenAI minimizing geodesics and intrinsic uniqueness.",
                "The general noncompact and boundary cases, and automatic smoothness of a distance isometry, remain pending."]
        if "prop:general-ruled-return" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.general_ruled_return",
                "TightVer401.generalRuledDelta_eq_det",
                "TightVer401.general_ruled_actual_riccati",
                "TightVer401.general_ruled_gaussianCurvature",
                "TightVer401.general_ruled_flow_over_period",
                "TightVer401.general_ruled_return_of_asymptotic_curve",
                "TightVer401.riccati_solutions_unique",
                "TightVer401.general_ruled_return_identity_iff"]
            row["scope_notes"] = [
                "The ordinary smooth periodic curve and ruling functions determine actual derivatives, cross-product normal, triple determinant, fundamental forms and curvature. The nonzero determinant proves the actual immersion and negative curvature.",
                "The central-leaf asymptotic condition is stated using the actual OpenAI second fundamental form. It eliminates the constant coefficient of the actual quadratic characteristic equation; both remaining coefficients are defined from the actual curve derivatives and proved smooth and periodic.",
                "The actual OpenAI primitives construct the flow through zero over a whole circuit. An integrating factor from the same primitive proves uniqueness for arbitrary actual solutions on that compact interval. Every smooth asymptotic graph with sufficiently small initial value has the displayed projective return.",
                "The first and second derivatives of the actual return are checked, and identity of its germ is equivalent both to the two projective parameters and to the manuscript two-jet criterion."]
        if "lem:finite-moment-balance" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.finite_moment_period_prescription",
                "TightVer401.finite_moment_period_prescription_smooth_circle"]
            row["scope_notes"] = [
                "Actual native smooth maps on AddCircle L for every positive L, every ambient dimension m and every real target nonlinear period.",
                "The construction gives a smooth strictly positive speed, exact actual vector moments, an arbitrarily small actual L1 change and the requested actual integral of g/sqrt(a).",
                "At most d+1 projected intervals cover the correction support, where d is the dimension of the actual full-circle moment span; their total lengths can be arbitrarily small. Includes dimension zero.",
                "Independent localized controls, their actual continuous linear coordinate inverse, quantitative coefficient smallness, positivity, period divergence and attainment are derived. No correction or period conclusion is assumed."]
        if "thm:normal-loop-criterion" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.normalLoop_existence_criterion",
                "TightVer401.normalLoop_existence_criterion_arbitrarily_close",
                "TightVer401.normalLoop_prescribed_identity_band_criterion",
                "TightVer401.periodicRuledFrame_identity_flow_inside_band"]
            row["scope_notes"] = [
                "For every actual smooth positive-period spherical unit-speed loop, ordinary ambient convex interior, actual smooth positive closing speed and actual smooth positive closed balanced speed are equivalent.",
                "The forward convex direction constructs a speed from actual attainable smooth nonnegative moments; the converse derives full affine span and actual halfspace separation. Nonconstant curvature and both signs of its derivative are derived from positive closure.",
                "Every smooth positive closing speed admits balanced speeds arbitrarily close in actual L1. Actual global arclength inversion constructs the prescribed curve, orthonormal frame, curvature and torsion with zero actual physical return period.",
                "The prescribed immersed circle-band equivalence is proved with native smoothness and manifold differential injectivity, actual coordinate induced metric and negative intrinsic curvature, and the actual constructed asymptotic ODE and identity endpoint. Small positive trajectories stay inside every prescribed positive band width throughout the whole period.",
                "The geometric converse derives moment closure from actual frame periodicity and arclength shift. No final closure, period, curvature or identity-return package is assumed. Embedding is a separate later claim."]
        if "prop:one-slowdown" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = ["TightVer401.one_slowdown_holonomy_correction"]
            row["scope_notes"] = [
                "For every positive cell period, positive smooth periodic baseline speed with actual scalar closing moment zero, smooth nonzero scalar tangent component and smooth periodic nonconstant curvature, every positive L1 tolerance and support-length tolerance admit the stated actual corrected speed.",
                "The actual scalar closing moment remains zero, the actual integral of curvature derivative divided by square-root speed is zero, and actual L1 change is below the requested tolerance.",
                "The native smooth circle speed equals the representative speed. The scalar moment span has dimension at most one, so the actual change support is covered by at most two projected intervals with arbitrarily small total length.",
                "Both signs of the actual curvature derivative and the support count are derived. This proposition does not assert the seed's visibility or the balanced speed's global embedding; those belong to the separate balanced embedded-speed theorem."]
        if "cor:relative-holonomy-upgrade" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = ["TightVer401.normalLoop_relative_holonomy_upgrade"]
            row["scope_notes"] = [
                "For each positive closing speed with actual embedded primitive, constructs the same positive balanced speed and a jointly smooth native circle family joining it to the baseline, with arbitrary L1 and uniform positional smallness.",
                "Every intermediate actual closed curve is smoothly embedded with injective actual manifold differential. Its actual derivative is a positive multiple of the fixed tangent, and the actual prescribed unit spherical normal remains orthogonal at each parameter.",
                "Every specified continuous linear projection with regular tangent and actually embedded baseline projection retains its native smooth embedding and differential injectivity along the same family. The identity projection supplies the case with no separately specified projection.",
                "The actual global arclength inverse and same-speed periodic physical frame yield the negative-curvature identity-return band and an actual thin band embedding. Actual embeddedness of the spherical normal curve derives injectivity of its actual Gauss map on a thin neighborhood."]
        if "lem:seed" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.corrugated_analytic_seed",
                "TightVer401.corrugatedSeed_origin_inside",
                "TightVer401.corrugatedSeed_positive_argument_turns",
                "TightVer401.corrugatedRoot_exists_unique_nat",
                "TightVer401.corrugatedSeedBeta_cell",
                "TightVer401.corrugatedSeedPartner_cell",
                "TightVer401.corrugatedSeedPartner_deriv",
                "TightVer401.corrugatedSeedMultiplier_pos",
                "TightVer401.corrugatedSeedBeta_periodic",
                "TightVer401.corrugatedSeedPartner_periodic",
                "TightVer401.corrugatedSeedBeta_injOn",
                "TightVer401.corrugatedSeedPartner_action",
                "TightVer401.corrugatedSeedBeta_contDiff_analytic",
                "TightVer401.corrugatedSeedPartner_contDiff_analytic",
                "TightVer401.corrugatedSeedBeta_isJordanCurve",
                "TightVer401.corrugatedSeedBeta_native_embedding",
                "TightVer401.corrugatedSeed_outer_visible",
                "TightVer401.corrugatedSeed_reflected_visible",
                "TightVer401.corrugatedSeed_visible_closed_pairs",
                "TightVer401.corrugatedSeedPartner_injOn",
                "TightVer401.corrugatedSeedPartner_native_embedding",
                "TightVer401.corrugatedSeedPartner_isJordanCurve",
                "TightVer401.corrugatedSeedPartner_separates",
                "TightVer401.corrugatedSeedSphere_native_embedding",
                "TightVer401.corrugatedSeedSphere_north",
                "TightVer401.corrugatedSeedSphere_curvature_positive",
                "TightVer401.corrugatedSeedSphere_curvature_negative",
                "TightVer401.corrugatedSeedSphere_exists_arclength"]
            row["scope_notes"] = [
                "The exact complex beta and partner delta are constructed using the actual scalar root and pinned OpenAI integral primitive. Their actual smoothness, regular derivatives, full period, rotational covariance and positive tangent multiplier are checked.",
                "The first curve is injective on the fundamental half-open period interval. The actual mixed determinant integral vanishes on a cell and the full period, by the actual root equation.",
                "Both actual curves are real analytic; analyticity of the constructed partner is derived from a genuine holomorphic primitive and actual derivative uniqueness.",
                "The first curve has an actual native smooth embedding and genuine Jordan range. Both strict derivative visibility pairs at radii 1/4 and 4/5, including the explicitly reflected reversed pair, follow from actual checked quantitative position, tangent and direction estimates.",
                "The partner is also injective on the fundamental interval and induces an actual native smooth embedding and genuine separating Jordan range. This is derived from the constructed visibility angle, its positive actual derivative, exact one-turn shift and exponential identity.",
                "The actual gnomonic spherical lift has a native smooth sphere-circle embedding and lies in the northern hemisphere. Its actual geodesic curvature has both signs; a constructed global inverse arclength map also gives a unit-speed curve whose existing normalLoopCurvature has both signs.",
                "Both actual Jordan curves enclose the origin, proved via a Schoenflies disk and uniqueness of actual circle covering lifts. Each actual normalized position has a continuous real argument of exact increment +2π, giving positive orientation about the proved interior origin. The whole seed package is constructed with no geometric conclusion assumed. The appendix's sharper 60/N estimate remains separate; the checked 100/N bound suffices for this numbered lemma."]
        if "thm:spike" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = ["TightVer401.corrugatedSeed_exists_balanced_embedded_speed"]
            row["scope_notes"] = [
                "For every actual seed N at least 10000 and every positive L1 tolerance, constructs its own actual inverse spherical arclength map and a positive smooth cell-periodic speed arbitrarily close to the exact initial speed.",
                "The actual cell scalar moment, full spatial moment, cell nonlinear balance and full nonlinear balance all vanish. Both actual outer and reflected strict visible pairs hold for the same constructed corrected partner.",
                "The actual translated spatial primitive and its exact actual horizontal projection admit smooth native circle embeddings with injective manifold differentials. The same speed is retained throughout, and its correction is supported on at most two native cell arcs of arbitrarily small total length.",
                "Band construction and later global surface attachment are separate claims; this theorem discharges the exact balanced embedded speed statement."]
        if "lem:cap" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = [
                "TightVer401.radialCap_contDiffOn",
                "TightVer401.radialCap_matches_first_jet",
                "TightVer401.radialCap_strict_derivative_signs",
                "TightVer401.radialCap_endpoint_derivatives",
                "TightVer401.exists_radialCap_small_width",
                "TightVer401.exists_concave_first_jet_join",
                "TightVer401.exists_finite_radial_cap",
                "TightVer401.exists_finite_radial_cap_surface"]
            row["scope_notes"] = [
                "The actual square-root cap's smoothness, actual first and second derivatives, incoming first-jet match, strict derivative signs before the endpoint, endpoint derivatives and sufficiently-small-width bound are checked.",
                "For arbitrary incoming local smooth representatives, every sufficiently small positive width admits actual radial smoothing preserving an open incoming collar and the exact terminal cap germ, with strict concavity throughout, positive first derivative before the endpoint and the stated endpoint derivatives.",
                "The general relative join constructs actual positive acceleration, corrects both actual moments with internally constructed controls, integrates twice and proves both outer germs before pasting. No final smoothing or geometry package is assumed.",
                "The actual radial Hessian determinant and induced intrinsic Gaussian curvature are also proved negative on the punctured capped interior."]
        if TARGET["target"] in {"ver500", "ver503"} and "lem:neck-adapter" in row["labels"]:
            row["status"] = "proved"
            row["proof_origin"] = "new_ver500_construction"
            row["proved_declarations"] = [
                "TightVer401.dualRadialNeck_actual_first_jet",
                "TightVer401.dualRadialNeck_contDiffOn",
                "TightVer401.dualRadialNeck_strict_derivative_signs",
                "TightVer401.exists_dualRadialNeck_gradient_adapter",
                "TightVer401.radialPlanarGradient_norm_eq_abs_deriv"]
            row["scope_notes"] = [
                "For every actual smooth incoming representative near j with positive first derivative and negative actual second derivative, and every 0<a<j, the exact manuscript B,C give a square-root neck matching the incoming value and derivative at j.",
                "Constructs an actual smooth F on (a,b), b>j, with strict positive first derivative and negative second derivative throughout, exact terminal square-root germ on (a,c), and the exact incoming representative on a retained open collar (d,b) contained in its original domain.",
                "Positive slope is derived from strict concavity and the retained positive right derivative. The actual radial Hessian determinant, support differential injectivity and intrinsic Gaussian curvature are checked.",
                "The Euclidean norm of the actual planar gradient equals the positive radial derivative on every ray and tends to infinity as r decreases to a. This is the Euclidean L2 norm, not the max norm on the coordinate representation.",
                "The inverse Legendre formula is a separately proved refinement. Global gradient injectivity, the full two-sided completion and torus gluing remain separate pending claims."]
        if TARGET["target"] in {"ver500", "ver503"} and "prop:central-support" in row["labels"]:
            row["status"] = "proved"
            row["proof_origin"] = "new_ver500_construction"
            row["proved_declarations"] = [
                "TightVer401.identityBand_central_support_tensor",
                "TightVer401.identityBand_central_cartesian_tensor",
                "TightVer401.identityBand_central_cartesian_positive_transverse"]
            row["scope_notes"] = [
                "Constructs one corrected seed frame, actual two-sided Gauss-coordinate potential and final protected subband; its genuine supported bending is selected after the final width.",
                "For that same potential the actual central Hessian pairing in the scaled Gauss-coordinate tangent basis is exactly [[0,a],[a,0]], with a positive. Actual support reconstruction and normal correspondence give the spherical support-tensor interpretation.",
                "Positive noncharacteristic transverse directions and the actual signed tangential formula are derived. Positive exit perturbations, visible connectors and global torus completion remain separate pending constructions."]
        if TARGET["target"] in {"ver500", "ver503"} and "lem:smoothing" in row["labels"]:
            row["status"] = "proved"
            row["proof_origin"] = "new_ver500_construction"
            row["proved_declarations"] = [
                "TightVer401.exists_relative_saddle_smoothing",
                "TightVer401.exists_relative_saddle_smoothing_on_sides",
                "TightVer401.exists_relative_saddle_smoothing_in_collar",
                "TightVer401.relativeSaddleSeam_shared_entries",
                "TightVer401.relativeSaddleProfile_error_bounds",
                "TightVer401.relativeSaddle_correctedHessian_error"]
            row["scope_notes"] = [
                "Actual smooth regular periodic parametrization of a compact embedded closed seam; actual planar potentials smooth on open branch domains containing the seam, with matching values and actual gradients and negative Cartesian Hessian determinants.",
                "Constructs an actual smooth saddle interpolation retaining both outer branch germs outside any prescribed open seam neighborhood and arbitrarily small uniform value and actual Cartesian-gradient errors. Separate branch domains are allowed; no smoothing witness or exterior regularity package is assumed.",
                "For a supplied whole-domain piecewise exterior, ordinary side/frontier and local normal-side data describe the old geometry. The standalone collar theorem constructs the regular tube, canonical sides and piecewise potential directly from seam geometry, deriving determinant negativity on a neighborhood from the seam values.",
                "The common tangential and mixed Hessian entries are derived from actual gradient agreement. The retained normal-profile/Taylor construction, compact determinant control, cutoff error estimates and curved-coordinate connection corrections are now included in the active audited closure.",
                "Positive common tangential Hessian is a sufficient input retained in the manuscript interface; the proved matching-jet construction is stronger. Bare closed-side data without a common ambient smooth extension and compatible actual jets are not supplied by this interface. Global gradient injectivity and connector-specific branch construction remain separate pending obligations."]
        if "lem:complete-profile" in row["labels"]:
            row["status"] = "proved"
            row["proved_declarations"] = ["TightVer401.exists_completeProfile"]
            row["scope_notes"] = [
                "For an arbitrary profile smooth near H with positive value, actual first derivative and actual second derivative, every beta>0 admits an actual globally smooth extension.",
                "The extension agrees on a whole neighborhood of H, is positive with positive first and second derivatives throughout [H,infinity), has second derivative beta eventually and first derivative tending to infinity.",
                "The positive global acceleration is constructed using a localized smooth cutoff; two actual pinned OpenAI primitives yield the profile and full-germ equality by the fundamental theorem of calculus.",
                "This profile lemma does not assert the complete cylinder's global embedding, completeness, Gauss-map bijectivity or curvature integral."]
        if "prop:budget" in row["labels"]:
            row["status"] = "partial"
            row["proved_declarations"] = ["TightVer401.curvature_unchanged_off_support"]
            row["scope_notes"] = ["Intrinsic curvature is unchanged off the bending support, via equality of actual map and metric germs.",
                                  "Actual compact-region and supported periodic band negativity preservation is checked; actual small band perturbation embeddings are checked; torus stability, area integrals, Gauss鈥揃onnet and tightness are pending."]
        if "thm:localized-sign" in row["labels"]:
            row["status"] = "partial"
            row["proved_declarations"] = ["TightVer401.Manifold.infinite_sign_metric",
                                          "TightVer401.signedSeries_coefficients_injective"]
            row["scope_notes"] = ["The common metric for an actually smoothly convergent sign series, and injectivity of parametrized maps with nonzero disjoint modes and nonzero amplitudes.",
                                  "Uniform smooth small-series construction, embedding and tightness neighborhoods, image noncongruence, and quotient topology remain pending."]
    # New producer claims are bound to exact current ver500 statements, never inherited by label.
    for row in claims:
        if "lem:degree" in row["labels"]:
            row.update(status="proved", proof_origin="new_ver500_construction",
                proved_declarations=["TightVer401.annular_degree_global_diffeomorphism",
                    "TightVer401.annular_degree_planarGradient_global_diffeomorphism"],
                scope_notes=["Actual smooth map near an explicit compact nested Jordan annulus; constant nonzero interior Jacobian sign, actual boundary homeomorphisms and ordinary one-point winding tests, either boundary assignment and possible boundary rank degeneration. Signed counts, exact image, injectivity, smooth interior inverse and closure homeomorphism are derived.",
                    "The gradient specialization identifies the same actual planarGradient with the actual planarHessian determinant. Filling/connector/completion callers must supply their own geometric hypotheses."])
        if "lem:quadratic-filling" in row["labels"]:
            row.update(status="proved", proof_origin="new_ver500_construction",
                proved_declarations=["TightVer401.exists_quadratic_radial_filling",
                    "TightVer401.exists_quadratic_radial_filling_global_gradient",
                    "TightVer401.exists_quadratic_radial_filling_global_gradient_with_overlap",
                    "TightVer401.exists_quadratic_radial_filling_global_gradient_with_retained_trace"],
                scope_notes=["Constructs an actual smooth saddle filling from an incoming exterior scalar germ with positive radial and tangential trace pairings. The arbitrarily large quadratic coefficient, unchanged full exterior germ and actual quadratic inner germ are constructed, without an assumed filling or inverse package.",
                    "Under the manuscript's actual positively oriented Jordan gradient-trace hypothesis, the real signed annular degree theorem yields the exact punctured-disk gradient image, global injectivity and smooth inverse; boundary rank degeneration is allowed.",
                    "The stronger retained-trace consumer retains ONE S/M/H/e and the original GammaS excluded inverse hole, then constructs a distinct Gamma0 at R<S0<S with a true open unchanged-potential/inverse collar inside the same e.source. This does not construct an incoming visible connector or the two-ended completion."])
        if "lem:convex" in row["labels"]:
            row.update(status="proved", proof_origin="new_ver500_construction",
                proved_declarations=["TightVer401.exists_parabolic_convex_closure"],
                scope_notes=["From only RN, mu, h>0 constructs one same-meridian convex body and smooth embedded closed lateral annulus, actual strictly positive interior curvature, exact parabolic endpoint germs, outward twice-punctured-sphere Gauss diffeomorphism, exterior-cylinder/height separation and actual lateral-image asymmetry.",
                    "Includes actual registered interval-halfspace boundary smoothness/rank and body frontier/outward-support statements; no completed saddle, torus, marking, tightness or final pair is granted."])
    # Reuse requires an exact reviewed current statement hash, not just matching labels.
    review = json.loads((ROOT / "target/ver503-reuse-review.json").read_text(encoding="utf-8"))
    assert review["target"] == TARGET["target"] and review["manuscript_sha256"] == lock["sha256"]
    assert (ROOT / "target/manuscript.tex").read_bytes() == data
    reviewed = {r["label"]: r for r in review["claims"]}
    assert len(reviewed) == len(claims)
    for row in claims:
        entry = reviewed[row["labels"][0]]
        current_hash = hashlib.sha256(row["statement_tex"].replace("\r\n", "\n").encode("utf-8")).hexdigest()
        assert current_hash == entry["statement_sha256"], row["labels"]
        assert entry["status"] == row["status"], row["labels"]
        row["proof_reuse_review"] = entry["review"]
        row["statement_sha256"] = current_hash
        row["migration_review"] = "target/ver503-reuse-review.json"
    coverage = {"manuscript": str(Path(TARGET["manuscript"])),
                "manuscript_sha256": hashlib.sha256(data).hexdigest(),
                "paper_completion": "INCOMPLETE", "target": TARGET["target"],
                "primary_objective": {"statement": TARGET["objective"], "status": "pending",
                    "lean_target": "TightVer401.exists_noncongruent_isometric_tight_tori_pair",
                    "scope": "First assertion of thm:main-fiber only; the Cantor-family clause is deferred.",
                    "conditional_lean_target": "TightVer401.exists_noncongruent_isometric_tight_tori_pair_of_classical",
                    "accepted_background": "TightVer401.ClassicalExternalResults", "additional_explicit_background": ["TightVer401.ClassicalEmbeddedImageReparametrizationClaim", "TightVer401.MarkerEllipseAxesRecognition"]},
                "deferred_scope": TARGET["deferred"], "claims": claims,
                "classical_external_policy": {"mode": "explicit_named_theorem_parameters", "authorization_date": "2026-10-09", "registry": "classical-external-results.json", "registry_sha256": hashlib.sha256((ROOT / "classical-external-results.json").read_bytes()).hexdigest(), "conditional_final_pair_status": "pending", "external_results_are_not_proved_claims": True},
                "additional_checked_scope": {
                    "actual-connector-same-potential-inner-outer-completion-branch-assembly": ["TightVer401.exists_dualRadialCompletion_branches_assembly", "TightVer401.exists_dualRadialCompletionConnectorInputs", "TightVer401.exists_dualRadialCompletion_filling_inputs"],
                    "actual-round-boundary-degree-from-proved-gradient-degree": ["TightVer401.dualRadialCompletionCircularDegree_of_gradientClaim"],
                    "actual-uniform-complete-flow-visibility-before-protected-field-selection": ["TightVer401.positiveExit_exists_visible_complete_flow_initial_margin", "TightVer401.positiveExitRawVisibility_exists_strip"],
                    "actual-completed-saddle-full-scalar-tuple-and-once-chosen-meridian-connection": ["TightVer401.completedSaddleTorusActualGraphData_of_literal", "TightVer401.exists_completedSaddleTorusActualGraph_with_full_meridian"],
                    "actual-same-cylinder-supported-branch-gauss-and-conditional-tightness": ["TightVer401.nativeTorusImmersionNormal_eq_of_eventuallyEq", "TightVer401.protectedTorusActualCylinderBranchPositiveGaussData", "TightVer401.protectedTorusActualCylinderBranch_tight_of_classical", "TightVer401.protectedTorus_bending_positive_phase_germs", "TightVer401.protectedTorusActualCylinder_supported_branches_tight"],
                    "actual-same-cylinder-full-meridian-no-open-planar-patches": ["TightVer401.protectedTorusActualCylinder_curvature_ne_zero_off_seams", "TightVer401.protectedTorusActualCylinder_nonzero_curvature_dense", "TightVer401.protectedTorusActualCylinder_hasNoOpenPlanarPatch", "TightVer401.protectedTorusActualCylinder_bending_hasNoOpenPlanarPatch"],
                    "actual-same-cylinder-full-meridian-positive-gauss-and-entire-image": ["TightVer401.protectedTorusActualGraphCylinderData_of_ordinary", "TightVer401.protectedTorusActualCylinderPositiveGaussData", "TightVer401.protectedTorusActualCylinderPositiveGauss_tight_of_classical", "TightVer401.protectedTorusPositiveGauss_actualCylinder_region_eq_phase", "TightVer401.protectedTorusPositiveGauss_actualCylinder_positive_image"],
                    "actual-marked-contragredient-family-own-support-curvature-threshold": ["TightVer401.markedRuledBand_native_compact_curvature_threshold", "TightVer401.protectedTorus_marked_bending_curvature_threshold"],
                    "actual-full-quadratic-filling-and-retained-open-inverse-collar": ["TightVer401.exists_quadratic_radial_filling_global_gradient", "TightVer401.exists_quadratic_radial_filling_global_gradient_with_overlap", "TightVer401.exists_quadratic_radial_filling_global_gradient_with_retained_trace"],
                    "actual-native-torus-no-open-planar-patch-consumer": ["TightVer401.coord_curvature_zero_of_open_plane", "TightVer401.nativeTorusChartCurvature_zero_of_open_plane", "TightVer401.nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature", "TightVer401.nativeTorus_nonzero_curvature_dense_of_support_negative"],
                    "actual-native-torus-two-phase-seam-density": ["TightVer401.protectedTorusOffPhaseSeams_dense", "TightVer401.nativeTorus_nonzero_curvature_dense_of_off_seams"],
                    "actual-same-assembly-embedded-branches-and-entire-positive-image-stability": ["TightVer401.completedSaddleTorusBending_branch_stability", "TightVer401.exists_completedSaddleTorus_embedded_stable_branches"],
                    "actual-full-same-meridian-witness-for-torus-and-gauss": ["TightVer401.completedSaddleTorusAssemblyFromMeridian", "TightVer401.completedSaddleTorusAssemblyFromMeridian_embedding", "TightVer401.exists_completedSaddleTorusAssembly_with_full_meridian"],
                    "actual-completed-saddle-protected-torus-chart": ["TightVer401.completedSaddleTorusBandChart_source", "TightVer401.completedSaddleTorusBandChart_forward_smooth", "TightVer401.completedSaddleTorusBandChart_inverse_smooth", "TightVer401.completedSaddleTorusBandChart_placement", "TightVer401.completedSaddleTorusBandChart_exists_outside"],
                    "actual-native-torus-source-curvature-reparameterization": ["TightVer401.nativeTorusChartCurvature_comp_homeomorph"],
                    "actual-same-saddle-torus-supported-bending-and-metric-branches": ["TightVer401.exists_completedSaddleTorus_compact_nonzero_bending", "TightVer401.exists_completedSaddleTorus_metric_branching"],
                    "actual-local-band-torus-curvature-and-same-support-branch-threshold": ["TightVer401.nativeTorusChartCurvature_of_band_placement", "TightVer401.nativeTorusChartCurvature_of_band_placement_at_height", "TightVer401.protectedTorus_bending_branch_placement", "TightVer401.protectedTorus_ruled_bending_curvature_threshold"],
                    "conditional-marked-entire-image-noncongruence": ["TightVer401.nativeTorusSmoothEmbedding_affineIsometry", "TightVer401.nativeTorusPositiveImages_eq_of_ambient_congruence", "TightVer401.torusImageNoncongruent_of_positive_marker_and_ranges_ne", "TightVer401.torusImageNoncongruent_of_positive_marker_and_open_agreement"],
                    "same-saddle-one-meridian-actual-embedded-torus-connection": ["TightVer401.exists_protectedTorusAssembly_from_saddle"],
                    "literal-affine-protected-field-and-branch-connections": ["TightVer401.protectedTorusBendingField_linear_connection", "TightVer401.protectedTorusBendingField_linear_connection_fun", "TightVer401.protectedTorusBendingField_linear_connection_source", "TightVer401.protectedTorus_linear_branches_source"],
                    "actual-rigid-motion-curvature-and-entire-positive-image-connections": ["TightVer401.torusRigid_coord_fderiv", "TightVer401.torusRigid_coord_inducedMetric", "TightVer401.nativeTorusChartCurvature_affineIsometry", "TightVer401.nativeTorusPositiveRegion_affineIsometry", "TightVer401.nativeTorusPositiveImage_affineIsometry"],
                    "reviewed-actual-exit-neck-and-curvature-producer-connections": ["TightVer401.positiveExit_exists_two_actual_embedded_cartesian_patches", "TightVer401.visibleConnector_tangent_direction_properties", "TightVer401.exists_dualRadialCompletion_neck_filling_data", "TightVer401.dualRadialCompletionNeck_gradient_bijOn", "TightVer401.protectedTorus_curvature_reparam"],
                    "actual-cylinder-and-protected-geometry-from-ordinary-completion-data": ["TightVer401.completedSaddleAnnulusCylinderAssembly_height_pos", "TightVer401.exists_completedSaddleAnnulusCylinderInput", "TightVer401.completedSaddleAnnulusProtectedBand_from_data", "TightVer401.exists_completedSaddleAnnulusGeometryOutput"],
                    "same-protected-branch-actual-image-inequality-under-classical-rigidity": ["TightVer401.protectedTorus_bending_ranges_ne_of_classical"],
                    "generic-embedded-image-reparametrization-explicit-parameter": ["TightVer401.ClassicalEmbeddedImageReparametrizationClaim", "TightVer401.classicalEmbeddedImages_reparametrize"],
                    "same-protected-field-exact-torus-metric-and-positive-region-consumers": ["TightVer401.protectedTorus_isNativeBending", "TightVer401.protectedTorus_exact_sign_pair", "TightVer401.protectedTorus_bending_common_metric", "TightVer401.protectedTorus_bending_common_smooth_metric", "TightVer401.protectedTorus_bending_open_agreement", "TightVer401.protectedTorus_bending_sign_separation", "TightVer401.protectedTorus_metric_branching", "TightVer401.nativeTorusChartCurvature_eq_of_eventuallyEq", "TightVer401.protectedTorus_bending_branch_germs_off_support", "TightVer401.protectedTorus_bending_curvature_off_support", "TightVer401.protectedTorus_bending_positive_regions"],
                    "classical-external-interfaces-and-explicitly-conditional-wrappers": ["TightVer401.nativeTorusChartCurvature", "TightVer401.nativeTorusPositiveRegion", "TightVer401.NativeTorusSmoothEmbedding", "TightVer401.ClassicalPositiveGaussTightnessClaim", "TightVer401.ClassicalCoincidentEmbeddingFixedOpenClaim", "TightVer401.ClassicalExternalResults", "TightVer401.classicalPositiveGauss_tightness", "TightVer401.classicalCoincidentEmbeddings_eq", "TightVer401.NativeTorusPositiveGaussData", "TightVer401.nativeTorusPositiveGaussData_tight_of_classical"],
                    "actual-saddle-cylinder-to-native-torus-phase-connection": ["TightVer401.protectedTorusPhaseChart_properties", "TightVer401.protectedTorusPhaseChart_inverse_smooth", "TightVer401.protectedTorusPhaseChart_map_target"],
                    "actual-torus-seams-and-embedding-from-ordinary-producer-data": ["TightVer401.protectedTorusMap_contMDiff_and_immersion_from_data", "TightVer401.protectedTorusMap_contMDiff_and_immersion", "TightVer401.protectedTorusMap_injective", "TightVer401.protectedTorusMap_range", "TightVer401.protectedTorusMap_embedding_of_annulus_and_meridian"],
                    "conditional-full-filling-and-same-object-saddle-assembly": ["TightVer401.exists_quadratic_radial_filling_boundary_data_of_jordan_image", "TightVer401.quadraticRadialFilling_inner_subdisk_image", "TightVer401.quadraticRadialFilling_puncturedDisk_image_and_injOn_of_degreeBand", "TightVer401.completedSaddleAnnulusGraphHeight_fderiv_ne_zero", "TightVer401.completedSaddleAnnulusHeightResolved_separation", "TightVer401.completedSaddleAnnulusProtectedBand_of_support_coordinates"],
                    "shared-actual-parabolic-collar-calculus": ["TightVer401.parabolicConvexClosureCollar_contDiff", "TightVer401.parabolicConvexClosureCollar_differential_injective", "TightVer401.parabolicConvexClosureCollar_upper_eq", "TightVer401.parabolicConvexClosureCollar_lower_eq"],
                    "native-product-actual-geometry-transport": ["TightVer401.native_product_plane_geometry_transport", "TightVer401.nativeProductPlane_band_geometry", "TightVer401.nativeProductPlane_band_curvature_neg", "TightVer401.nativeProductPlane_band_gauss_support", "TightVer401.nativeProductPlane_coordinate_fderiv", "TightVer401.nativeProductPlane_coordinate_metric", "TightVer401.bandBending_plane_exact_sign_pair"],
                    "actual-native-intrinsic-length-distance-transport": ["TightVer401.nativeProductPlaneImmersion_pathELength_transport", "TightVer401.nativeProductPlaneImmersionEDist_transport"],
                    "actual-smooth-native-metric-bundles": ["TightVer401.nativeProductPlane_bending_scaled_common_smooth_metric", "TightVer401.nativeProduct_bending_branch_immersion", "TightVer401.nativeProductPlaneImmersionMetric_transport", "TightVer401.nativeProductPlaneTangentHomeomorph"],
                    "actual-compact-and-supported-embedding-stability": ["TightVer401.nativeCompactEmbedding_exists_amplitude_threshold", "TightVer401.nativeSupportedEmbedding_exists_parameter_threshold", "TightVer401.nativeSupportedEmbedding_exists_amplitude_threshold"],
                    "actual-embedded-identity-band-pair": ["TightVer401.periodicRuledFrame_exists_identity_embedded_curvature_pair"],
                    "actual-coupled-central-band-support": ["TightVer401.identityBand_central_support_tensor", "TightVer401.identityBandPlanarSupport_hessian_det_neg_on_image"],
                    "actual-asymmetric-parabolic-convex-meridian": ["TightVer401.exists_parabolic_convex_meridian", "TightVer401.exists_protectedParabolicMeridianInput_geometry", "TightVer401.parabolicConvexClosure_revolution_gaussianCurvature_pos", "TightVer401.parabolicConvexClosure_gaussHeight_bijOn"],
                    "actual-torus-topology-from-producer-data": ["TightVer401.protectedTorusMap_injective_from_data", "TightVer401.protectedTorusMap_range_from_data"],
                    "actual-protected-band-to-torus-bending-transfer": ["TightVer401.protectedTorusBendingField_contMDiff", "TightVer401.protectedTorus_compact_nonzero_bending"],
                    "actual-completion-neck-and-legendre-germs": ["TightVer401.exists_dualRadialCompletion_neck_local_legendre", "TightVer401.dualRadialCompletionNeckLegendre_germ", "TightVer401.dualRadialCompletionLegendre_involutive_germ"],
                    "actual-inner-gradient-annulus-and-legendre": ["TightVer401.quadraticFillerCartesianGradientEquiv", "TightVer401.quadraticFillerCartesianGradient_image", "TightVer401.quadraticFillerCartesianLegendre_gradient", "TightVer401.quadraticFillerCartesianLegendre_hessian", "TightVer401.quadraticFillerCartesianLegendre_gaussianCurvature_neg"],
                    "actual-analytic-quadratic-radial-filling": ["TightVer401.exists_quadratic_radial_filling", "TightVer401.exists_quadratic_radial_filling_boundary_data"],
                    "actual-native-band-chart-curvature": ["TightVer401.bandBending_actual_curvature_translation", "TightVer401.periodicRuledFrame_native_compact_bending_curvature_threshold"],
                    "actual-protected-band-planar-support": ["TightVer401.identityBand_exists_planar_support_annulus", "TightVer401.identityBandPlanarSupport_open_annuli", "TightVer401.identityBandPlanarSupport_bending_transfer", "TightVer401.identityBandPlanarRegionField_tsupport"],
                    "actual-band-bending-curvature-stability": ["TightVer401.bandBendingParameterCoordPartial_eq_slice", "TightVer401.bandBending_metricFamily_curvature_contDiffOn", "TightVer401.bandBending_actual_curvature_family_contDiffOn", "TightVer401.bandBending_compact_actual_curvature_threshold", "TightVer401.bandBending_actual_curvature_periodic", "TightVer401.periodicRuledFrame_compact_bending_curvature_threshold", "TightVer401.periodicRuledFrame_exists_identity_bending_curvature_pair"],
                    "actual-cartesian-quadratic-filler": ["TightVer401.exists_quadratic_cartesian_filler"],
                    "actual-cartesian-quadratic-gradient-boundary": ["TightVer401.exists_quadratic_cartesian_filler_large_gradient", "TightVer401.quadraticFillerCartesianGradientCircle_orientation", "TightVer401.quadraticFillerCartesianPotential_boundary_hessian_det", "TightVer401.quadraticFillerCartesianPotential_boundary_uniform_hessian_margin"],
                    "ver500-actual-torus-target-objects": [
                        "TightVer401.NonrigidTorusSource", "TightVer401.IsTightImage",
                        "TightVer401.ImageNoncongruent", "TightVer401.HasNoOpenPlanarPatch"],
                    "ver500-actual-polar-saddle-criterion": [
                        "TightVer401.saddlePolarChart_hessian_det_on",
                        "TightVer401.saddlePolarChart_hessian_det_neg_on",
                        "TightVer401.saddlePolarChart_gaussianCurvature_neg_on"],
                    "ver500-constructed-angular-filler-and-cartesian-descent": [
                        "TightVer401.exists_quadratic_filler_coefficient",
                        "TightVer401.exists_quadratic_filler_coefficient_with_cutoff",
                        "TightVer401.dualQuadraticFiller_boundary_first_jet",
                        "TightVer401.dualQuadraticFiller_inner_germ",
                        "TightVer401.quadratic_filler_exists_cartesian_descent",
                        "TightVer401.angularDescentPotential_hessian_det",
                        "TightVer401.angularDescentPotential_gaussianCurvature_neg"],
                    "ver500-quadratic-radial-germ-and-boundary": [
                        "TightVer401.dualRadialQuadraticPotential_gaussianCurvature_neg",
                        "TightVer401.dualRadialQuadraticCompactification_boundary_regular"],
                    "ver500-full-germ-preserving-neck-adapter": [
                        "TightVer401.exists_dualRadialNeck_adapter",
                        "TightVer401.exists_dualRadialNeck_saddle_adapter",
                        "TightVer401.exists_dualRadialNeck_gradient_adapter",
                        "TightVer401.radialPlanarGradient_norm_eq_abs_deriv"],
                    "ver500-native-torus-source-geometry": [
                        "TightVer401.nonrigidTorusSource_compact",
                        "TightVer401.nonrigidTorusSource_connected",
                        "TightVer401.nonrigidTorusSource_isManifold"],
                    "ver500-actual-square-root-neck-and-inverse": [
                        "TightVer401.dualRadialNeck_actual_first_jet",
                        "TightVer401.dualRadialNeck_deriv_tendsto_atTop",
                        "TightVer401.dualRadialNeck_inverse_legendre",
                        "TightVer401.dualRadialNeck_radius_of_derivative",
                        "TightVer401.dualRadialNeck_radial_support_geometry",
                        "TightVer401.dualRadialNeckLegendreGerm_radial_support_geometry"],
                    "constructed-embedded-identity-holonomy-band": [
                        "TightVer401.corrugatedSeed_exists_identity_holonomy_band",
                        "TightVer401.periodicRuledFrame_completeIdentityBand",
                        "TightVer401.periodicRuledFrame_identity_band_period_zero",
                        "TightVer401.periodicRuledFrame_identity_band_iff_period_zero",
                        "TightVer401.periodicRuledFrame_closed_asymptotic_leaves",
                        "TightVer401.periodicRuledFrame_identity_band_supported_kernel",
                        "TightVer401.periodicRuledFrame_bandSphereGauss_contMDiff",
                        "TightVer401.periodicRuledFrame_bandSphereGauss_differential_injective",
                        "TightVer401.periodicRuledFrame_bandGaussMap_orthogonal",
                        "TightVer401.periodicRuledFrame_northern_band_projection_regular",
                        "TightVer401.periodicRuledFrame_exists_embedded_flow_annulus",
                        "TightVer401.corrugatedSeed_exists_protected_identity_holonomy_band",
                        "TightVer401.periodicRuledFrame_saturatedIdentitySubband",
                        "TightVer401.identityFlowSurface_immersion",
                        "TightVer401.identityFlowSurface_real_lift",
                        "TightVer401.corrugatedSeed_exists_protected_identity_band_bending",
                        "TightVer401.periodicRuledFrame_protectedIdentityBendingSubband",
                        "TightVer401.periodicRuledFrame_exists_protected_bending",
                        "TightVer401.periodicRuledFrame_profile_tsupport_levels",
                        "TightVer401.identityFlowSurface_compact_nonzero_bending",
                        "TightVer401.isBandBending_pullback",
                        "TightVer401.bandBending_opposite_branches_metric",
                        "TightVer401.bandBending_branch_immersion",
                        "TightVer401.bandBending_opposite_branches_ne",
                        "TightVer401.bandBending_branches_agree_off_support"],
                    "complete-constructed-end": [
                        "TightVer401.exists_revolutionEnd_complete_continuation",
                        "TightVer401.revolutionEnd_closedEnd_complete",
                        "TightVer401.revolutionEndBoundaryEMetricSpace_edist",
                        "TightVer401.revolutionEndBoundaryEMetricSpace_topology",
                        "TightVer401.revolutionEndGauss_range",
                        "TightVer401.revolutionEndGaussEquiv",
                        "TightVer401.revolutionHeightInverse_contDiffOn"],
                    "eq:metricquad": ["TightVer401.metric_quadratic", "TightVer401.metric_sub_quadratic",
                                      "TightVer401.exact_sign_pair", "TightVer401.metric_pair_common",
                                      "TightVer401.Manifold.metric_quadratic", "TightVer401.Manifold.exact_sign_pair"],
                    "eq:return": ["TightVer401.projectiveReturn_multiplier_one", "TightVer401.projectiveReturn_fixed_iff",
                                  "TightVer401.projectiveReturn_comp", "TightVer401.projectiveReturn_second_jet",
                                  "TightVer401.principal_return_of_characteristic",
                                  "TightVer401.ruledOmega_increment", "TightVer401.ruled_return_of_actual_ODE",
                                  "TightVer401.principalTrajectory_hasDerivAt",
                                  "TightVer401.principalTrajectory_uniform_denominator",
                                  "TightVer401.ruled_flow_over_period"],
                    "eq:ruled-II": ["TightVer401.ruled_metric_entries", "TightVer401.ruled_metric_det",
                                    "TightVer401.ruled_isUnitNormal", "TightVer401.ruled_mixed_and_ruling_second_form",
                                    "TightVer401.ruled_second_form_det", "TightVer401.ruled_gaussianCurvature",
                                    "TightVer401.ruled_gaussianCurvature_neg",
                                    "TightVer401.ruled_second_form_ss", "TightVer401.ruled_asymptotic_slope",
                                    "TightVer401.ruled_characteristic_derivative_of_asymptotic"],
                    "eq:regular-holonomy-coordinate": ["TightVer401.regularCoordinate_transverse_derivative",
                                                       "TightVer401.regularCoordinate_characteristic_derivative"],
                    "eq:planar": ["TightVer401.planarSupportMap_coordPartial",
                        "TightVer401.planarSupportMap_isUnitNormal",
                        "TightVer401.planarHessian_symm",
                        "TightVer401.planarSupportMap_inducedMetric",
                        "TightVer401.planarSupportMap_secondFundamental",
                        "TightVer401.planarSupportMap_metric_det",
                        "TightVer401.planarSupportMap_differential_injective",
                        "TightVer401.planarSupportMap_gaussianCurvature_at",
                        "TightVer401.planarSupportMap_negative_curvature_iff",
                        "TightVer401.gnomonicSupport_reconstruction"],
                    "planar-converse-and-gradient-local-inverse": [
                        "TightVer401.planarSupportMap_converse_local",
                        "TightVer401.planarPotential_eq_weight_height",
                        "TightVer401.planarGradient_fderiv_apply",
                        "TightVer401.planarGradient_exists_smooth_local_inverse_at"],
                    "eq:action": ["TightVer401.planarTrace_value_deriv",
                        "TightVer401.planarTrace_gradient_deriv",
                        "TightVer401.planarTrace_periodic_action_zero"],
                    "eq:tangent-sign": ["TightVer401.gnomonicSupport_tensor",
                        "TightVer401.gnomonicSupport_trace_tangent"],
                    "gnomonic-support-determinant-and-duality": [
                        "TightVer401.gnomonic_inducedMetric_det",
                        "TightVer401.gnomonicSupport_endomorphism_det",
                        "TightVer401.gnomonicSupport_saddle_iff",
                        "TightVer401.planarLegendre_gradient",
                        "TightVer401.planarLegendre_hessian",
                        "TightVer401.planarLegendre_saddle"],
                    "eq:structural-moments": [
                        "TightVer401.normalLoop_exists_global_arclength_inverse",
                        "TightVer401.normalLoop_balance_density",
                        "TightVer401.normalLoop_whole_period_balance",
                        "TightVer401.normalLoop_construct_periodic_ruled_frame"],
                    "normal-loop-L1-position-bound": [
                        "TightVer401.normalLoopCurve_uniform_norm_sub_le"],
                    "positive-L1-speed-native-embedding-stability": [
                        "TightVer401.exists_speedCurve_tangent_radius",
                        "TightVer401.exists_speedCurve_distant_separation",
                        "TightVer401.exists_speedCurve_L1_representative_threshold",
                        "TightVer401.exists_speedCurve_L1_embedding_threshold",
                        "TightVer401.speedCurve_circle_mfderiv_injective",
                        "TightVer401.exists_speedCurve_L1_smooth_embedding_threshold"],
                    "normal-loop-embedded-balanced-frame": [
                        "TightVer401.normalLoop_balance_embedded_speed",
                        "TightVer401.normalLoop_arclength_reparameterized_injective",
                        "TightVer401.normalLoop_construct_embedded_balanced_frame"],
                    "corrugated-seed-certified-position-and-tangent-bounds": [
                        "TightVer401.corrugatedSeedBeta_error",
                        "TightVer401.corrugatedSeedUnitTangent_error",
                        "TightVer401.corrugatedSeedAverage_y_bound",
                        "TightVer401.corrugatedSeedAverage_cos_bound",
                        "TightVer401.corrugatedSeedPartner_uniform_error",
                        "TightVer401.corrugatedSeedPartner_radius_bounds"],
                    "moment-correction-preparatory-lemmas": [
                        "TightVer401.normalizedMomentControl_integral",
                        "TightVer401.momentPath_pos",
                        "TightVer401.momentPathMoment_eq",
                        "TightVer401.momentPath_l1_lt",
                        "TightVer401.momentNonlinearPeriod_continuous",
                        "TightVer401.momentNonlinearPeriod_slowdown"],
                    "normal-loop-frame-and-closure": [
                        "TightVer401.normalLoop_frame",
                        "TightVer401.normalLoop_second_derivative",
                        "TightVer401.normalLoop_derivative_P",
                        "TightVer401.normalLoopCurve_periodic_iff",
                        "TightVer401.normalLoop_physical_frame"],
                    "Gauss-equation-bridge": ["TightVer401.curvature_eq_second_form_det_div_metric_det",
                                              "TightVer401.negative_curvature_iff_second_form_det_neg"],
                    "corrugated-seed-actual-scalar-root": [
                        "TightVer401.corrugatedRoot_exists_unique",
                        "TightVer401.corrugatedRoot_exists_unique_nat",
                        "TightVer401.corrugatedCosExpectation_strictAnti",
                        "TightVer401.corrugatedCosExpectation_tendsto_atTop",
                        "TightVer401.corrugatedCosExpectation_tendsto_atBot",
                        "TightVer401.corrugatedRootIntegral_joint_contDiff",
                        "TightVer401.corrugatedRootValue_contDiffOn",
                        "TightVer401.corrugatedSeedNormalization_pos",
                        "TightVer401.corrugatedSeedMultiplier_pos",
                        "TightVer401.corrugatedSeedMultiplier_periodic"],
                    "complete-cylinder-local-end-geometry": [
                        "TightVer401.revolutionEnd_differential_injective",
                        "TightVer401.revolutionEnd_isUnitNormal",
                        "TightVer401.revolutionEnd_metric",
                        "TightVer401.revolutionEnd_secondFundamental",
                        "TightVer401.revolutionEnd_gaussianCurvature",
                        "TightVer401.revolutionEnd_gaussianCurvature_neg",
                        "TightVer401.revolutionNormalHeight_hasDerivAt",
                        "TightVer401.revolutionNormalHeight_strictMonoOn",
                        "TightVer401.revolutionNormalHeight_tendsto",
                        "TightVer401.revolutionEndCircle_isClosedEmbedding",
                        "TightVer401.revolutionEndCircle_isProperMap",
                        "TightVer401.revolutionEnd_absoluteCurvature_iterated_integral",
                        "TightVer401.revolutionEnd_absoluteCurvature_product_integral",
                        "TightVer401.revolutionEnd_absoluteCurvature_product_integrable",
                        "TightVer401.revolutionEndCircleFull_contMDiff",
                        "TightVer401.revolutionEndCircleFull_mfderiv_injective",
                        "TightVer401.revolutionEndGauss_injective",
                        "TightVer401.revolutionEndCircleGauss_contMDiff",
                        "TightVer401.revolutionEndCircleCurve_height_edist_le_pathELength",
                        "TightVer401.exists_revolutionEnd_positive_extension",
                        "TightVer401.revolutionEndInducedInner_pos",
                        "TightVer401.revolutionEndRiemannianMetric"],
                    "concave-cap-join-preparation": [
                        "TightVer401.concaveJetReconstruction_eqOn_of_second_deriv",
                        "TightVer401.concaveJetReconstruction_strict_concavity",
                        "TightVer401.jetLocalExtension_contDiff",
                        "TightVer401.exists_concave_first_jet_join"],
                    "polar-germ-and-circular-boundary-local-geometry": [
                        "TightVer401.polarSupportPotential_supportMap",
                        "TightVer401.polarSupportPotential_hessian",
                        "TightVer401.polarSupportPotential_hessian_det",
                        "TightVer401.polarSupportPotential_gaussianCurvature",
                        "TightVer401.polarSupportPotential_gaussianCurvature_neg",
                        "TightVer401.polarCompactification_contDiff",
                        "TightVer401.polarCompactification_boundary",
                        "TightVer401.polarCompactification_boundary_metric",
                        "TightVer401.polarCompactification_differential_injective",
                        "TightVer401.polarCompactification_eq_support",
                        "TightVer401.polarCompactification_isUnitNormal",
                        "TightVer401.polarCompactification_secondFundamental",
                        "TightVer401.polarCompactification_gaussianCurvature_neg"],
                    "actual-radial-planar-saddle-geometry": [
                        "TightVer401.radialPlanarPotential_contDiffOn",
                        "TightVer401.radialPlanarPotential_coordPartial",
                        "TightVer401.radialPlanarPotential_hessian",
                        "TightVer401.radialPlanarPotential_hessian_det",
                        "TightVer401.radialPlanarPotential_gaussianCurvature",
                        "TightVer401.radialPlanarPotential_gaussianCurvature_neg"]},
                "limits": ["The principal-normal geometric characteristic equation, actual integrating factor and period-integral return with explicit flow through zero over a full compact circuit are proved. The full general ruled characteristic coefficients, actual geometry, constructed flow, uniqueness and projective return/two-jet proposition are proved.",
                           "Actual open-sphere support reconstruction and the global injective regular Gauss-image bridge are proved. The planar potential curvature, converse, local gradient inverse and gnomonic support reconstruction are proved; global degree and surface completion remain pending.",
                           "None of the three principal existence theorems is yet proved.",
                           "Declaration counts do not measure the percentage of the paper formalized."]}
    coverage["additional_checked_scope"].update({
        "actual-visible-connector-only-completion-caller": [
            "TightVer401.dualRadialCompletionClaim_of_producers",
            "TightVer401.exists_dual_radial_support_completion_of_visible_connector"],
        "actual-exit-full-period-all-interior-winding": [
            "TightVer401.positiveExit_actual_positive_argument_lift",
            "TightVer401.positiveExit_positive_turn_all_interior_lifts",
            "TightVer401.positiveExitTrace_exists_completion_positive_traces"],
        "actual-marked-metric-normal-Gauss-ellipse-rigidity": [
            "TightVer401.MarkerEllipseAxesRecognition",
            "TightVer401.torusAffineMarkerContra_eq_inverse_adjoint",
            "TightVer401.affineMarkedTorusLinear_common_smooth_metric",
            "TightVer401.affineMarkedTorusGauss_native_curvature",
            "TightVer401.affineMarkedTorusPositiveGaussData",
            "TightVer401.torusAffineMarker_actual_meridian_rigid",
            "TightVer401.affineMarkedTorusGauss_actualCylinder_positive_image_rigid"],
        "actual-same-corrected-seed-visible-full-turn": [
            "TightVer401.positiveExit_balancedPartner_positive_turn_uniform_threshold",
            "TightVer401.positiveExit_central_support_with_balanced_turn",
            "TightVer401.positiveExit_seed_central_positive_turns",
            "TightVer401.positiveExit_exists_turn_complete_flow_initial_margin",
            "TightVer401.positiveExit_same_seed_visible_turn_protected_field"],
        "actual-cartesian-connector-closed-inverse-and-scalar": [
            "TightVer401.visibleConnector_cartesian_descent",
            "TightVer401.visibleConnector_exists_local_potential",
            "TightVer401.visibleConnectorSourceInverse_cartesian_jacobian_polar",
            "TightVer401.visibleConnectorSourceInverse_cartesian_positive_closed",
            "TightVer401.visibleConnectorSourceInverse_global",
            "TightVer401.visibleConnectorSourceInverseApplication_global",
            "TightVer401.visibleConnectorCartesianPotential_closed_strip_calculus",
            "TightVer401.visibleConnectorCartesianPotentialApplication_global"],
        "actual-same-potential-selected-traces-geometric-budget": [
            "TightVer401.positiveExit_exists_two_selected_visible_cartesian_patches"],
        "actual-selected-homotopy-closed-source-domain": [
            "TightVer401.positiveExit_actual_selected_pair_source_homotopy",
            "TightVer401.positiveExit_actual_source_homotopy_closed_annulus_in_domain"],
        "actual-native-connector-charts-same-inverse": [
            "TightVer401.visibleConnectorSourceInverse_native_charts_of_actual_inverse",
            "TightVer401.visibleConnectorSourceInverse_native_charts_of_raw"],
        "actual-same-terminal-geometry-and-original-point-source-inverse": [
            "TightVer401.visibleConnector_exists_actual_terminal_local_saddle",
            "TightVer401.visibleConnector_exists_uniform_periodic_actual_ruling",
            "TightVer401.visibleConnector_periodic_actual_coefficients_and_terminal_radial",
            "TightVer401.visibleConnector_periodic_actual_positive_terminal_pair",
            "TightVer401.visibleConnector_periodic_actual_terminal_jordan",
            "TightVer401.visibleConnectorDisplaced_exists_local_inverse"],
        "actual-final-potential-gradient-inverse-and-collar": [
            "TightVer401.visibleConnectorGradientInverseApplication_boundary_homeomorph",
            "TightVer401.visibleConnectorGradientInverseApplication_boundary_winding",
            "TightVer401.visibleConnectorGradientInverseApplication_ordinary_boundary",
            "TightVer401.visibleConnectorGradientInverseApplication_exists_collar",
            "TightVer401.visibleConnectorGradientInverseApplication_collar_agrees",
            "TightVer401.visibleConnectorGradientInverseApplication_global",
            "TightVer401.visibleConnectorGradientInverseApplication_restricted_chart",
            "TightVer401.visibleConnectorGradientInverseApplication_restricted_chart_properties",
            "TightVer401.visibleConnectorGradientInverseApplication_charts",
            "TightVer401.visibleConnectorGradientInverseApplication_terminal_traces_in_collars",
            "TightVer401.visibleConnectorGradientInverseApplication_terminal_circle_in_target",
            "TightVer401.visibleConnectorGradientInverseApplication_raw"],
        "actual-selected-homotopy-ordinary-pair-domain-connection": [
            "TightVer401.selectedSourceHomotopy_closedBand_subset",
            "TightVer401.selectedSourceHomotopy_closedBand_subset_source",
            "TightVer401.exists_markedTorus_pair_of_homotopy_exit_traces"],
        "actual-ordinary-exit-traces-to-marked-pair": [
            "TightVer401.exists_markedTorus_pair_of_ordinary_exit_traces"],
        "actual-exit-output-to-marked-pair": [
            "TightVer401.exists_dualRadialCompletionExitApplication_of_visible_connector",
            "TightVer401.exists_dualRadialCompletionExitApplication_inputs",
            "TightVer401.exists_dualRadialCompletion_exit_application_collar",
            "TightVer401.dualRadialCompletionExitApplicationPeriod_positive_traces",
            "TightVer401.exists_markedTorus_pair_of_actual_positive_exits"],
        "actual-visible-seed-and-protected-open-neighborhood": [
            "TightVer401.positiveExit_seed_central_visible",
            "TightVer401.positiveExit_same_seed_visible_protected_field",
            "TightVer401.identityFlowCoordinates_isOpen_range",
            "TightVer401.identityFlowBandInclusion_denominator_ne_zero",
            "TightVer401.identityFlowBandInclusion_isOpen_range",
            "TightVer401.identityFlowBandInclusion_planar_isOpen_range",
            "TightVer401.identityFlowBandInclusion_exists_protected_neighborhood"],
        "actual-marked-pair-from-ordinary-completed-support": [
            "TightVer401.exists_markedTorus_pair_of_ordinary_completed_support"],
        "actual-marked-completed-data-pair-connection": [
            "TightVer401.nativeTorusPositiveGaussData_of_branch_germs",
            "TightVer401.protectedTorus_marked_positive_regions",
            "TightVer401.periodicRuledFrame_marked_coordinate_inputs",
            "TightVer401.completedSaddleTorus_marked_branch_stability",
            "TightVer401.affineMarkedTorus_actual_positive_image_affine_rigid",
            "TightVer401.affineMarkedTorus_actualCylinder_bending_hasNoOpenPlanarPatch",
            "TightVer401.affineMarkedTorus_actualCylinder_bending_imageNoncongruent",
            "TightVer401.exists_completedSaddleTorus_marked_pair"]})
    coverage["additional_checked_scope"].update({'actual-canonical-ordinary-connector-witness-assembly': ['TightVer401.VisibleConnectorWitnessAssemblyTerminalFacts', 'TightVer401.visibleConnectorWitnessAssembly_terminal_trace', 'TightVer401.visibleConnectorWitnessAssembly_incoming_germ', 'TightVer401.VisibleConnectorWitnessAssemblyOrdinaryData', 'TightVer401.visibleConnectorWitnessAssemblyTopology_complex_point', 'TightVer401.visibleConnectorWitnessAssemblyTopology_positiveJordan', 'TightVer401.visibleConnectorWitnessAssemblyTopology_positive_traces', 'TightVer401.visibleConnectorWitnessAssemblyTopology_physical_geometry', 'TightVer401.visibleConnectorWitnessAssemblyTopology_annulus_geometry', 'TightVer401.visibleConnectorWitnessAssembly_phase_surjective', 'TightVer401.visibleConnectorWitnessAssembly_terminal_circle_range', 'TightVer401.visibleConnectorWitnessAssembly_terminal_circle_subset', 'TightVer401.visibleConnectorWitnessAssembly_positiveExitJacobian_det', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_determinant', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_negative', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_gradient_positive', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_contDiffOn', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_periodic', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_endpoints', 'TightVer401.visibleConnectorWitnessAssembly_native_raw_source_mapsTo', 'TightVer401.visibleConnectorWitnessAssembly_complex_circle_trace', 'TightVer401.visibleConnectorWitnessAssembly_complex_physical_boundary', 'TightVer401.visibleConnectorWitnessAssembly_of_ordinary', 'TightVer401.visibleConnectorWitnessAssembly_statement', 'TightVer401.exists_dual_radial_support_completion_of_ordinary_connector_data'], 'actual-ordinary-connector-data-to-same-homotopy-pair': ['TightVer401.exists_markedTorus_pair_of_ordinary_connector_data']})
    coverage["additional_checked_scope"].update({'actual-negative-hessian-reversed-gradient-order': ['TightVer401.visibleConnector_actual_negative_map_reverses_jordan_order', 'TightVer401.visibleConnector_actual_negative_map_reverses_positive_jordan_order', 'TightVer401.visibleConnectorGradientOrder_planarGradient', 'TightVer401.visibleConnectorGradientOrder_physical'], 'actual-negative-gradient-order-to-same-marked-pair': ['TightVer401.exists_markedTorus_pair_of_negative_gradient_order'], 'actual-incoming-collar-terminal-positive-filling-Gin-family': ['TightVer401.visibleConnectorIncomingNative', 'TightVer401.visibleConnectorIncomingNative_chart', 'TightVer401.visibleConnectorIncomingNative_continuous', 'TightVer401.visibleConnectorIncoming_exists_source_chart', 'TightVer401.visibleConnectorIncoming_exists_actual_collar', 'TightVer401.visibleConnectorDisplacedNativePsi', 'TightVer401.visibleConnectorDisplacedNativeChart', 'TightVer401.visibleConnectorDisplacedNativeChart_apply', 'TightVer401.visibleConnectorDisplacedNativePsi_chart', 'TightVer401.visibleConnectorDisplaced_exists_compact_native_collar', 'TightVer401.visibleConnectorDisplacedNativeSolution', 'TightVer401.visibleConnectorDisplacedNativeSolutionDomain', 'TightVer401.visibleConnectorDisplaced_exists_native_open_image', 'TightVer401.visibleConnectorDisplacedPhaseDifference', 'TightVer401.visibleConnectorDisplacedRealPhase', 'TightVer401.visibleConnectorDisplacedRealPhaseDomain', 'TightVer401.visibleConnectorDisplacedRealPhase_projection', 'TightVer401.visibleConnectorDisplaced_exists_smooth_real_phase', 'TightVer401.visibleConnectorDisplaced_exists_uniform_phase_signs', 'TightVer401.visibleConnectorTerminalNormalizedTrace', 'TightVer401.visibleConnectorTerminalNormalizedTrace_hasDerivAt', 'TightVer401.visibleConnectorTerminalNormalizedTrace_fields', 'TightVer401.visibleConnectorTerminal_exists_positive_completion_trace', 'TightVer401.visibleConnector_periodic_actual_terminal_positive_trace', 'TightVer401.visibleConnectorGinDisplacedPosition', 'TightVer401.visibleConnectorGinDisplacedGradient', 'TightVer401.visibleConnectorGinDisplacedDomain', 'TightVer401.visibleConnectorGinDisplacedVisibilityDomain', 'TightVer401.visibleConnectorGinRotatedDirection', 'TightVer401.visibleConnectorGinRotatedRuling', 'TightVer401.visibleConnectorGinDisplacedRuling', 'TightVer401.visibleConnectorGinRotatedRuling_eq_shifted', 'TightVer401.visibleConnectorGinDisplacedFamily_properties', 'TightVer401.visibleConnector_complex_norm_le_twice_coord_norm', 'TightVer401.visibleConnector_uniform_actual_terminal_norm_gt', 'TightVer401.visibleConnector_jordan_closure_norm_le', 'TightVer401.visibleConnector_closedBall_subset_jordanInterior', 'TightVer401.visibleConnector_jordan_enclosure_of_frontier_norm_bounds']})
    coverage["additional_checked_scope"].update({'frozen-canonical-gradient-order-witness': ['TightVer401.visibleConnectorGradientOrder_retained_incoming_terminal'], 'frozen-actual-positive-source-order': ['TightVer401.visibleConnector_actual_positive_map_preserves_positive_jordan_order', 'TightVer401.visibleConnector_actual_signed_map_orders_positive_jordan_fills', 'TightVer401.visibleConnectorSourceOrder_round', 'TightVer401.visibleConnectorSourceOrder_physical', 'TightVer401.visibleConnectorSourceOrder_retained_incoming_terminal'], 'frozen-same-inverse-central-fields-and-rebase': ['TightVer401.visibleConnectorDisplaced_exists_uniform_phase_signs', 'TightVer401.visibleConnectorRebaseParameter', 'TightVer401.visibleConnectorRebasedSource', 'TightVer401.visibleConnectorRebasedHeight', 'TightVer401.visibleConnectorRebasedRuling', 'TightVer401.visibleConnectorRebasedGradient', 'TightVer401.visibleConnector_rebase_source', 'TightVer401.visibleConnector_rebase_height', 'TightVer401.visibleConnector_rebase_smooth', 'TightVer401.visibleConnector_rebased_source_deriv', 'TightVer401.visibleConnector_rebased_ruling_deriv', 'TightVer401.visibleConnector_rebase_determinants', 'TightVer401.visibleConnector_rebase_value_deriv', 'TightVer401.visibleConnector_rebase_B', 'TightVer401.visibleConnector_rebase_positive', 'TightVer401.visibleConnector_rebase_gradient', 'TightVer401.visibleConnector_rebase_periodic']})
    coverage["additional_checked_scope"]["ver503-literal-normalized-bending-sign"] = [
        "TightVer401.completedSaddleTorusBandAffine_linear_apply",
        "TightVer401.completedSaddleTorusBendingField_source_eq_neg"]
    coverage["limits"] = [
        item.replace("global degree and surface completion remain pending.",
                     "actual degree and full quadratic filling are proved; original exits/full visible connector and ultimate original completion/pair caller remain pending.")
        for item in coverage["limits"]]
    coverage["limits"].append("Completed-saddle marked-pair connections are conditional on actual SAME completed scalar/geometry inputs and exact registered classical parameters; they do not discharge original exits/connector or ultimate existence.")
    (ROOT / "coverage.json").write_text(json.dumps(coverage, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Mapped {len(claims)} manuscript claims.")

if __name__ == "__main__":
    main()
