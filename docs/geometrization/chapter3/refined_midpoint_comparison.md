# Refined local comparison and continuous hyperbolic midpoint tools

Thirteen public theorems and one definition in three leaves provide a refined endpoint-comparison range, a continuous scalar midpoint principle with its actual hyperbolic interpolant, and an exact scalar-to-comparison-angle bridge. They support the original8R work; this milestone does not itself claim AC02 or AC64 from source geometry.

The new endpoint kernel retains actual complete L-buffers, local compactness, short curves and local four-point comparison, with exact arm-sum bound10L/33. It uses a=33/32,theta=11/16,ell=65r*/64 in the accepted retained-budget selection; these are verified proof constants. Earlier11/3/20/256 leaves remain unchanged. The exact model-side, comparison-angle and fixed-endpoint versions retain the original hinge/germs.

The scalar principle uses only continuity on the actual closed interval, the actual endpoint inequalities and ONE positive symmetric step at each interior point where comparison fails. The comparison function satisfies exact midpoint equality; the original function satisfies the corresponding upper midpoint inequality. A negative minimum of their difference contradicts cosh(kh)>1. No derivatives, support functions or geometric comparison are inferred from the scalar hypotheses. The actual weighted sinh interpolant, its endpoint identities, global symmetric identity, maximum bound, cosh representation and quotient implication are all proved. The maximum bound assumes only0<=max(u,v); positive frequency guards endpoint interpolation and the full consumer.

The last bridge keeps the same supplied a,A,b,c,C and sqrt(kappa) normalization. For0<a<=A andb>0, the actual cosh-interpolant inequality implies the comparison-angle shortening inequality, includinga=A and collinear model configurations. It supplies no missing metric interpolation premise.

The source and independent scalar review follow. Refined endpoint and angle-bridge original-input tests are in the final acceptance record. All source-geometric domain production remains a separate consumer. Blueprint207 and migration interfaces remain unchanged.

# Refined complete-buffer comparison kernel

The separate refined leaf keeps the frozen original-AC36 leaves unchanged. It proves model-side, canonical-germ angle, and endpoint comparison from the same metric/local-comparison/short-curve hypotheses and an actual complete closed L-ball at the chosen endpoint, for arm sum strictly below `10L/33`.

The proof uses the already independently reviewed budget-selection theorem with exact constants

- `a = 33/32`, `θ = 11/16`, hence `a/(1−θ) = 33/10`;
- `ℓ = 65r*/64`, hence `ℓ < ar*`;
- `2ℓ/3 = 65r*/96 < 11r*/16 = θr*`;
- `3ℓ = 195r*/64 < 33r*/10`.

The retained budget provides `dist(p*,p)+(33/10)r* ≤ (33/10)r(p) < L`. Thus the actual recentered segment producer has its closed-buffer hypothesis, every nearby point has the required short-hinge comparison threshold, and the accepted endpoint enlargement applies. No minimizing join is assumed. This gives the exact public threshold `10L/33`; it is stronger than the original-AC36 kernel's `3L/11` but does not by itself establish AC02 or AC64.

Sources were freshly checked during this task: blueprint207A original AC02 lines2141–2190, AC36 lines3885–3956, AC64 lines5374–5421; AKP pinned vol1 ed6a16eb2a3c `defs-CBB.tex` key-lem:globalization/lem:alm-min/globalization lines953–1218; KL§3.3 printed22–23/PDF17–18. Exact source identities/errata roles are in `/tmp/gc_AC36_budget_comparison_record.md` and independent `/tmp/gc_AC36_independent_review_record.md`. The new rational constants are project proof choices, not literal source constants. No source-qualified sharp comparison theorem is assumed.

Public declarations:

1. `Metric.MinimizingHinge.modelSide_ge_dist_of_complete_refined_budget_buffer`.
2. `Metric.MinimizingHinge.comparisonAngle_le_of_complete_refined_budget_buffer`.
3. `DifferentialGeometry.Geometry.Comparison.Toponogov.endpointHingeComparison_of_complete_refined_budget_buffer`.

All retain κ≥0 (model curvature−κ), explicit arbitrarily short curves, local four-point comparison, and local compactness. The region need not be complete globally. No finite dimension, properness, or global geodesic assumption is added.

Frozen body `/tmp/gc_RefinedBudgetInteriorComparison_body.lean` SHA256 `a453ad6620728573e99acab0b5ed3815a20af7ca8d5fb1630447aa429e48722b`; minimal combined driver `/tmp/gc_RefinedBudgetInteriorComparison_agent.lean` SHA256 `e965151fd275a65ece3d9ae6afc25f0fc57892372cfb2ea52051d671b8114423`. Imports are the budget-selection leaf, accepted ComparisonRadius, EndpointEnlargement and IsometricBufferSegment. Compiler exit0 with empty `/tmp/gc_RefinedBudgetInteriorComparison.log`; lint driver exit0 with standard3 closure for all three declarations and silent selected lint in `_lint.log`.

Regression `/tmp/gc_refined_budget_review_body.lean` constructs actual real metric short curves and local comparison, and an actual original isometric hinge with center0, endpoints−1 and2, in complete closed bufferL10 at−1. It proves that its arm sum3 is in the new range100/33 and outside the old range30/11, then invokes BOTH refined hinge theorems for every κ≥0 and the actual endpoint producer at100/33. Final regression compiler and lint both exited0; all three regression declarations have standard3 closure, selected lint is silent. Logs: `/tmp/gc_refined_budget_review.log` (empty) and `/tmp/gc_refined_budget_review_lint.log`.

Temporary-only implementation and evidence; no repository, shared build, source archive, or blueprint edits.

Final regression body SHA256 `484f9f7dc237c9250bb49d247b3dfbfa979eeb4bd70cf165e5e83ea606809455`; combined driver SHA256 `880ad3e3167ae05d06a5e43dcf4a1c43f6e748c840d52013b7e1a8a5710211e9`.

# Independent scalar hyperbolic midpoint review

Frozen production `/tmp/gc_HyperbolicMidpoint_body.lean`, SHA256 `fb8b8ab2f4cfae1566c0a41f7612421dc6a97381ee432ac161f3903a145a8b07`: nine public theorems and one real-valued interpolant definition. Complete final body independently read, including the appended cosh representation and quotient implication. No mathematical proof or scope issue found.

## Source checked

Pinned AKP source branchvol1, commit `ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`, author date2026-07-12, retained under `GEOMETRIZATION_BLUEPRINT/references/akp-ed6a16eb2a3c/`. Independently reopened actual `defs-CBB.tex` lines516–557, labels `thm:conc` / `comp-kappa`, full function-comparison statement and proof (file SHA256 `b80b54fafc6e30cbac121880c1b80265ee62afcd90d8a3ab77c0deef1a0e1f9c`). Also reopened `model.tex` lines38–94 and150–157, standard-function definitions/negative-curvature scaling and label `md-diff-eq` (file SHA256 `db849cb9a051e0c3f8ec335942c954f14223c542eee1a40c4bca4ea2a63af9f8`). The published/archived PDF and this pinned moving-source snapshot retain distinct locator namespaces; no new book build or current-web errata audit was performed.

AKP’s theorem assumes a complete length space and includes G-delta geodesicity; it translates CBB comparison into a differential inequality for modified distance. The new theorem is an independently proved scalar midpoint principle motivated by that route. It uses an explicit symmetric-step inequality, not an unproved identification with derivative/support concavity. It proves neither the geometric local step nor global geometry. The conversion of the actual long-short hinges remains a separate consumer. For lower curvature−λ, the hyperbolic frequency is sqrtλ, consistent with the checked standard-function table.

## Proof and assumptions

For continuous f,g on[a,b], endpoints g≤f, and frequencyk>0, the theorem only asks for ONE positive symmetric in-domain step at each interior point where f<g. Compactness supplies a negative minimum of f−g if comparison fails. Endpoint inequalities put that minimum in the strict interior. Both neighbor values are at least the minimum; the two midpoint conditions give their sum≤2cosh(kh) times that negative minimum, contradicting cosh(kh)>1. No derivative, second derivative, local Lipschitz or support-function assumption is smuggled in. Degenerate or empty intervals are harmless: a counterexample point would create a nonempty interval and force a strict interior minimum.

The actual sinh-weighted interpolant has exact endpoint values fork>0,A>0; its symmetric identity is algebraic for ALL real parameters. The upper-max estimate requires only0≤max(u,v), correctly allowing one negative endpoint. Its proof uses nonnegative weights and weight sum≤1. The full consumer builds its comparison function from the actual f endpoints, preserving the same function and interval.

The appended cosh formula is an exact addition-law rearrangement with positive denominator. The quotient implication divides only by sinh(kt)>0 and sinh(kA)>0. Its t>0 assumption is necessary for that division; t≤A is correctly not required once the interpolant inequality itself is supplied. No positivity off is assumed. Atk=0 the raw sinh-ratio definition evaluates to0 by Lean division convention; it is not an affine zero-curvature interpolation theorem. Positive-frequency hypotheses guard all endpoint and full-consumer claims.

## Concrete original-input tests

Frozen `/tmp/gc_hyperbolic_midpoint_review_body.lean`, SHA256 `b48cbdd6d978c5637409d91354d77c6a65571db60548ceae471052fe45b965ec`; combined `/tmp/gc_hyperbolic_midpoint_review_agent.lean`, SHA256 `69ac223983adb323146296223aa728bd53b2be15bccd9293e47fb4484dc82e9b`.

1. Actual continuous tent profile f(t)=2−|t−1| on[0,2]. The test independently proves the symmetric concavity inequality using the absolute-value triangle inequality, constructs a positive in-domain step at every interior point, then applies the FULL interpolant consumer. Its local premise is proved unconditionally rather than by assuming the global conclusion or exploiting the bad-point implication. The actual interpolant is strictly below the tent at the midpoint.
2. Actual weighted interpolant with unequal mixed-sign endpoints−2/5, frequency2, interval length3. Exact endpoints, ALL symmetric midpoint identities and the global≤5 bound are checked.
3. Negative control: endpoints−1/−1 give an interior value STRICTLY ABOVE their maximum−1, proving the max-nonnegativity assumption cannot simply be removed.
4. Zero-frequency control: the raw formula is identically0 and fails to interpolate the nonzero endpoint3, exercising the positive-frequency guard.
5. The actual tent interpolant inequality is fed to the NEW quotient theorem for every0<t≤2, retaining the same tent function and endpoint values.

Final compiler and `#lint- only unusedArguments simpNF synTaut` driver exited0 without warnings or diagnostics. All five public test declarations have exactly `[propext, Classical.choice, Quot.sound]` as axiom closure. No admissions, custom axioms, repository edits, shared builds or reference-archive mutations were made by this review.

# Hyperbolic interpolation to comparison angle

Production body: `/tmp/gc_HyperbolicInterpolation_body.lean`, SHA256 `86bc49e3f1577f148e2e7e7640bad752537c0734dc24a0262f1a0816b9f5fd03`.

One public theorem, `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_cosh_interpolate`. For positive κ,a,b and a≤A, the actual weighted sinh interpolation of cosh(√κ b), cosh(√κ C) at a bounded above by cosh(√κ c) implies Θκ(A,b,C)≤Θκ(a,b,c). Lower curvature is −κ and the frequency is √κ. No triangle inequalities, actual geometric production, or signs of c,C are assumed. The supplied parameters are retained literally. The equality case a=A is allowed with independent c,C.

Proof uses the reviewed `hyperbolicInterpolate_eq_cosh`, clears only strictly positive sinh(√κ A), sinh(√κ a), sinh(√κ b), then applies global antitonicity of real arccos. It deliberately does not encode endpoint values in an auxiliary function, which would wrongly conflate c,C when a=A.

Source basis: pinned AKP *Alexandrov geometry: foundations* source, branch vol1, commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, `defs-CBB.tex` 516–557 (`thm:conc` / `comp-kappa`), and `model.tex` 38–94,150–157 (`md-diff-eq`), freshly read with the scalar parent. This is an algebraic adapter motivated by that comparison route, not a proof of the geometric antecedent. `defs-CBB.tex` SHA256 b80b54fafc6e30cbac121880c1b80265ee62afcd90d8a3ab77c0deef1a0e1f9c; `model.tex` SHA256 db849cb9a051e0c3f8ec335942c954f14223c542eee1a40c4bca4ea2a63af9f8. No new external errata check. Actual accepted `Comparison.ModelAngle` definition and arccos antitone API inspected.

Concrete tests: actual real collinear opposite rays (q=0,a=1,A=3,z=−2,κ=4) yield both angles π; actual same ray (z=5) yields both angles 0. Interpolation hypotheses follow from exact cosh addition laws rather than assumed angle conclusions. A separate scalar endpoint test a=A=1,b=2,C=1,c=3 checks independent opposite-side arguments at equal radial parameters.

Test body `/tmp/gc_hyperbolic_interpolation_review_body.lean`, SHA256 69d8b3e0f8252b25e3b312e3a26fb53c705c9c9faec8f8da670d8cde22035073; combined driver `/tmp/gc_hyperbolic_interpolation_review_agent.lean`, SHA256 371e29453ecd0b777b46007f8a67883f80473bf7ecb48b8c0feb3b60319fdf19. Production compiled silently exit 0; final lint driver `/tmp/gc_hyperbolic_interpolation_review_lint.lean` compiled exit 0, `#lint- only unusedArguments simpNF synTaut` clean; all four new public declarations have only propext, Classical.choice, Quot.sound. No shared repository build or repository edit was performed.
