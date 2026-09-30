# Uniform same-original-ray endpoint and finite representative-net acceptance

Three public theorems in two leaves add three owned declarations. The 430-module shared gate checks 2,069 owned declarations in 3,268 jobs. Seven new actual-object regressions and ten canonical-import standard-axiom reports pass, with silent selected lint. The separate unchanged blueprint static audit remains pending because historical iCloud inputs are still downloading; no static pass is claimed.

Every owned transitive axiom closure is restricted to propext, Classical.choice and Quot.sound. The ten explicit review reports cover three public production theorems and seven new concrete regressions. All older frozen fixtures are re-elaborated exactly once and are not counted as new tests. The shared gate records the three declarations as public theorems, with no admissions, new definitions, instances or generated declarations. Earlier mathematical leaves are unchanged. No full migrated-root, PDF, Overleaf or human-approval claim is made.

The inherited AreaUpperBarrier build warning remains outside these owned axiom closures.

Independent peer reviews read the complete frozen scalar, same-original-path and finite-net proofs. The uniform endpoint estimate keeps the exact supplied paths and unequal original lengths, derives actual angle existence from the original intrinsic8R geometry, and retains the exact sinh(1)*r coefficient. The generic net consumer retains compact actual directions and one positive cutoff without creating a direction in the empty case.

Four endpoint tests use the actual translated Euclidean plane with q=(7,-3), p=q+(1/2,0), R=2, original ray lengths1,2,3, exact noncollinear angle/chord data, identical and opposite directions at r=R/2=1, and scalar zero/maximal/interior chords including r=2. Three finite-net tests preserve the actual returned empty singleton net with positive cutoff, force at least two real representatives and three plane representatives, and prove exact radius S on every returned original path. The plane test preserves an injective labeled approximating triple. Geometry, compactness and Hausdorff dimension are independently proved from actual source fixtures.

These are bounded dependencies, not a proof of pi-geodesicity, tangent length/CBB, moving-direction convergence, pointed GH blowup identification, sharp sphere packing or tangent dimension. Blueprint207 and migration interfaces are unchanged.

# Uniform endpoint estimate for the same original rays

## Frozen proof files and checks

Production `/tmp/gc_UniformRayEndpoint_body.lean` SHA256 `7e27c30ad4c46242a7e9d30bde6ab945e137608cf649a26b7c20857590e24409`.
Minimal canonical-import driver `/tmp/gc_UniformRayEndpoint_agent.lean` SHA256 `61223202b4571e58ffd78768fb8076c4b6c9724b6bc36a97c38601b8342e915d`.
Lint/axiom driver `/tmp/gc_UniformRayEndpoint_lint.lean` SHA256 `ee0aa20a4925a439139583d9b367c7c0e0c666d4bd1c53b47ae376d60636b1b4`.

Two public theorems, no private declarations, definitions, structures, admissions, or new axioms. Normal compilation exited 0 with an empty log using default resource limits. Separate selected lint (`unusedArguments`, `simpNF`, `synTaut`) exited 0 without lint diagnostics; both transitive axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`. No repository edits or shared build performed by this author.

## Exact public scope

`Toponogov.side_le_sinh_mul_comparisonAngle_one`: for real r>0 and 0≤c≤2r,

  c ≤ sinh(r) * comparisonAngleNegCurvature 1 r r c.

This includes c=0 and c=2r. No angle is supplied as a hypothesis. The parameter 1 means model curvature −1.

`Toponogov.dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer`: original complete metric X with arbitrarily short explicit continuous curves, R>0, ambient local compactness of open B(p,8R), intrinsic local comparison parameter 1 there, q∈B(p,R/2), SAME supplied positive finite geodesic representatives σ and τ at q. For 0<r≤σ.length, r≤τ.length, r≤R/2, r≤1, it proves

  dist(σ.path r, τ.path r) ≤ sinh(1) * r * dist(σ.direction, τ.direction).

The conclusion uses a `letI HasAnglesAt q` produced from the original local comparison hypotheses. It asks for no separate direction-limit package, compactness, finite dimension, properness, tangent realization, or GH premise. The σ/τ lengths need not agree. It never chooses a replacement geodesic; the intermediate finite hinge is constructed from these exact supplied germs. The output is about the original path values and their actual completed directions. No endpoint-direction uniqueness is asserted. The positive-radius contract does not assert that representatives exist in singleton spaces.

## Source contract and proof route

Freshly read the actual KLP *Lectures on Alexandrov spaces with curvature bounded below*, Theorem 6.5, printed 62–64 / PDF 64–66, including the entire π-geodesic proof and its final warning. Archived PDF SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`. The source compares a vanishing-scale midpoint direction with a fixed geodesic direction approaching its limit; on printed 64 it uses comparison to make normalized same-radius endpoint distance small. The present exact sinh(1) estimate supplies that step for the accepted local curvature−1 convention. It is a proved quantitative adapter, not a coefficient quoted verbatim from KLP. The source's convention and Alexandrov-space definition were checked at Definition 1.2, printed 20 / PDF 22; the source often displays κ=0 arguments. This implementation explicitly retains curvature−1 and its hyperbolic factor. The author errata status is inherited from the existing revision63 source record; no new external errata retrieval or errata-free claim is made.

Original intrinsic 8R comparison and actual direction definitions are unchanged accepted dependencies. Their existing source records are reused, not claimed to have been newly audited from scratch. The bounded next-midpoint audit is `/tmp/gc_DirectionMidpoint_frontier_audit.md`.

Fresh finite-algebra checks:
- accepted `Comparison/EqualSideHalfAngle.lean`, `sinh_half_sq_eq_of_equal_comparison_sides`: the exact hyperbolic cosine-law identity at κ=1;
- Mathlib `Analysis/SpecialFunctions/Trigonometric/Bounds.lean` lines 119–127: `1−θ²/2≤cos θ`;
- Mathlib `Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean` lines 443–459: `0≤x` implies `x≤sinh x`;
- accepted `Analysis/Convex/HyperbolicSine.lean` lines 12–29: actual convexity proof and `sinh(t*h)≤t*sinh(h)` for 0≤t≤1 and h≥0.

The scalar proof squares nonnegative quantities, uses the exact half-angle identity and the cosine bound, and then unsquares with explicit signs. It obtains c≤sinh(r)*θ. For geometry, each original endpoint lies in closedB(p,R) from dist(q,p)<R/2 and r≤R/2. The accepted `exists_hinge_of_germs` is applied to the SAME σ.path and τ.path on (0,r]; fresh inspection of its body and `GermSegment.exists_isometry_segment_of_germ` confirms agreement at every positive original parameter (and the common base at zero). The accepted original intrinsic8R hinge comparison bounds the finite comparison angle by that germ angle. The accepted all-curvature joint direction limit identifies this germ angle with the actual completed-direction distance. Finally sinh(r)≤r*sinh(1).

## Independent review and regressions

Both `/root/ac57_half_angle` and `/root/ac57_source_review` independently read the complete frozen proof body and reported a proof/scope pass. They specifically checked original-path preservation, endpoint containment, κ=1 normalization, c=0 and c=2r behavior, the full joint direction limit, and the exact sinh(1)*r coefficient. These are independent mathematical/code reviews, not a claim of independent recompilation by them.

Half-angle owns the separate actual translated-plane producer applications. At this freeze those regressions are being compiled; their final paths/hashes/results will be appended or cited by the integrator. No uncompleted test is represented here as passed.

## Boundaries

This leaf is a finite uniform estimate. It proves no π-geodesicity, moving-direction normalized limit, tangent-as-GH-limit theorem, sharp sphere-packing bound, or tangent dimension formula. It is usable in either the actual-direction midpoint route or the finite-net proof of convergence to the same constructed tangent. Blueprint and unfinished PC interfaces remain unchanged.

### Final independent concrete checks

Half-angle's frozen independent record is `/tmp/gc_UniformRayEndpoint_independent_review_record.md`. The actual off-center translated-plane scaffold SHA256 is `c1f0cecba16c5bd71f13fc6ba4d30f493d66e94e3c0bb1d625a69b290fea3cec`; four-test extra body SHA256 `b302cdafcc2d58f40f63b7f5f4ef4b43c49c90de2b02434eca8e8438ca6e2156`. Its combined `/tmp/gc_uniform_ray_endpoint_review_agent.lean` SHA256 `ef54178c376170f5c578feebc84d41df4bb797b2ac4db9d1897f4296fbcc926d` compiled with exit0 and an empty log. Separate lint driver SHA256 `9042b5781d265fa0ae679f264600630bd3724f018bc4d1148f8d78f4edc68d0a` exited0 with no selected-lint diagnostics and standard3 closures for all four tests. These exercise noncollinear actual rays with unequal original domains, identical and opposite directions at the radius boundary, and scalar zero/maximal/interior sides including r=2. This is the peer's reported concrete compiler evidence; production files above remain unchanged.


# Uniform same-original-ray endpoint estimate: independent review and actual-input regressions

Reviewer: ac57_half_angle. Temp files only; no repository edits or shared builds.

## Review verdict

The full frozen production body passes independent proof and contract review. The scalar theorem includes every r>0 and 0<=c<=2r, including zero and opposite-angle endpoints. It uses the exact accepted hyperbolic equal-leg half-angle identity at parameter 1, the bound 1-theta^2/2<=cos(theta), and c/2<=sinh(c/2). Every squaring and unsquaring has the required nonnegative signs.

The geometric theorem retains the two supplied GeodesicRepresentative paths and their original possibly unequal domains. Exact original radial distances and q's original half-ball position place both endpoints in closedBall(p,R). HingeOfGerms constructs a finite hinge agreeing with the supplied original germs at every positive parameter through r and the same base at zero. The accepted same-H original intrinsic8R comparison applies. The full joint parameter-1 angle limit identifies its germ angle with the actual completed-direction distance. The original r<=1 restriction gives sinh(r)<=r*sinh(1). No compactness, finite dimension, tangent realization, replacement-ray endpoint, or unproved limiting-direction hypothesis is used. Comparison parameter 1 corresponds to model curvature -1.

I reread the complete production proof and the accepted bodies of Comparison/HingeOfGerms.lean, Comparison/EqualSideHalfAngle.lean, and Analysis/Convex/HyperbolicSine.lean. I also reread the source hinge-comparison statement/proof and angle-sidelength monotonicity in the retained AKP source snapshot ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, defs-CBB.tex lines 307-378 and 418-447, labels thm:defs_of_alex (angle) and cor:monoton. The accepted original8R localization is retained exactly; these source statements are not used to replace that proved adapter. The producer author's separate /tmp/gc_UniformRayEndpoint_record.md records the freshly checked KLP Theorem6.5 motivation, curvature normalization, and existing errata status. This reviewer did not independently reread KLP for this bounded test task and makes no new external-source claim. The sinh(1) coefficient is a proved adapter constant, not a verbatim source assertion.

## Actual original-input fixtures

The source is the actual Euclidean plane E2 with its inner-product metric. The ray base is q=(7,-3), while the local-ball center is p=q+(1/2,0), so dist(q,p)=1/2. We take R=2, hence the original intrinsic comparison ball is ball(p,16), q is strictly inside ball(p,1), and the allowed endpoint radius r=1 is exactly R/2 and exactly the upper normalization radius.

Curves are actual affine segments, with exact constant-speed metric identities and accepted variation estimates yielding arbitrary short curves. Global comparison0 is proved using actual inner-product angles and angle triangle inequalities, and accepted fourPointComparison.of_zero gives comparison parameter1. The accepted intrinsic/ambient local-comparison equivalence supplies the original intrinsic local hypotheses. Ambient local compactness is the actual Euclidean open-set instance.

The unchanged earlier plane fixture supplies actual original representatives along (1,0), (-3/5,4/5), and (-3/5,-4/5), with original lengths 1,2,3. The new scaffold proves the exact angle arccos(-3/5) and exact squared unit-radius chord16/5 for the first two rays, and constructs an actual reversed ray of original length3 with angle pi and equal-radius chord2r.

Four new public regression theorems:
1. Noncollinear original lengths1 and2, exact chord-square16/5, and the full producer bound for every 0<r<=1, with actual direction distance replaced by its independently proved arccos(-3/5) value.
2. Identical original ray at r=R/2=1: actual endpoint distance0 and direction distance0, with a direct application of the full producer.
3. Opposite original lengths1 and3 at r=1: the first original representative reaches its endpoint while the second remains interior; actual chord2 and direction distancepi, with the bound2<=sinh(1)*pi obtained from the full original-geometry producer.
4. Scalar zero-chord, maximal-chord at r=2,c=4, and nontrivial interior r=c=1. The r=2 case confirms the scalar theorem itself has no hidden r<=1 premise.

No test assumes an angular package, local curvature conclusion, chosen-hinge conclusion, or endpoint bound as a premise.

## Compiler, lint, and axioms

Working directory: /Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3.
Lean4.35.0-rc3; Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.

Normal command: lake env lean /tmp/gc_uniform_ray_endpoint_review_agent.lean. Actual final exit0; /tmp/gc_uniform_ray_endpoint_review_agent.log empty.
Lint/axiom command: lake env lean /tmp/gc_uniform_ray_endpoint_review_lint.lean. Actual exit0; no findings from #lint- only unusedArguments simpNF synTaut. All four new theorems have exactly propext, Classical.choice, Quot.sound.

For canonical-import integration, concatenate the unchanged gc_plane_direction_packing_review_body.lean ONCE, then new gc_uniform_ray_endpoint_review_scaffold.lean, then new gc_uniform_ray_endpoint_review_extra.lean. The private helpers require same-source concatenation. There are four new public tests; the one public theorem in the old plane fixture is inherited evidence, not a new declaration. The current combined driver includes the frozen production body because canonical integration is pending. Its import header lists the exact dependencies; test-only Mathlib.Tactic is used.

## Frozen hashes

- /tmp/gc_UniformRayEndpoint_body.lean: `7e27c30ad4c46242a7e9d30bde6ab945e137608cf649a26b7c20857590e24409`
- /tmp/gc_plane_direction_packing_review_body.lean: `da72dffd52a1167361f8d9155ccd1722e5213ab52c2b24790dd20a39f65794a2`
- /tmp/gc_uniform_ray_endpoint_review_scaffold.lean: `c1f0cecba16c5bd71f13fc6ba4d30f493d66e94e3c0bb1d625a69b290fea3cec`
- /tmp/gc_uniform_ray_endpoint_review_extra.lean: `b302cdafcc2d58f40f63b7f5f4ef4b43c49c90de2b02434eca8e8438ca6e2156`
- /tmp/gc_uniform_ray_endpoint_review_agent.lean: `ef54178c376170f5c578feebc84d41df4bb797b2ac4db9d1897f4296fbcc926d`
- /tmp/gc_uniform_ray_endpoint_review_lint.lean: `9042b5781d265fa0ae679f264600630bd3724f018bc4d1148f8d78f4edc68d0a`


# Finite actual representative nets: independent non-vacuity regressions

Reviewer: ac57_half_angle. Temp-only; no changes to frozen prior bodies, repository files, or shared build artifacts.

## Production reviewed

Metric.exists_finite_representative_net_with_common_length in /tmp/gc_FiniteGeodesicDirections_body.lean. Full body read. Its compact actual completed-direction net has epsilon/2 accuracy, its original representatives approximate each center within epsilon/2, and the triangle inequality yields strict epsilon coverage. Finite simultaneous original length bounds supply ONE positive cutoff. In the empty case the finite constraint is vacuous but the positive-radius filter still supplies a positive cutoff; no direction is created. No source metric completeness, curvature, nonempty direction, or tangent-realization premise is hidden in the proof. The supplied CompactSpace is the actual completed-direction compactness, not a replacement carrier.

## Three actual-input regressions

1. PUnit source, for every epsilon>0: invoke the theorem with compactness obtained from actual original singleton geometry. Retain the actual returned F and S, prove F=empty from the actual absence of positive geodesic representatives, preserve S>0, all original length bounds, and full net coverage of the empty actual direction space. This directly tests the empty finite-index case rather than choosing an arbitrary positive S independently of the producer.

2. Real source at q=7, epsilon=pi/4: compactness comes from the full original local-geometry/Hausdorff-dimension theorem. The independently constructed positive and negative original real directions are pi apart. Their returned approximants must be distinct, so the actual returned F has cardinality at least2. The SAME positive S satisfies S<=sigma.length for every returned representative, and every original path has dist(7,sigma.path S)=S. Full coverage of all actual completed directions is retained.

3. Translated Euclidean plane q=(7,-3), epsilon=pi/8: compactness is derived from actual affine short curves, actual global inner-product four-point comparison0 weakened to parameter1, and the actual Hausdorff dimension2 proved using Real.dimH_univ_eq_finrank and finrank_euclideanSpace_fin. The three original directions (1,0), (-3/5,4/5), (-3/5,-4/5), with original representative lengths1,2,3 and pairwise direction distances>pi/2, force an injective labeled triple of returned approximants. Thus cardF>=3. The test retains each original label's approximation estimate, all length bounds, one S>0, exact original endpoint radius S for every element of F, and the full completed-direction net property.

No test assumes the desired finite representative net, positive common cutoff, compact direction package, curvature conclusion, or dimension claim. Real and singleton compactness uses the previously frozen actual-source regressions; the plane compactness derivation is newly explicit in this test body.

## Source and dependency scope

The source geometric conventions are the unchanged actual direction completion of AKP section6D and actual tangent convention of6E, archived PDF SHA1ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed, printed/PDF67-68. Their targeted reading and the original local-geometry compactness route are recorded in /tmp/gc_CompactDirections_independent_review_record.md. The present leaf adds only finite-net approximation and a common positive finite-family length cutoff; it does not assert a new geometric comparison result. No new external source or errata check is claimed for this elementary finite-family consumer.

Mathlib revision c55e6e786f49471c72fbddbec5415808896aec1e; Lean4.35.0-rc3. New plane dimension evidence uses Mathlib/Topology/MetricSpace/HausdorffDimension.lean line492 and Mathlib/Analysis/InnerProductSpace/PiL2.lean lines203-209.

## Checks

Workdir /Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3.
Normal: lake env lean /tmp/gc_finite_geodesic_directions_review_agent.lean. Actual exit0; corresponding .log empty.
Lint/axioms: lake env lean /tmp/gc_finite_geodesic_directions_review_lint.lean. Actual exit0; no unusedArguments/simpNF/synTaut findings. All three public regression declarations have exactly propext, Classical.choice, Quot.sound.

## Integration assembly

The new public regression body is /tmp/gc_finite_geodesic_directions_review_body.lean (three public tests and two private plane compactness/dimension helpers). It uses unchanged prior private fixtures in the SAME source. Concatenate each exactly once in this order:
- gc_direction_space_review_body.lean
- gc_real_direction_obstruction_review_extra.lean
- gc_actual_direction_chart_review_scaffold.lean
- gc_direction_packing_open_review_extra.lean
- gc_original_compact_directions_review_scaffold.lean
- gc_original_compact_directions_review_extra.lean
- gc_plane_direction_packing_review_body.lean
- gc_uniform_ray_endpoint_review_scaffold.lean
- gc_finite_geodesic_directions_review_body.lean

The current normal/lint drivers import already accepted FiniteDimensionalDirections and other geometry dependencies, and prepend only the pending FiniteGeodesicDirections production body. A canonical-import driver can replace that body with its future import. Prior fixture public declarations are inherited checks, not new production or new regression counts. Test-only Mathlib.Tactic is used. No frozen prior body was changed.

## Frozen SHA256

- /tmp/gc_FiniteGeodesicDirections_body.lean: `3cff75e0cc48dc9064fa8f0938b9f3d3a9f95f795ddb70c364d32a17caa32eb1`
- /tmp/gc_finite_geodesic_directions_review_body.lean: `5311a57dcda026939af2f979e29b063d3b47ad3902a3f0f0e8db2ec757041060`
- /tmp/gc_finite_geodesic_directions_review_agent.lean: `7fe8db784536fc63b91d722d209bbc4359726a8b87b819900cc0dd6a30678cee`
- /tmp/gc_finite_geodesic_directions_review_lint.lean: `1c86d4a12abc8192ec31221af226f148583850ab6fcf07db7a1e434c5ac4afdb`


# Finite original representative nets with a common positive domain

One public theorem, Metric.exists_finite_representative_net_with_common_length, in /tmp/gc_FiniteGeodesicDirections_body.lean, SHA256 3cff75e0cc48dc9064fa8f0938b9f3d3a9f95f795ddb70c364d32a17caa32eb1.

For any metric X, original point q, actual HasAnglesAt q and compact actual completed SpaceOfDirections q, every epsilon>0 admits a finite set F of actual GeodesicRepresentative q and one S>0 with S<=sigma.length for all sigma in F, and every completed direction strictly within epsilon of an actual direction from F. X need not be complete, proper, or curvature-controlled. Empty actual directions and empty F are supported; no fallback direction or Nonempty instance is introduced.

Proof: compactness gives a finite epsilon/2 net with weak distance bound. Actual representative density supplies a strict epsilon/2 approximation for each member of that finite subtype. The image in original representatives is finite, and finite intersection of the original positive length neighborhoods supplies one common positive S. The triangle inequality gives the strict epsilon conclusion. The order is epsilon, finite family, common length; no uniform length over every original representative is claimed.

Source checked: KLP, Lectures on Alexandrov spaces with curvature bounded below, v1 July14 2026, Exercise3.4 printed37/PDF39 and its full semisolution printed129-130/PDF131-132. Archived PDF SHA256 3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67. Root read the actual exercise and proof, including its comparison and logarithm-map step. This lemma formalizes the finite geodesic direction net/common-domain step only. It does not claim the source's logarithm map, its whole-point distortion bound, or GH convergence. Existing canonical completion/density and finite-net results are reused unchanged. Retained source/errata status is reused; no fresh external check or absence-of-errata claim.

Minimal driver /tmp/gc_FiniteGeodesicDirections_agent.lean compiled exit0 with empty log. Selected lint/axiom driver /tmp/gc_FiniteGeodesicDirections_lint.lean compiled exit0, unusedArguments/simpNF/synTaut silent, closure exactly propext, Classical.choice, Quot.sound. Default resource limits. Source_review independently read the complete body and passed, explicitly checking the empty subtype/eventual_all case. Concrete actual-object tests are recorded separately when complete. No shared gate or static audit claim in this temporary record.


# Independent finite actual-direction net review

Reviewed the complete `/tmp/gc_FiniteGeodesicDirections_body.lean`, SHA256 `3cff75e0cc48dc9064fa8f0938b9f3d3a9f95f795ddb70c364d32a17caa32eb1`. Verdict: pass. Compactness gives a finite epsilon/2 net in the actual completed direction space; density chooses actual representatives at epsilon/2; the triangle estimate gives the stated strict epsilon bound. Finite intersection of original positive lengths yields ONE positive cutoff before any direction or evaluation time is chosen. The finset image may identify representatives without affecting coverage/length. Empty directions lead to an empty finite index type, so choice is a function on an empty type and no nontrivial ray is manufactured. The eventual positive cutoff remains available. This is exactly the finite-family first step of KLP3.4's semisolution printed130/PDF132, freshly read along with its definitions and statement; source hash and conventions are in `/tmp/gc_TangentBlowup_source_audit.md`.

The theorem was compiled transitively in our minimal TangentPairedNets/original blowup drivers and lint driver; no separate root-owned file was edited. Root reports its own standalone compile/lint/closure, and half_angle owns the independent real/two-member and empty-direction tests. This review does not assert pi-geodesicity or tangent GH convergence from the finite net alone.


```lean
import DifferentialGeometry.Geometry.Comparison.UniformRayEndpoint
import DifferentialGeometry.Geometry.Metric.FiniteGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalDirections
import DifferentialGeometry.Geometry.Comparison.DirectionPackingOpen
import DifferentialGeometry.Geometry.Comparison.AngularObstruction
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentChart
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic

open scoped NNReal

noncomputable section
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCDirectionSpaceReview

private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private def positiveCurve (L : ℝ) : Icc (0 : ℝ) L → ℝ := fun t => 7 + t.val

private def negativeCurve (L : ℝ) : Icc (0 : ℝ) L → ℝ := fun t => 7 - t.val

private theorem positive_isometry (L : ℝ) : Isometry (positiveCurve L) := by
  apply Isometry.of_dist_eq
  intro s t
  change |7 + (s : ℝ) - (7 + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
  congr 1
  ring

private theorem negative_isometry (L : ℝ) : Isometry (negativeCurve L) := by
  apply Isometry.of_dist_eq
  intro s t
  change |7 - (s : ℝ) - (7 - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
  rw [show 7 - (s : ℝ) - (7 - (t : ℝ)) = (t : ℝ) - s by ring, abs_sub_comm]

private theorem positive_path {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    IccExtend hL (positiveCurve L) t = 7 + t := by
  rw [IccExtend_of_mem hL _ ht]
  rfl

private theorem negative_path {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    IccExtend hL (negativeCurve L) t = 7 - t := by
  rw [IccExtend_of_mem hL _ ht]
  rfl

private theorem same_positive_angle {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    germComparisonAngle 0 (IccExtend hL.le (positiveCurve L))
      (IccExtend hM.le (positiveCurve M)) = 0 := by
  have heq := germComparisonAngle_congr_on (κ := 0) hL hM
    (γ := IccExtend hL.le (positiveCurve L))
    (β := IccExtend hM.le (positiveCurve M))
    (γ' := fun t : ℝ => 7 + t) (β' := fun t : ℝ => 7 + t)
    (fun t ht => positive_path hL.le ⟨ht.1.le, ht.2⟩)
    (fun t ht => positive_path hM.le ⟨ht.1.le, ht.2⟩)
  rw [heq]
  apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
  intro s _ t _
  rw [Real.dist_eq]
  congr 1
  ring

private theorem positive_negative_angle {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    germComparisonAngle 0 (IccExtend hL.le (positiveCurve L))
      (IccExtend hM.le (negativeCurve M)) = Real.pi := by
  apply germComparisonAngle_opposite (by norm_num) hL hM
  intro s hs t ht
  rw [positive_path hL.le ⟨hs.1.le, hs.2⟩,
    negative_path hM.le ⟨ht.1.le, ht.2⟩, Real.dist_eq,
    show 7 + s - (7 - t) = s + t by ring, abs_of_pos (add_pos hs.1 ht.1)]


private def positiveRepresentative {L : ℝ} (hL : 0 < L) : GeodesicRepresentative (7 : ℝ) where
  length := L
  length_pos := hL
  curve := positiveCurve L
  isometry := positive_isometry L
  start := by simp [positiveCurve]

private def negativeRepresentative {L : ℝ} (hL : 0 < L) : GeodesicRepresentative (7 : ℝ) where
  length := L
  length_pos := hL
  curve := negativeCurve L
  isometry := negative_isometry L
  start := by simp [negativeCurve]

theorem unequal_length_representatives :
    positiveRepresentative (by norm_num : (0 : ℝ) < 1) ≠
      positiveRepresentative (by norm_num : (0 : ℝ) < 2) := by
  intro h
  have hl := congrArg GeodesicRepresentative.length h
  norm_num [positiveRepresentative] at hl

theorem shortening_retains_actual_original_path (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
    ((positiveRepresentative (by norm_num : (0 : ℝ) < 2)).shorten
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num [positiveRepresentative])).path t = 7 + t := by
  rw [GeodesicRepresentative.shorten_path _ _ _ ht]
  change IccExtend _ (positiveCurve 2) t = 7 + t
  exact positive_path (by norm_num) ⟨ht.1, ht.2.trans (by norm_num)⟩

theorem singleton_representatives_empty : IsEmpty (GeodesicRepresentative (PUnit.unit : PUnit)) :=
  inferInstance


private instance : HasAnglesAt (7 : ℝ) :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ
    (real_comparison (by norm_num)) (mem_univ _)

theorem unequal_length_same_geodesic_direction :
    (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).geodesicDirection =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).geodesicDirection := by
  rw [GeodesicRepresentative.geodesicDirection_eq_iff]
  exact same_positive_angle (by norm_num [positiveRepresentative])
    (by norm_num [positiveRepresentative])

theorem unequal_length_same_completed_direction :
    (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).direction =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).direction := by
  rw [GeodesicRepresentative.direction_eq_iff]
  exact same_positive_angle (by norm_num [positiveRepresentative])
    (by norm_num [positiveRepresentative])

theorem opposite_completed_directions_distance :
    dist (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).direction
      (negativeRepresentative (by norm_num : (0 : ℝ) < 2)).direction = Real.pi := by
  rw [GeodesicRepresentative.dist_direction]
  exact positive_negative_angle (by norm_num [positiveRepresentative])
    (by norm_num [negativeRepresentative])

theorem shortening_preserves_completed_direction :
    ((positiveRepresentative (by norm_num : (0 : ℝ) < 2)).shorten
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num [positiveRepresentative])).direction =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).direction :=
  GeodesicRepresentative.direction_shorten _ _ _

theorem approximation_by_actual_positive_segment (v : SpaceOfDirections (7 : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : GeodesicRepresentative (7 : ℝ), dist v σ.direction < ε ∧
      dist (7 : ℝ) (σ.path (σ.length / 2)) = σ.length / 2 := by
  obtain ⟨σ, hσ⟩ := v.exists_representative_dist_lt hε
  exact ⟨σ, hσ, σ.dist_base_path ⟨by linarith [σ.length_pos], by linarith [σ.length_pos]⟩⟩

private instance : HasAnglesAt (PUnit.unit : PUnit) where
  tendsto_angle σ := isEmptyElim σ

theorem singleton_completed_directions_empty :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit)) := inferInstance

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private instance realHasAnglesAt (p : ℝ) : HasAnglesAt p :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ
    (real_comparison (by norm_num)) (mem_univ _)

private def positiveRepresentativeAt (p : ℝ) : GeodesicRepresentative p where
  length := 1
  length_pos := by norm_num
  curve := fun t => p + t.val
  isometry := by
    apply Isometry.of_dist_eq
    intro s t
    change |p + (s : ℝ) - (p + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
    congr 1
    ring
  start := by simp

private def negativeRepresentativeAt (p : ℝ) : GeodesicRepresentative p where
  length := 1
  length_pos := by norm_num
  curve := fun t => p - t.val
  isometry := by
    apply Isometry.of_dist_eq
    intro s t
    change |p - (s : ℝ) - (p - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
    rw [show p - (s : ℝ) - (p - (t : ℝ)) = (t : ℝ) - s by ring, abs_sub_comm]
  start := by simp

private theorem positive_path_at (p t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (positiveRepresentativeAt p).path t = p + t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem negative_path_at (p t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (negativeRepresentativeAt p).path t = p - t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem real_representative_paths_at (p : ℝ) (σ : GeodesicRepresentative p) :
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = p + t) ∨
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = p - t) := by
  have hend := σ.dist_base_path ⟨σ.length_pos.le, le_rfl⟩
  rw [Real.dist_eq] at hend
  rcases (abs_eq σ.length_pos.le).mp hend with hneg | hpos
  · right
    intro t ht
    have h := σ.dist_base_path ht
    have hdist := σ.dist_path ht ⟨σ.length_pos.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hdist
    rw [Real.dist_eq] at h
    have hlow := le_abs_self (σ.path t - σ.path σ.length)
    have hhigh := le_abs_self (p - σ.path t)
    linarith
  · left
    intro t ht
    have h := σ.dist_base_path ht
    have hdist := σ.dist_path ht ⟨σ.length_pos.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hdist
    rw [Real.dist_eq] at h
    have hlow := neg_le_abs (σ.path t - σ.path σ.length)
    have hhigh := neg_le_abs (p - σ.path t)
    linarith

private theorem representative_direction_cases_at (p : ℝ) (σ : GeodesicRepresentative p) :
    σ.direction = (positiveRepresentativeAt p).direction ∨
      σ.direction = (negativeRepresentativeAt p).direction := by
  rcases real_representative_paths_at p σ with hp | hm
  · left
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path (positiveRepresentativeAt p).path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos (by norm_num : (0 : ℝ) < 1)
      (γ := σ.path) (β := (positiveRepresentativeAt p).path)
      (γ' := fun t : ℝ => p + t) (β' := fun t : ℝ => p + t)
      (fun t ht => hp t ⟨ht.1.le, ht.2⟩)
      (fun t ht => positive_path_at p t ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq]
    congr 1
    ring
  · right
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path (negativeRepresentativeAt p).path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos (by norm_num : (0 : ℝ) < 1)
      (γ := σ.path) (β := (negativeRepresentativeAt p).path)
      (γ' := fun t : ℝ => p - t) (β' := fun t : ℝ => p - t)
      (fun t ht => hm t ⟨ht.1.le, ht.2⟩)
      (fun t ht => negative_path_at p t ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq, show p - s - (p - t) = t - s by ring, abs_sub_comm]

private theorem direction_cases_at (p : ℝ) (v : SpaceOfDirections p) :
    v = (positiveRepresentativeAt p).direction ∨ v = (negativeRepresentativeAt p).direction := by
  by_contra hn
  have hp : 0 < dist v (positiveRepresentativeAt p).direction :=
    dist_pos.mpr (fun h => hn (Or.inl h))
  have hm : 0 < dist v (negativeRepresentativeAt p).direction :=
    dist_pos.mpr (fun h => hn (Or.inr h))
  obtain ⟨σ, hσ⟩ := v.exists_representative_dist_lt (lt_min hp hm)
  rcases representative_direction_cases_at p σ with h | h
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_left _ _)) hσ
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_right _ _)) hσ

theorem actual_real_direction_obstruction_everywhere (p : ℝ) :
    AngularObstruction (SpaceOfDirections p) 1 (1 / 16) := by
  rintro ⟨ξ, ζ, hζ, hξ⟩
  have hpair := hζ (0 : Fin 2) 1 (by decide)
  have hzero := hξ (0 : Fin 2)
  have hone := hξ (1 : Fin 2)
  rcases direction_cases_at p (ζ 0) with h₀ | h₀ <;>
    rcases direction_cases_at p (ζ 1) with h₁ | h₁ <;>
    rcases direction_cases_at p ξ with hx | hx
  all_goals
    simp only [h₀, h₁, hx, dist_self] at hpair hzero hone
    linarith [Real.two_le_pi]


theorem actual_real_opposite_directions_everywhere (p : ℝ) :
    ∃ σ τ : GeodesicRepresentative p, σ.length = 1 ∧ τ.length = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ.path t = p + t ∧ τ.path t = p - t) ∧
      dist σ.direction τ.direction = Real.pi := by
  refine ⟨positiveRepresentativeAt p, negativeRepresentativeAt p, rfl, rfl,
    fun t ht => ⟨positive_path_at p t ht, negative_path_at p t ht⟩, ?_⟩
  rw [GeodesicRepresentative.dist_direction]
  change germComparisonAngle 0 (positiveRepresentativeAt p).path
    (negativeRepresentativeAt p).path = Real.pi
  apply germComparisonAngle_opposite (by norm_num)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  intro s hs t ht
  rw [positive_path_at p s ⟨hs.1.le, hs.2⟩, negative_path_at p t ⟨ht.1.le, ht.2⟩,
    Real.dist_eq, show p + s - (p - t) = s + t by ring,
    abs_of_pos (add_pos hs.1 ht.1)]

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private theorem chart_real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private theorem chart_real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments chart_real_segments

local instance : LocallyCompactSpace (ball (7 : ℝ) (8 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

private theorem chart_real_intrinsic_local :
    ∀ z : ball (7 : ℝ) (8 * (1 : ℝ)), ∃ Ω : Set (ball (7 : ℝ) (8 * (1 : ℝ))),
      @IsOpen _
        (intrinsicBallMetricSpace chart_real_curves 7 (by norm_num : (0 : ℝ) < 8 * 1)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _
        (intrinsicBallMetricSpace chart_real_curves 7 (by norm_num : (0 : ℝ) < 8 * 1)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff chart_real_curves 7
    (by norm_num : (0 : ℝ) < 8 * 1) z).mpr
    ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ _⟩

private theorem chart_real_obstruction (x : ball (7 : ℝ) (1 : ℝ)) :
    AngularObstruction (SpaceOfDirections x.val) 1 (8 * (2 : ℝ))⁻¹ := by
  convert actual_real_direction_obstruction_everywhere x.val using 1
  norm_num

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

theorem actual_real_two_direction_packing_open_and_univ :
    IsOpen {x : ball (7 : ℝ) (1 / 2) | ∃ ξ : Fin 2 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} ∧
    {x : ball (7 : ℝ) (1 / 2) | ∃ ξ : Fin 2 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} = univ := by
  let : LocallyCompactSpace (ball (7 : ℝ) (8 * (1 : ℝ))) := isOpen_ball.locallyCompactSpace
  constructor
  · exact isOpen_direction_packing_of_intrinsic_8_buffer chart_real_curves 7
      (R := 1) (by norm_num) chart_real_intrinsic_local 2
  · ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨σ, τ, _, _, _, hdist⟩ := actual_real_opposite_directions_everywhere x.val
    refine ⟨![σ.direction, τ.direction], ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm] <;> linarith [Real.pi_pos]

private theorem singleton_metric_segments (a b : PUnit) :
    ∃ f : unitInterval → PUnit, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  refine ⟨fun _ => a, continuous_const, rfl, Subsingleton.elim _ _, ?_⟩
  intro s t
  have hab : b = a := Subsingleton.elim _ _
  simp [hab]

private theorem singleton_short_curves : ∀ a b : PUnit, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → PUnit, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments singleton_metric_segments

private theorem singleton_comparison : fourPointComparison 1 (univ : Set PUnit) := by
  intro x hx a ha b hb c hc hax
  exact (hax (Subsingleton.elim _ _)).elim

private theorem singleton_intrinsic_local :
    ∀ z : ball (PUnit.unit : PUnit) (8 * (1 : ℝ)),
      ∃ Ω : Set (ball (PUnit.unit : PUnit) (8 * (1 : ℝ))),
      @IsOpen _ (intrinsicBallMetricSpace singleton_short_curves PUnit.unit
        (by norm_num : (0 : ℝ) < 8 * 1)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ (intrinsicBallMetricSpace singleton_short_curves PUnit.unit
        (by norm_num : (0 : ℝ) < 8 * 1)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff singleton_short_curves PUnit.unit
    (by norm_num : (0 : ℝ) < 8 * 1) z).mpr
    ⟨univ, isOpen_univ, singleton_comparison, mem_univ _⟩

private instance singleton_angles_everywhere (p : PUnit) : HasAnglesAt p where
  tendsto_angle σ := isEmptyElim σ

theorem actual_singleton_zero_direction_packing_open_and_univ :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit)) ∧
    IsOpen {x : ball (PUnit.unit : PUnit) (1 / 2) | ∃ ξ : Fin 0 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} ∧
    {x : ball (PUnit.unit : PUnit) (1 / 2) | ∃ ξ : Fin 0 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} = univ := by
  let : LocallyCompactSpace (ball (PUnit.unit : PUnit) (8 * (1 : ℝ))) :=
    isOpen_ball.locallyCompactSpace
  refine ⟨inferInstance, ?_, ?_⟩
  · exact isOpen_direction_packing_of_intrinsic_8_buffer singleton_short_curves PUnit.unit
      (R := 1) (by norm_num) singleton_intrinsic_local 0
  · ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private theorem real_dim_le_one (U : Set ℝ) : dimH U ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using (dimH_mono (subset_univ U)).trans_eq Real.dimH_univ

private theorem singleton_dim_le_one (U : Set PUnit.{1}) : dimH U ≤ (1 : ℕ) := by
  have hz : dimH U = 0 := dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)
  rw [hz]
  positivity

private theorem original_real_open_local : ∀ z ∈ ball (7 : ℝ) 2,
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
  intro z _
  exact ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ _⟩

private theorem original_singleton_open_local : ∀ z ∈ (univ : Set PUnit.{1}),
    ∃ Ω : Set PUnit, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
  intro z _
  exact ⟨univ, isOpen_univ, singleton_comparison, mem_univ _⟩

theorem actual_real_original_uniform_scaled_nets :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, 0 < s → s < S → ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset ℝ,
        T.card ≤ (1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℕ) * Real.sinh 2 / ε⌉₊) ^ (1 : ℕ) ∧
        (T : Set ℝ) ⊆ closedBall (7 : ℝ) s ∧
        ∀ x ∈ closedBall (7 : ℝ) s, ∃ y ∈ T, dist x y < ε * s := by
  exact exists_uniform_small_scale_nets_of_local_comparison_and_dimH chart_real_curves
    isOpen_ball (by norm_num : 1 ≤ (1 : ℕ)) (real_dim_le_one (ball (7 : ℝ) 2))
    original_real_open_local (mem_ball_self (by norm_num))

theorem actual_singleton_original_uniform_scaled_nets :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, 0 < s → s < S → ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset PUnit.{1},
        T.card ≤ (1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℕ) * Real.sinh 2 / ε⌉₊) ^ (1 : ℕ) ∧
        (T : Set PUnit.{1}) ⊆ closedBall (PUnit.unit : PUnit.{1}) s ∧
        ∀ x ∈ closedBall (PUnit.unit : PUnit.{1}) s, ∃ y ∈ T, dist x y < ε * s := by
  exact exists_uniform_small_scale_nets_of_local_comparison_and_dimH singleton_short_curves
    isOpen_univ (by norm_num : 1 ≤ (1 : ℕ)) (singleton_dim_le_one univ)
    original_singleton_open_local (mem_univ PUnit.unit)

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

theorem actual_real_original_compact_directions_proper_tangent :
    CompactSpace (SpaceOfDirections (7 : ℝ)) ∧ ProperSpace (TangentCone (7 : ℝ)) := by
  exact compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    chart_real_curves isOpen_ball (by norm_num : 1 ≤ (1 : ℕ))
    (real_dim_le_one (ball (7 : ℝ) 2)) original_real_open_local
    (mem_ball_self (by norm_num))

theorem actual_real_intrinsic_compact_directions_far_from_center :
    (14 : ℝ) ∈ ball 7 (8 * (1 : ℝ)) ∧ (14 : ℝ) ∉ closedBall 7 (1 / 2) ∧
    CompactSpace (SpaceOfDirections (14 : ℝ)) ∧ ProperSpace (TangentCone (14 : ℝ)) := by
  have hq : (14 : ℝ) ∈ ball 7 (8 * (1 : ℝ)) := by
    norm_num [mem_ball, Real.dist_eq]
  refine ⟨hq, by norm_num [mem_closedBall, Real.dist_eq], ?_⟩
  exact compact_directions_and_proper_tangent_of_intrinsic_eight_comparison_and_dimH
    chart_real_curves 7 (by norm_num : (0 : ℝ) < 1) (by norm_num : 1 ≤ (1 : ℕ))
    (real_dim_le_one (ball (7 : ℝ) (8 * (1 : ℝ)))) chart_real_intrinsic_local hq

theorem actual_singleton_original_compact_empty_directions_proper_tangent :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    CompactSpace (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    ProperSpace (TangentCone (PUnit.unit : PUnit.{1})) ∧
    ∀ x : TangentCone (PUnit.unit : PUnit.{1}), x = EuclideanCone.tip := by
  obtain ⟨hc, hp⟩ := compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    singleton_short_curves isOpen_univ (by norm_num : 1 ≤ (1 : ℕ))
    (singleton_dim_le_one univ) original_singleton_open_local (mem_univ PUnit.unit)
  refine ⟨inferInstance, hc, hp, ?_⟩
  intro x
  rcases EuclideanCone.eq_tip_or_eq_mk x with h | ⟨r, u, _, _⟩
  · exact h
  · exact isEmptyElim u

theorem actual_singleton_intrinsic_compact_directions_proper_tangent :
    CompactSpace (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    ProperSpace (TangentCone (PUnit.unit : PUnit.{1})) := by
  exact compact_directions_and_proper_tangent_of_intrinsic_eight_comparison_and_dimH
    singleton_short_curves PUnit.unit (by norm_num : (0 : ℝ) < 1)
    (by norm_num : 1 ≤ (1 : ℕ))
    (singleton_dim_le_one (ball (PUnit.unit : PUnit.{1}) (8 * (1 : ℝ))))
    singleton_intrinsic_local (mem_ball_self (by norm_num))

end GCDirectionSpaceReview

noncomputable section

open Set Filter Topology Metric InnerProductGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCPlaneDirectionPackingReview

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem comparison_eq_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : comparisonAngle ‖x‖ ‖y‖ ‖x - y‖ = angle x y := by
  rw [comparisonAngle, angle, norm_sub_pow_two_real]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem inner_comparison {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    fourPointComparison 0 (univ : Set V) := by
  intro p hp a ha b hb c hc hap hbp hcp
  simp only [comparisonAngleNegCurvature_zero]
  have he (x y : V) : comparisonAngle (dist p x) (dist p y) (dist x y) = angle (x - p) (y - p) := by
    rw [dist_comm p x, dist_comm p y]
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using comparison_eq_angle (x - p) (y - p)
  rw [he a b, he b c, he c a]
  have ht := angle_le_angle_add_angle (a - p) (-(b - p)) (c - p)
  rw [angle_neg_right, angle_neg_left, angle_comm (a - p) (c - p)] at ht
  linarith

private def base : Plane := WithLp.toLp 2 ![7, -3]

private def vector (i : Fin 3) : Plane :=
  ![WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![-3/5, 4/5], WithLp.toLp 2 ![-3/5, -4/5]] i

private theorem vector_norm (i : Fin 3) : ‖vector i‖ = 1 := by
  have hs : ‖vector i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∑ j : Fin 2, (vector i) j * (vector i) j) = 1
    fin_cases i <;> norm_num [vector, Fin.sum_univ_two]
  nlinarith [norm_nonneg (vector i)]

private theorem vector_inner_neg (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (vector i) (vector j) < 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [vector, PiLp.inner_apply, Fin.sum_univ_two] at *

private def ray (i : Fin 3) (t : ℝ) : Plane := base + t • vector i

private theorem ray_isometry (i : Fin 3) : Isometry (ray i) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, ray, ray,
    show base + s • vector i - (base + t • vector i) = (s - t) • vector i by
      rw [sub_smul]; abel,
    norm_smul, Real.norm_eq_abs, vector_norm, mul_one, Real.dist_eq]

private def representative (i : Fin 3) : GeodesicRepresentative base where
  length := (i.val : ℝ) + 1
  length_pos := by positivity
  curve := fun t => ray i t.val
  isometry := (ray_isometry i).comp isometry_subtype_coe
  start := by simp [ray]

private theorem representative_path (i : Fin 3) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) ((i.val : ℝ) + 1)) :
    (representative i).path t = ray i t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private instance : HasAnglesAt base :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ inner_comparison (mem_univ _)

private theorem ray_comparison (i j : Fin 3) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    comparisonAngleNegCurvature 0 s t (dist (ray i s) (ray j t)) =
      angle (vector i) (vector j) := by
  rw [comparisonAngleNegCurvature_zero, dist_eq_norm,
    show ray i s - ray j t = s • vector i - t • vector j by unfold ray; abel]
  have h := comparison_eq_angle (s • vector i) (t • vector j)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hs, abs_of_pos ht, vector_norm, vector_norm, mul_one, mul_one] at h
  rw [h, angle_smul_left_of_pos _ _ hs, angle_smul_right_of_pos _ _ ht]

private theorem representative_angle (i j : Fin 3) :
    (representative i).angle (representative j) = angle (vector i) (vector j) := by
  change germComparisonAngle 0 (representative i).path (representative j).path = _
  rw [germComparisonAngle_congr_on (representative i).length_pos (representative j).length_pos
    (γ' := ray i) (β' := ray j)
    (fun t ht => representative_path i t ⟨ht.1.le, ht.2⟩)
    (fun t ht => representative_path j t ⟨ht.1.le, ht.2⟩)]
  apply germComparisonAngle_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hp.prod_inl _, hp.prod_inr _] with z hs ht
  exact (ray_comparison i j hs ht).symm

theorem actual_translated_plane_direction_packing :
    (∀ i : Fin 3, (representative i).length = (i.val : ℝ) + 1) ∧
    (∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) ((i.val : ℝ) + 1),
      (representative i).path t = base + t • vector i) ∧
    (∀ i j : Fin 3, dist (representative i).direction (representative j).direction =
      angle (vector i) (vector j)) ∧
    ∀ i j : Fin 3, i ≠ j → Real.pi / 2 <
      dist (representative i).direction (representative j).direction := by
  refine ⟨fun _ => rfl, representative_path, ?_, ?_⟩
  · intro i j
    rw [GeodesicRepresentative.dist_direction, representative_angle]
  · intro i j hij
    rw [GeodesicRepresentative.dist_direction, representative_angle]
    exact inner_neg_iff_pi_div_two_lt_angle.mp (vector_inner_neg i j hij)

end GCPlaneDirectionPackingReview

namespace GCPlaneDirectionPackingReview

private theorem plane_segments (x y : Plane) :
    ∃ f : unitInterval → Plane, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → Plane := fun t => x + (t : ℝ) • (y - x)
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  rw [dist_eq_norm, show f s - f t = ((s : ℝ) - t) • (y - x) by
    dsimp [f]; rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs,
    ← dist_eq_norm y x, dist_comm y x]
  change |(s : ℝ) - t| * dist x y = dist x y * |(s : ℝ) - t|
  exact mul_comm _ _

private theorem plane_short_curves : ∀ x y : Plane, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → Plane, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments plane_segments

private def center : Plane := ray 0 (1 / 2)

private theorem base_center_dist : dist base center = 1 / 2 := by
  have h := (ray_isometry 0).dist_eq 0 (1 / 2)
  simpa [ray, center, Real.dist_eq] using h

private theorem plane_intrinsic_local :
    ∀ z : ball center (8 * (2 : ℝ)), ∃ Ω : Set (ball center (8 * (2 : ℝ))),
      @IsOpen _ (intrinsicBallMetricSpace plane_short_curves center
        (by norm_num : (0 : ℝ) < 8 * 2)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ (intrinsicBallMetricSpace plane_short_curves center
        (by norm_num : (0 : ℝ) < 8 * 2)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff plane_short_curves center
    (by norm_num : (0 : ℝ) < 8 * 2) z).mpr
    ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ _⟩

private def negative_ray (t : ℝ) : Plane := base - t • vector 0

private theorem negative_ray_isometry : Isometry negative_ray := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, negative_ray, negative_ray,
    show base - s • vector 0 - (base - t • vector 0) = (t - s) • vector 0 by
      rw [sub_smul]; abel,
    norm_smul, Real.norm_eq_abs, vector_norm, mul_one, Real.dist_eq, abs_sub_comm]

private def negative_rep : GeodesicRepresentative base where
  length := 3
  length_pos := by norm_num
  curve := fun t => negative_ray t.val
  isometry := negative_ray_isometry.comp isometry_subtype_coe
  start := by simp [negative_ray]

private theorem negative_rep_path (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 3) :
    negative_rep.path t = negative_ray t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem opposite_endpoint_distance (t : ℝ) (ht : 0 ≤ t) :
    dist (ray 0 t) (negative_ray t) = 2 * t := by
  rw [dist_eq_norm, ray, negative_ray,
    show base + t • vector 0 - (base - t • vector 0) = (2 * t) • vector 0 by
      rw [mul_smul]; norm_num; module,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), vector_norm, mul_one]

private theorem opposite_direction_distance :
    dist (representative 0).direction negative_rep.direction = Real.pi := by
  rw [GeodesicRepresentative.dist_direction]
  change germComparisonAngle 0 (representative 0).path negative_rep.path = Real.pi
  apply germComparisonAngle_eq_of_tendsto
  have hev : ∀ᶠ z : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      z.1 ∈ Ioc (0 : ℝ) 1 ∧ z.2 ∈ Ioc (0 : ℝ) 3 :=
    by
      have h₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 1 :=
        Ioc_mem_nhdsGT (by norm_num)
      have h₂ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 3 :=
        Ioc_mem_nhdsGT (by norm_num)
      filter_upwards [h₁.prod_inl _, h₂.prod_inr _] with z hz₁ hz₂ using ⟨hz₁, hz₂⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with z hz
  rw [representative_path 0 z.1 (by simpa using ⟨hz.1.1.le, hz.1.2⟩),
    negative_rep_path z.2 ⟨hz.2.1.le, hz.2.2⟩]
  have hd : dist (ray 0 z.1) (negative_ray z.2) = z.1 + z.2 := by
    rw [dist_eq_norm, ray, negative_ray,
      show base + z.1 • vector 0 - (base - z.2 • vector 0) =
          (z.1 + z.2) • vector 0 by rw [add_smul]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hz.1.1 hz.2.1), vector_norm, mul_one]
  rw [hd]
  exact (comparisonAngleNegCurvature_add (by norm_num) hz.1.1 hz.2.1).symm

private theorem noncollinear_direction_distance :
    dist (representative 0).direction (representative 1).direction = Real.arccos (-3 / 5) := by
  rw [GeodesicRepresentative.dist_direction, representative_angle, angle, vector_norm, vector_norm]
  norm_num [vector, PiLp.inner_apply, Fin.sum_univ_two]

private theorem noncollinear_endpoint_distance_sq :
    dist ((representative 0).path 1) ((representative 1).path 1) ^ 2 = 16 / 5 := by
  rw [representative_path 0 1 (by norm_num), representative_path 1 1 (by norm_num),
    dist_eq_norm, ← real_inner_self_eq_norm_sq]
  change (∑ j : Fin 2, (ray 0 1 - ray 1 1) j * (ray 0 1 - ray 1 1) j) = 16 / 5
  norm_num [ray, vector, Fin.sum_univ_two, base]

end GCPlaneDirectionPackingReview

namespace GCPlaneDirectionPackingReview

theorem actual_noncollinear_same_original_ray_bound :
    (representative 0).length = 1 ∧ (representative 1).length = 2 ∧
    dist ((representative 0).path 1) ((representative 1).path 1) ^ 2 = 16 / 5 ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      dist ((representative 0).path r) ((representative 1).path r) ≤
        Real.sinh 1 * r * Real.arccos (-3 / 5) := by
  let : LocallyCompactSpace (ball center (8 * (2 : ℝ))) := isOpen_ball.locallyCompactSpace
  refine ⟨by norm_num [representative], by norm_num [representative], noncollinear_endpoint_distance_sq, ?_⟩
  intro r hr hr1
  have h := dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer
    plane_short_curves center (R := 2) (by norm_num)
    (by rw [base_center_dist]; norm_num) plane_intrinsic_local
    (representative 0) (representative 1) hr
    (by simpa [representative] using hr1)
    (by norm_num [representative]; linarith)
    (by simpa using hr1) hr1
  rw [noncollinear_direction_distance] at h
  exact h

theorem actual_identical_same_original_ray_boundary :
    dist ((representative 1).path 1) ((representative 1).path 1) = 0 ∧
    dist (representative 1).direction (representative 1).direction = 0 ∧
    dist ((representative 1).path 1) ((representative 1).path 1) ≤
      Real.sinh 1 * 1 * dist (representative 1).direction (representative 1).direction := by
  let : LocallyCompactSpace (ball center (8 * (2 : ℝ))) := isOpen_ball.locallyCompactSpace
  refine ⟨dist_self _, dist_self _, ?_⟩
  exact dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer
    plane_short_curves center (R := 2) (by norm_num)
    (by rw [base_center_dist]; norm_num) plane_intrinsic_local
    (representative 1) (representative 1) (by norm_num)
    (by norm_num [representative]) (by norm_num [representative])
    (by norm_num) le_rfl

theorem actual_opposite_same_original_ray_boundary :
    (representative 0).length = 1 ∧ negative_rep.length = 3 ∧
    dist ((representative 0).path 1) (negative_rep.path 1) = 2 ∧
    dist (representative 0).direction negative_rep.direction = Real.pi ∧
    dist ((representative 0).path 1) (negative_rep.path 1) ≤ Real.sinh 1 * Real.pi := by
  let : LocallyCompactSpace (ball center (8 * (2 : ℝ))) := isOpen_ball.locallyCompactSpace
  refine ⟨by norm_num [representative], rfl, ?_, opposite_direction_distance, ?_⟩
  · rw [representative_path 0 1 (by norm_num), negative_rep_path 1 (by norm_num),
      opposite_endpoint_distance 1 (by norm_num)]
    norm_num
  · have h := dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer
      plane_short_curves center (R := 2) (by norm_num)
      (by rw [base_center_dist]; norm_num) plane_intrinsic_local
      (representative 0) negative_rep (by norm_num : (0 : ℝ) < 1)
      (by norm_num [representative]) (by norm_num [negative_rep])
      (by norm_num) le_rfl
    simpa only [mul_one, opposite_direction_distance] using h

theorem actual_scalar_equal_leg_boundary_and_interior :
    (0 : ℝ) ≤ Real.sinh 2 * comparisonAngleNegCurvature 1 2 2 0 ∧
    (4 : ℝ) ≤ Real.sinh 2 * Real.pi ∧
    (1 : ℝ) ≤ Real.sinh 1 * comparisonAngleNegCurvature 1 1 1 1 := by
  refine ⟨side_le_sinh_mul_comparisonAngle_one (by norm_num) le_rfl (by norm_num), ?_,
    side_le_sinh_mul_comparisonAngle_one (by norm_num) (by norm_num) (by norm_num)⟩
  have h := side_le_sinh_mul_comparisonAngle_one
    (r := 2) (c := 4) (by norm_num) (by norm_num) (by norm_num)
  have ha : comparisonAngleNegCurvature 1 2 2 4 = Real.pi := by
    convert comparisonAngleNegCurvature_add
      (κ := 1) (a := 2) (b := 2) (by norm_num) (by norm_num) (by norm_num) using 1; norm_num
  rwa [ha] at h

end GCPlaneDirectionPackingReview

namespace GCDirectionSpaceReview

theorem actual_empty_direction_net_positive_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (GeodesicRepresentative (PUnit.unit : PUnit.{1})), ∃ S : ℝ,
      F = ∅ ∧ 0 < S ∧ (∀ σ ∈ F, S ≤ σ.length) ∧
      ∀ v : SpaceOfDirections (PUnit.unit : PUnit.{1}),
        ∃ σ ∈ F, dist v σ.direction < ε := by
  let : CompactSpace (SpaceOfDirections (PUnit.unit : PUnit.{1})) :=
    actual_singleton_original_compact_empty_directions_proper_tangent.2.1
  obtain ⟨F, S, hS, hlength, hnet⟩ :=
    exists_finite_representative_net_with_common_length (PUnit.unit : PUnit.{1}) hε
  refine ⟨F, S, ?_, hS, hlength, hnet⟩
  ext σ
  exact isEmptyElim σ

theorem actual_real_representative_net_two_members_positive_cutoff :
    ∃ F : Finset (GeodesicRepresentative (7 : ℝ)), ∃ S : ℝ,
      0 < S ∧ 2 ≤ F.card ∧ (∀ σ ∈ F, S ≤ σ.length) ∧
      (∀ σ ∈ F, dist (7 : ℝ) (σ.path S) = S) ∧
      ∀ v : SpaceOfDirections (7 : ℝ), ∃ σ ∈ F, dist v σ.direction < Real.pi / 4 := by
  classical
  let : CompactSpace (SpaceOfDirections (7 : ℝ)) :=
    actual_real_original_compact_directions_proper_tangent.1
  obtain ⟨F, S, hS, hlength, hnet⟩ :=
    exists_finite_representative_net_with_common_length (7 : ℝ) (by positivity : 0 < Real.pi / 4)
  obtain ⟨σ, τ, _, _, _, hdist⟩ := actual_real_opposite_directions_everywhere (7 : ℝ)
  obtain ⟨s, hs, hσ⟩ := hnet σ.direction
  obtain ⟨t, ht, hτ⟩ := hnet τ.direction
  have hne : s ≠ t := by
    intro h
    have hh := dist_triangle σ.direction s.direction τ.direction
    rw [h, dist_comm t.direction τ.direction, hdist] at hh
    rw [h] at hσ
    linarith [Real.pi_pos]
  have hcard : 2 ≤ F.card := by
    have hsub : ({s, t} : Finset (GeodesicRepresentative (7 : ℝ))) ⊆ F := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hs
      · exact ht
    have h := Finset.card_le_card hsub
    simpa [hne] using h
  exact ⟨F, S, hS, hcard, hlength,
    fun σ hσ => σ.dist_base_path ⟨hS.le, hlength σ hσ⟩, hnet⟩

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

private theorem plane_dim_two : dimH (univ : Set Plane) = (2 : ℕ) := by
  rw [Real.dimH_univ_eq_finrank]
  simp [Plane]

private theorem plane_compact_actual_directions : CompactSpace (SpaceOfDirections base) := by
  have hlocal : ∀ z ∈ (univ : Set Plane), ∃ Ω : Set Plane,
      IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
    intro z _
    exact ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ _⟩
  exact (compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    plane_short_curves isOpen_univ (by norm_num : 1 ≤ (2 : ℕ))
    plane_dim_two.le hlocal (mem_univ base)).1

theorem actual_plane_representative_net_three_members_positive_cutoff :
    ∃ F : Finset (GeodesicRepresentative base), ∃ S : ℝ,
      ∃ σ : Fin 3 → GeodesicRepresentative base,
      0 < S ∧ 3 ≤ F.card ∧ Function.Injective σ ∧
      (∀ i, σ i ∈ F ∧ dist (representative i).direction (σ i).direction < Real.pi / 8) ∧
      (∀ τ ∈ F, S ≤ τ.length) ∧ (∀ τ ∈ F, dist base (τ.path S) = S) ∧
      ∀ v : SpaceOfDirections base, ∃ τ ∈ F, dist v τ.direction < Real.pi / 8 := by
  classical
  let : CompactSpace (SpaceOfDirections base) := plane_compact_actual_directions
  obtain ⟨F, S, hS, hlength, hnet⟩ :=
    exists_finite_representative_net_with_common_length base (by positivity : 0 < Real.pi / 8)
  choose σ hmem happ using fun i : Fin 3 => hnet (representative i).direction
  have hinj : Function.Injective σ := by
    intro i j hij
    by_contra hne
    have hsep := actual_translated_plane_direction_packing.2.2.2 i j hne
    have hd := dist_triangle (representative i).direction (σ i).direction (representative j).direction
    rw [hij, dist_comm (σ j).direction (representative j).direction] at hd
    have hi := happ i
    rw [hij] at hi
    linarith [happ j, Real.pi_pos]
  have hcard : 3 ≤ F.card := by
    have hh := Fintype.card_le_of_injective (fun i : Fin 3 => (⟨σ i, hmem i⟩ : F)) (by
      intro i j hij
      exact hinj (congrArg Subtype.val hij))
    simpa using hh
  exact ⟨F, S, σ, hS, hcard, hinj, fun i => ⟨hmem i, happ i⟩, hlength,
    fun τ hτ => τ.dist_base_path ⟨hS.le, hlength τ hτ⟩, hnet⟩

end GCPlaneDirectionPackingReview

#lint- only unusedArguments simpNF synTaut
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.side_le_sinh_mul_comparisonAngle_one
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer
#print axioms Metric.exists_finite_representative_net_with_common_length
#print axioms GCPlaneDirectionPackingReview.actual_noncollinear_same_original_ray_bound
#print axioms GCPlaneDirectionPackingReview.actual_identical_same_original_ray_boundary
#print axioms GCPlaneDirectionPackingReview.actual_opposite_same_original_ray_boundary
#print axioms GCPlaneDirectionPackingReview.actual_scalar_equal_leg_boundary_and_interior
#print axioms GCDirectionSpaceReview.actual_empty_direction_net_positive_cutoff
#print axioms GCDirectionSpaceReview.actual_real_representative_net_two_members_positive_cutoff
#print axioms GCPlaneDirectionPackingReview.actual_plane_representative_net_three_members_positive_cutoff
```
