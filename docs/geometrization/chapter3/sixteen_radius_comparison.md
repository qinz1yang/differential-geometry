# Original AC36 at16R: quantitative almost-minimum proof

Eight public theorems in three leaves prove AC36 with the ORIGINAL16R controlled domain and ORIGINAL ambient four-point conclusion. They use the actual intrinsic metric of that open ball, local four-point comparison there, local compactness, ambient completeness and arbitrarily short curves. Finite Hausdorff dimension is not needed by this stronger adapted proof. No completeness of the open intrinsic domain or properness of the whole ambient source is assumed.

The proof is different from the frozen blueprint's reduction to the still separate sharp localized comparison theorem. A quantitative almost-minimum lemma retains the joint displacement/radius inequality. With a=11/10 andtheta=7/10, it supplies the exact11/3 budget; the actual cradle joins and comparison neighborhood then fit the supplied complete ball. Complete intrinsic15R buffers at ORIGINAL vertices in ballR give endpoint radius45R/11>4R. The existing same-metric image transfer yields the required inequality for the same original ambient points. Original8R AC02/AC64 remain separate; previous20/256 leaves are unchanged.

The detailed source and domain audit follows. Final source-copy/accepted-import tests and gate receipts identify the accepted bytes; production docstrings from the temporary candidates are omitted according to repository rules. Blueprint207 and migration interfaces are unchanged.

# Original AC36: retained-budget local comparison

Scope: eight proved declarations recover the original ambient four-point conclusion on `ball o R` from local comparison for the actual intrinsic metric on `ball o (16*R)`. The ambient space is complete and has explicit arbitrarily short curves; the open ball is locally compact. The proof needs no finite-dimensional hypothesis, no global properness of the ambient space, and no completeness or globally assumed minimizing segments on the open ball. Curvature parameter `κ ≥ 0` means model curvature `−κ`, including zero. The four-point predicate includes its usual repeated-outer-point conventions.

This is an adapted proof of the original conclusion, rather than the original blueprint reduction through an unproved sharp localized Toponogov input. It does not establish original AC02's `8R` statement or original AC64's `8r<L` statement. Those remain separate. Existing factor-20 and factor-256 leaves are unchanged.

## Source passages actually read

Frozen `GEOMETRIZATION_BLUEPRINT/master207A.tex`, SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`: full AC02 lines2141–2190; AC36 lines3885–3956; AC64 lines5374–5421; ALG05 lines7486–7534. AC36's original constants are 16R (open ball), 10R complete intrinsic buffers at vertices in ball2R, and D=5R. The new proof keeps the original hypothesis/conclusion but uses a different quantitatively verified argument.

AKP retained `vol1` source commit `ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`, `GEOMETRIZATION_BLUEPRINT/references/akp-ed6a16eb2a3c/defs-CBB.tex`, SHA256 `b80b54fafc6e30cbac121880c1b80265ee62afcd90d8a3ab77c0deef1a0e1f9c`: full `key-lem:globalization` lines953–1090; `lem:alm-min` lines1091–1130; globalization proof lines1133–1218. The archived 303-page AKP author PDF labels this material 8.35/8.36, pp96–100; the pinned TeX and archived/published numbering are kept distinct. Existing accepted `EndpointEnlargement` implements the fixed-endpoint cradle with the actual threshold `2ℓ/3`. Existing `AlmostMinimum` implements the geometric descent with one parameter. The new lemma separates displacement/decay parameters and retains the invariant explicitly. The numerical constants 11/10,7/10,25/24,11/3,15R are project proof choices, not source quotations.

Kleiner–Lott, Asterisque365 (2014), archived `KleinerLottAsterisqueLocalCollapse.pdf`, SHA256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`: §3.3 printed22–23/PDF17–18 read in full. The source discusses incomplete locally complete spaces, prior confinement of proof geodesics, and complete closed2D vertex balls for triangles with all sides<D. It cites BBI§10.3, rather than supplying the expanded quantitative localized proof. This new result does not assume that citation as a Lean theorem.

BBI archived AMS2001 `BuragoBuragoIvanovBook.pdf`, SHA256 `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`: full Theorem10.3.1 proof printed360–363/PDF375–378 read. Its first descent step permits displacement100R and does not prove the sharp2D localization. Retained July6,2024 errata, SHA256 `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`, PDF13 reread: limiting neighborhood at q, failing angle at c, Figure10.1 corrections. None supplies completeness of an open region.

The retained May15,2015 KL corrections and July12,2026 AKP errata comparison from `reference_checks_revision140.md` and `checks/evidence/revision140_globalization_sources.json` are reused for the unchanged passages. No fresh external byte-identity assertion is made. No PC snapshot, migration interface, source archive, or blueprint was changed.

## Proof and domains

1. For positive r, a>0, 0≤θ<1, local positive lower bounds, and completeness only of the closed `a*r(o)/(1−θ)` ball, select p satisfying
   `(1−θ)*dist(p,o)+a*r(p) ≤ a*r(o)`, `r(p)≤r(o)`, and `r(q)>θ*r(p)` whenever `dist(p,q)≤a*r(p)`.
   Under the negation, geometric descent stays in the invariant set because a step of length≤a*r(x) with r(y)≤θ*r(x) consumes at most the corresponding radius drop. The resulting Cauchy sequence has radius tending to zero, contradicting its local positive lower bound. The boundary case θ=0 is permitted.
2. Apply this to the existing capped endpoint-comparison radius with a=11/10 and θ=7/10. The invariant gives `dist(p*,p)+(11/3)*r(p*) ≤ (11/3)*r(p)`.
3. Set ℓ=25*r(p*)/24. Then ℓ<(11/10)r(p*) and `2ℓ/3=(25/36)r(p*)<(7/10)r(p*)`. Also `3ℓ=(25/8)r(p*)<(11/3)r(p*)`. Thus the existing fixed-endpoint enlargement argument has its required nearby comparison and its actual minimizing joins, all inside the supplied complete L-buffer whenever the original bad-hinge arm sum is <3L/11. Enlargement contradicts maximality of the capped comparison radius.
4. For intrinsic vertices lying in the original ambient ballR, intrinsic closed15R balls are actually complete: the accepted intrinsic metric, nonexpansive inclusion, topological embedding, and ambient completeness give this since `dist(vertex,o)+15R<16R`. The resulting endpoint-comparison radius is45R/11>4R. Every relevant two-arm sum for points in intrinsic ballR is<4R; accepted `RegionFourPoint` uses actual minimizing segments and the local three-germ sum.
5. The image of intrinsic ballR is the original ambient ballR. Existing intrinsic-distance agreement applies on its entire closedR neighborhood since4R<16R. The final `fourPointComparison_image_iff_of_dist_eq` transfers the inequality for the same original points and ambient pair distances. No replacement metric or assumed comparison structure is substituted.

## Frozen production

- `/tmp/gc_BudgetAlmostMinimum_body.lean`: one public theorem; SHA256 `bb87d64d3a7399d2ef1eae9e5ac0fe27f213e379ad6ab5e4fbf2709d03d7450f`.
  Minimal imports: `Mathlib.Analysis.SpecificLimits.Basic`, `Mathlib.Topology.MetricSpace.Cauchy`, `Mathlib.Tactic.Linarith`.
- `/tmp/gc_BudgetInteriorComparison_body.lean`: three public theorems; SHA256 `d96cfeb48e098c11b55b7d41cbf2982bc75ac27b26deee6c385bbb96437cccfa`.
  Imports: new budget-selection leaf, accepted `Geometry.Comparison.ComparisonRadius`, `Geometry.Comparison.EndpointEnlargement`, `Topology.MetricSpace.IsometricBufferSegment`.
- `/tmp/gc_IntrinsicSixteenBufferComparison_body.lean`: four public theorems; SHA256 `b5628ba33135a32afac1f2079fd1c270f09d123b8d7934fc3a3b4e7d11d7a7fc`.
  Imports: new budget-comparison leaf, accepted `Geometry.Comparison.RegionFourPoint`, `Geometry.Comparison.MetricTransfer`, `Topology.MetricSpace.IntrinsicBallLength`, `Topology.MetricSpace.IntrinsicBallGeometry`.
- Minimal combined driver `/tmp/gc_IntrinsicSixteenBufferComparison_agent.lean`: SHA256 `b35f75507cc21058a9e57cc3f6f836a9a765e07b20bec3a2111ec919bc0d1fb5`.
- Public inventory `/tmp/gc_AC36_budget_public.txt` lists all eight declarations.

Actual minimal-driver `lake env lean` exited0 with an empty log. The lint driver `/tmp/gc_IntrinsicSixteenBufferComparison_lint.lean` exited0; `#lint- only unusedArguments simpNF synTaut` was silent, and all eight declarations have exactly the standard closure `[propext, Classical.choice, Quot.sound]`. This is temporary compiler evidence, not a shared project gate or push. Independent root/peer review and concrete original-input testing are separate acceptance steps.
