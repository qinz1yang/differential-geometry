# Actual radial cones and two-apex pointed splitting

This package proves full AC82 and AC84, with AC83 radial algebra and unique rays. AC83's full equivalence to the independently stated KL family-of-rays convention remains unfinished. The 29 public theorems, three definitions and one structure occupy five leaves; the metric baseline requires only a metric space. All radial parameters and the line are actual maps, and the full two-parameter distance law is retained.

The new comparison consumer applies the accepted AC43 splitting theorem to the SAME named two-apex line. Under properness, global CBB0 comparison and actual metric segments, it returns an onto isometry to Fin1 Euclidean space times a factor, based at the SECOND apex. That apex has coordinate zero; the first apex has coordinate minus their distance; the ENTIRE named line has coordinate t minus that distance. The factor retains properness, completeness, CBB0, segments and its dimension bound. No finite dimension assumption is needed for this consumer. No cone structure on the residual factor is asserted.

The snapshot/source record below describes the original candidate. Final repository compilation, independent regression and gate evidence are recorded separately in radial_cones_review.md and radial_cones_verification.json. Blueprint207 and migration interfaces are unchanged.

# AC82–84 radial cone data and the actual two-apex line

Production snapshot: `/tmp/gc_RadialConeData_agent.lean`, SHA256 `55709e9d4fb8704ae699ba38887c0bab154bd0c64953292d86fccb136626b759`. Namespace-only body: `/tmp/gc_RadialConeData_body.lean`, SHA256 `97ffbff3269c38cd1315f873001b2f77a51300ef19f26d949d7a930a59a4b000`.

## Exact scope

The file supplies 28 theorems, three definitions, and one structure. `RadialConeData p` has actual maps indexed by nonnegative reals, exact zero and identity values, and the full two-parameter squared-distance law with the metric polarization kernel. It assumes only `MetricSpace X`; no source properness, completeness, length, curvature, dimension, ray selection, or line existence is an input.

The shared forest proves kernel bounds/symmetry, apex and radius identities, same-ray distances, similarities, both kernel scaling identities, the semigroup law and inverse maps, positive-scale injectivity and surjectivity. The canonical unit ray goes through every non-apex point and is an isometry. Pointwise uniqueness from the two radial distance conditions gives radial segment uniqueness; its absolute-distance variant also handles points beyond the specified endpoint. Every actual isometric nonnegative-real ray through the apex and the specified non-apex point equals the canonical ray.

The named `H.twoApexLine K` uses the positive canonical ray from p through q and the continuation beyond p of the canonical ray from q through p. The additive cross-distance theorem is proved before the real-parameter isometry. Zero and nonpositive formulas agree at zero. Public `exists_line_through_two_apices H K hpq` returns an actual map on ALL real parameters, its `Isometry`, value p at zero and q at time `dist p q`. Distinctness is explicit and needed. No same-side-only or local-geodesic substitute is used. Root owns the separate existing-splitting consumer.

**Scope boundary:** AC82 and the metric line assertion of AC84 are implemented. AC83's radial algebra and ray/segment uniqueness are implemented. The equivalence to KL's family-of-rays/two-Euclidean-ray convention is NOT yet formalized; neither is the angular quotient construction or its triangle inequality. The metric kernel is not a bilinear form. This is not a claim that rescaling invariance alone is a cone.

## Sources actually read

Frozen `GEOMETRIZATION_BLUEPRINT/master207A.tex`, SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`: AC82 starts line6305, AC83 starts6340, AC84 starts6403, read through6443. Full `reference_checks_revision78.md` was read, including version and errata distinctions.

Kleiner–Lott, Astérisque365 local-collapse archive `KleinerLottAsterisqueLocalCollapse.pdf`, SHA256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`: actual Section2.2 cone convention, printed19/PDF14; Section4.5 and full Lemma4.19 proof, printed33/PDF28; full4.20 context, printed33–34/PDF28–29. The retained May15,2015 corrections affect6.5,14.1(2),20.2 and do not change4.19. KL's two-ray convention motivates the data; its exact equivalence remains the explicit formalization boundary above.

Burago–Burago–Ivanov archive `BuragoBuragoIvanovBook.pdf`, SHA256 `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`: actual3.6.12/3.6.13 and triangle-inequality proof printed91–92/PDF106–107,3.6.15/3.6.16 printed93/PDF108,3.6.17 and proof printed94/PDF109. The corrected distance uses cos(min(pi,angular distance)); zero-radius representatives are identified. The retained author errata `bbi-errata-2024-07-06.pdf`, SHA256 `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`, PDF5 was freshly text-read AND visually inspected (`/tmp/gc_AC82_BBI_errata5.png`): the incorrect radial-sum thresholds in3.6.16 must be angular-distance thresholds. BBI8.2.1's rescaling warning printed275/PDF290 is retained from the existing revision78 check (not freshly reopened by this agent in this bounded task).

Alexander–Kapovitch–Petrunin, archived `AlexanderKapovitchPetrunin303Alexandrov.pdf`, SHA256 `1ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed`: actual Section6E printed/PDF67, with surrounding66–68. It uses the clipped angular distance and distinguishes metric scalar-product notation from vector-space structure. Full retained July12,2026 author errata `akp-erratum-2026-07-12.pdf`, SHA256 `8f4642b105b03a52f23f920b6201a9156a2e0ceef63a37774c88e0d912801a79`, read; no correction to that cone formula. The archive, published edition, pinned TeX and moving repository are not identified. No new moving-source or migration probe was used.

## Evidence

`lake env lean /tmp/gc_RadialConeData_agent.lean`: exit0, empty log. `/tmp/gc_RadialConeData_lint.lean`: exit0; `#lint- only unusedArguments simpNF synTaut` silent; every one of the32 public declarations has only propext/Classical.choice/Quot.sound in transitive axiom closure. No admissions or new mathematical axioms. These are temporary-file Lean checks, not a shared repository build or acceptance gate.

Root independently read the baseline/source; ac65_same_lines independently reviews the entire final proof and supplies actual translated Euclidean-plane (distance5, both signs) and singleton examples. Those separate tests are recorded when their run finishes; do not infer them from this file's compilation.
