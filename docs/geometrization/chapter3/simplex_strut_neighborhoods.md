# Full conditional AC11: explicit simplex and original-anchor neighborhoods

Ten public theorems and one definition in four leaves prove the quantitative regular-simplex construction, selection of original representative endpoints at ONE common shortening scale, and a stable neighborhood of those SAME endpoints. They retain the original explicit direction-density, radial-representative and comparison-angle-limit inputs. Production of a Euclidean tangent and those direction inputs remains separate.

The core constructs the displayed blueprint simplex in the zero-sum hyperplane and realizes it by an actual orthonormal-basis isometry in EuclideanSpace R (Fin m). The exact inner products and angles include the antipodal m=1 case. For 1<=m<=n the exact margins are 8theta_n before approximation, strictly6theta_n after selecting original dense directions, strictly5theta_n at the shortened original endpoints, and strictly4theta_n throughout the final neighborhood, with theta_n=(8n)^-1. Available radii may differ by label; the selected single positive scale is below any prescribed positive cap and within ALL selected radii.

The finite-anchor vertex theorem works in any metric source and at degenerate collinear configurations. Its proof uses continuity of the actual hyperbolic comparison angle with nonzero arms, then the triangle inequality. It returns rho<s/8 and rho<cap, and every anchor remains farther than s/2. The full conditional theorem chooses original labels and s FIRST and then supplies such a neighborhood for EVERY positive cap; downstream consumers can choose a cap depending on the already chosen s without altering anchors. Source and label universes are independent.

This is AC11's full conditional metric construction with its actual needed inputs exposed. It does not assert direction-space completion, a tangent-cone isometry, angular density or the angle-limit theorem from local source geometry, nor supply the angular obstruction. No such missing producer is disguised as a concluded strut. The global properness/completeness/dimension machinery and PC migration bindings are unchanged. Blueprint207 is unchanged.

# AC11 regular-simplex core and common shortening

Status: production bodies compile with minimal imports, public declarations lint clean, all transitive axiom closures are exactly the standard three (`propext`, `Classical.choice`, `Quot.sound`). Both the scalar/vector regressions and the actual original-input shortening regression compile and lint cleanly, with standard3 axiom closure. Source and direction-label universes are independent.

## Sources actually checked

- Frozen blueprint `GEOMETRIZATION_BLUEPRINT/master207A.tex`, AC11 (`lem:alexandrov-simplex-struts`), lines 2600–2639; SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`.
- AKP *Alexandrov geometry: foundations*, retained source branch `vol1`, commit `ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`; `GEOMETRIZATION_BLUEPRINT/references/akp-ed6a16eb2a3c/dim.tex`, lines 22–105, definitions/proofs at `def:strut-I`, `prop:stutt`, `cor:rank>=k-open`. The exact theorem/proof body was read. This source uses approximation by geodesic directions, shortening, and openness; it does not state the blueprint's explicit `1/(8n)` constant. That quantitative margin is proved here by the explicit regular-simplex calculation.
- Retained author `erratum.tex` and actual author errata text from `references/chapter13_2026-09-26/AKP_erratum_2026-09-26.txt`, dated July 12, 2026, were read. The published p238 correction requires both `x_n → p` and direction convergence; this work does not infer direction realization from direction convergence alone. The published p228 onto-product correction does not enter the simplex argument. The archived PDF and moving/revised source are kept distinct.
- Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`: `Analysis/InnerProductSpace/PiL2.lean`, especially `OrthonormalBasis.fromOrthogonalSpanSingleton` at 1161–1164, constructs the actual isometry from the orthogonal complement into `EuclideanSpace ℝ (Fin m)`; `Geometry/Euclidean/Angle/Unoriented/TriangleInequality.lean`, `angle_le_angle_add_angle` at 192–201; `Analysis/SpecialFunctions/Trigonometric/Bounds.lean`, `Real.sin_le` at 55; and `Trigonometric/Inverse.lean` arcsin/arccos identities.

## Exact implementation and scope

`EuclideanSpace.regularSimplexVector m i` is exactly `sqrt((m+1)/m) • (e_i − (m+1)⁻¹ u)` in `EuclideanSpace ℝ (Fin (m+1))`. Its coordinate sum is zero. For `m>0`, its norm is one and its inner products are exactly one on the diagonal and `−1/m` off the diagonal. The standard unoriented angle is exactly `π/2+arcsin(1/m)`, including the antipodal `m=1` case. The orthogonal-complement orthonormal basis produces an actual family in `EuclideanSpace ℝ (Fin m)`; no completed basis or desired family is assumed. For `m≤n`, the lower margin is exactly `π/2+8θ_n`, where `θ_n=(8n)⁻¹`. Perturbing each direction through an angle strictly below `θ_n` yields the strict `6θ_n` margin.

`exists_common_shortening_strut_of_dense_directions` receives an original indexed family of unit Euclidean directions, actual original radial representatives `γ_d`, positive available radii `r_d`, exact radial distances on `0<s≤r_d`, angular density, and the actual comparison-angle limit for each pair at `s↓0`. It chooses original labels `d_j` and ONE positive common `s`, below any prescribed positive cap and within EVERY selected original radius. It returns the original endpoints `γ_(d_j)(s)`, exact common distances, the selected direction margin `6θ_n`, and their actual curvature-minus-one endpoint comparison margin `5θ_n`.

The adapter only requires radial distances and the diagonal one-parameter angle limit, which are the specific consequences of geodesic representatives and full angular limits needed in the proof. It does not produce a tangent-cone isometry, a direction completion, direction density, geodesic representatives, or their angle limits. Those remain explicit hypotheses, consistent with AC11's conditional contract. No source completeness, properness, curvature, dimension, or geodesic axioms are smuggled into these finite algebra/selection leaves. Root separately supplies the same-anchor vertex-continuity result and the full conditional assembly.

## Files and evidence

- `/tmp/gc_RegularSimplexDirections_body.lean`: one definition, seven public theorems, one private algebra lemma; SHA256 `577aa97db47160e714257c6cff753c02ddc43815c3b59c56f19ce4abfc4bd129`.
- `/tmp/gc_RegularSimplexDirections_agent.lean`: minimal production driver; SHA256 `5a4e8b50b2e19cc7f136f6802c336a15f44f1d98375c6b07d7086af02958e7a2`; compiler exit 0, empty `/tmp/gc_RegularSimplexDirections.log`.
- `/tmp/gc_RegularSimplexDirections_lint.lean/.log`: compiler exit 0, silent selected lint, all eight public declaration axiom closures standard3.
- `/tmp/gc_SimplexStrutShortening_body.lean`: one public theorem; SHA256 `17e49c58d6adc3665ac4aa11f7501c379c5fcfd0f5034f9b17de8e08766ddc53`.
- `/tmp/gc_SimplexStrutShortening_agent.lean/.log`: minimal production driver SHA256 `3d0636f580cd66c999208b713d42c3ac8ca0281b97d2c56fac1597747335670b`, compiler exit 0, empty log.
- `/tmp/gc_SimplexStrutShortening_lint.lean/.log`: initial grouped-universe version passed; final independent-universe theorem was rechecked with the concrete regression in `/tmp/gc_simplex_shortening_review_lint.lean/.log`, compiler exit 0, silent selected lint, both theorem axiom closures standard3.
- `/tmp/gc_regular_simplex_review_body.lean`: six concrete regression theorems: exact rank-one angle π; rank-two off-diagonal inner product −1/2; rank-two unit norm; actual rank-two family inside Eucl2; the ambient-dimension-three quantitative bound; and zero-dimensional definition evaluation showing why the positive-dimension hypothesis is required.
- `/tmp/gc_simplex_shortening_review_body.lean`: original-input regression uses source ℝ, apex 7, ORIGINAL paths `7+s` and `7−s`, available radii 2 and 3, actual Eucl1 unit-direction density proved exhaustively, actual hyperbolic angle limits 0/π, and common-shortening cap 1/100. It assumes no strut existence or angle-margin conclusion.

All implementation and checks are temporary. No repository files, manifests, shared build artifacts, or reference sources were modified.

Final frozen regression hashes:

- `/tmp/gc_regular_simplex_review_body.lean`: `1be4474dc2d9ed11fdf8d95da35b131b78b14de4ed57fc7e79d24905b9f7d85b`.
- `/tmp/gc_regular_simplex_review_agent.lean`: `e67a55e8f23340ab04e8563c062f8968f7333b68723398b621666edb0435f869`.
- `/tmp/gc_regular_simplex_review_lint.lean/.log`: exit 0, all six regression declarations standard3, silent selected lint.
- `/tmp/gc_simplex_shortening_review_body.lean`: `0c95c6c2f77b2becdd681466f0d802543e1cb48db616da45a2394fb1a737d843`.
- `/tmp/gc_simplex_shortening_review_agent.lean`: `f90cf22035ddd6456d38607d65e9dd375ae19d78fab398946ae81150794dc6a8`.
- `/tmp/gc_simplex_shortening_review_lint.lean/.log`: final independent-universe theorem plus actual regression, exit 0, standard3, silent selected lint.
