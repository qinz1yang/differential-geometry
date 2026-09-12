# `UniversalPrecompactness.lean`

`thm:ksol-universal-precompactness` (`master05a.tex` L30455).

## Scope

Sources are three-dimensional ancient `κ_i`-solutions with their *own* constants
`κ_i > 0`, none of them a shrinking spherical space form flow. Each is
normalized at a chosen `(x_i, t_i) ∈ M_i × (-∞,0]` by
`eq:ksol-universal-normalized-sequence`,
`ĝ_i(s) = Q_i g_i(t_i + s/Q_i)` with `Q_i = R_{g_i}(x_i,t_i)`. The scale is the
actual scalar curvature there; its positivity is `lem:ksol-scalar-positive`
(`ancientKappa_scalar_pos`), not an added hypothesis.

`thm:ksol-universal-kappa-gap` (`ancientKappaThree_universal_kappa_gap`) then
makes every normalized term an ancient `κ₀`-solution for the single
flow-independent `universalKappaConstant` of `eq:ksol-universal-kappa0`, and
`thm:ksol-fixed-kappa-compactness` applies with that fixed constant. The limit
is allowed to be spherical (non-roundness is not closed under pointed
convergence); noncompactness of all sources is passed to the limit by
`klim_pointedLimit_noncompact`.

## Public declarations

| name | content |
| --- | --- |
| `universalNormalizedFlow` | `eq:ksol-universal-normalized-sequence` for one flow at one spacetime point |
| `universalNormalizedFlow_isAncientKappaSolution` | the normalization keeps `IsAncientKappaSolution` with the same `κ` |
| `universalNormalizedFlow_scalarAtBase` | the normalization has base scalar curvature one |
| `universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow` | non-roundness is inherited, by `round_of_curvatureNormalizedFlow_round` |
| `universalNormalizedFlow_isAncientKappaSolution_universal` | the normalization is an ancient `universalKappaConstant`-solution |
| `universalNormalizedSeq` | the normalized sequence as a `PointedFlowSeq` |
| `exists_universal_precompactness` | the theorem |

`threeSpace_finrank : Module.finrank ℝ ThreeSpace = 3` is `private`.

## Route notes

* Non-roundness is stated on the *sources* `X i`, exactly the form consumed by
  `ancientKappaThree_terminal_universal_noncollapsed` /
  `ancientKappaThree_universal_kappa_gap`, and is transported to the
  normalizations by the time-translation rigidity
  `round_of_curvatureNormalizedFlow_round` (contrapositive). It does not appear
  in the conclusion.
* `universalNormalizedFlow` uses `hF.carrier_eq` / `hF.regular_eq` where
  `round_of_curvatureNormalizedFlow_round` writes `rfl rfl`; definitional proof
  irrelevance makes these interchangeable, so no bridge lemma is needed.
* `curvatureNormalizedFlow` keeps `M := F.M` with the same topology, so the
  connectedness and noncompactness hypotheses about the sources transfer to the
  normalized sequence definitionally (`(hX i).connected` is accepted where
  `ConnectedSpace ((universalNormalizedSeq …).term i).M` is expected).
* `t i ≤ 0` is accepted where `t i ∈ ancientTimeInterval.carrier` is expected
  (`ancientTimeInterval_carrier` is `rfl` and `Set.Iic` membership unfolds).
* The statement uses `Phi.atTime (X := universalNormalizedSeq X hX ht p)
  (L := L) s`; see `AncientKappaFixedCompactness.md` for why the implicit
  sequence must be given.

## Independence from `AncientKappaFixedCompactness.lean`

This file does **not** import `AncientKappaFixedCompactness.lean`: that module is
new and unregistered, so no `.olean` exists for it and `lake env lean` could not
load it. It therefore calls `exists_fixed_kappa_compactness` directly, with the
same three-line `ancientKappaThree_toKLim` bridge. The two files share no
declaration name, so both can be registered together; once
`AncientKappaFixedCompactness` has an artifact, the three lines here can be
replaced by `exists_ancientKappa_fixed_kappa_compactness` without changing the
statement.

## Verification

```
LEAN_NUM_THREADS=2 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/UniversalPrecompactness.lean
```

Empty output, exit 0, about 21 s (2026-09-11).

## Inherited admissions

`#print axioms` reports `propext, sorryAx, Classical.choice, Quot.sound` for all
seven public declarations — including the definitions, because the normalization
scale uses `ancientKappa_scalar_pos`, which inherits `complete_forward_flatness`.

A transitive scan of the proof term of `exists_universal_precompactness` (92333
reachable constants) finds exactly 28 declarations whose own value uses
`sorryAx`, all in namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions`: the 24 listed in
`AncientKappaFixedCompactness.md` plus the four contributed by the universal
gap chain,

```
ancientKappaThree_reducedCost_two_point
ancient_reducedVolume_antitone
exists_samePole_normalized_asymptotic_shrinker
normalized_nonflat_three_shrinker_round_or_mass
```

No new admission is introduced here. The only other explicit hypothesis is
`hnoEmbedding`, the nonembedding obstruction inherited from
`thm:ksol-three-dimensional-KLim-bounded`.

## Out of scope tonight

`cor:ksol-scalar-scale-comparison` (L30540) and
`thm:ksol-universal-derivative-estimates` are not started: the derivative
estimates need the jet-compactness argument on top of this theorem.
