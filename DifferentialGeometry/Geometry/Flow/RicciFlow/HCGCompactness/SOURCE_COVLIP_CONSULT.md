# GPT Pro consultation: constants-first whole-source covariant bounds

## Implementation status (2026-07-22)

The consultation selected **Route A: explicit numeric witnesses**.  The hypotheses were
confirmed mathematically sufficient; the defect is witness quantifier placement, not missing
geometry.  The route is now active and must resume from this checklist:

- [x] Gate 0: `SourceCovLip.covRic0_le` and the `q = 0` branch are focused-green.
- [x] Gate 1: `AkMFold.claim1Const`, nonnegativity, `claim1_abstract_bound`, and
  `claim1_bound` are focused+exact green; legacy APIs are wrappers.
- [x] Gate 2: `RicBoundClaims.claim1_LC_bound`, `claim2Const/spec`,
  `claim2_component_bound`, `mixedDescentConst`, `mixed_descent_bound`, `aNConst`, and
  `aN_component_bound` are focused+exact green.
- [x] Gate 3: `RicTowerCoeffs`, fixed `perDomain_bound`, and pointwise
  `ric_tower_on` are focused-green and exact-current.
- [x] Gate 4: the sequence/window `ric_bound_field_on` wrapper and
  `covOrderBound_stage_on` are focused-green and exact-current.
- [x] Gate 5: the positive-order `SourceCovLip.hcore` strong induction is
  sorry-free, focused-green, and exact-green (`4067/4067`).

Do not restart the route audit or revive the compact finite-subcover witness
assembly. The Route A theorem proof and its dedicated explicit-witness
machinery are 100% and exact-current. The separate
solution-generated `ShiCutoffData` frontier is unchanged. The whole HCG
compactness project remains about 60% complete.

## Repository context

- Repository: `https://github.com/liao9yuan/differential-geometry`
- Working branch: `codex/short-time-existence-align`
- Checked-out baseline commit: `373b2140568572659971e972d70d87f4904b2d13`
- Lean/Mathlib: pinned Lean `v4.29.0`

This is the short-time-existence alignment branch, but the requested review is
for the disjoint HCG compactness producer below. The live working tree has
uncommitted source changes that are not visible from GitHub; treat the
declarations and status described here as authoritative where they differ from
the remote commit.

## Target

The target is

```lean
HCGCompactness.srcCovLip_of_soln
```

in

```text
DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/SourceCovLip.lean
```

It must construct `SrcCovLipData` for pulled-back Ricci flows on varying,
possibly noncompact source manifolds. For each order `q`, both output constants
must be chosen before the source index `k`:

```lean
forall q, exists Cq Lq, 0 <= Cq /\ 0 <= Lq /\
  (forall k t y, metricCovDerivNorm q (g k t) (gRef k) y <= Cq) /\
  (forall k t y,
    sqrt (normSq0S (gRef k) y (q + 2)
      ((-2) • nablaRicReal (g k) (gRef k) q 0 t y)) <= Lq)
```

Inputs are already constants-first:

1. one `Bmax >= 1` giving whole-source metric equivalence for every `k,t`;
2. for each `N`, one `KShi >= 0` giving whole-source moving Shi bounds through
   order `N` for every `k,t`;
3. for each `q`, one initial whole-source `metricCovDerivNorm q` bound before
   `k`;
4. the existing pulled-back Ricci-flow solution/evolution API.

No compactness, bounded-volume, injectivity-radius, or new endpoint assumption
may be added.

## Checked progress

The outer time-Lipschitz assembly is already checked. The order-zero joint core
is now also checked by the new theorem

```lean
covRic0_le
```

using the explicit existing `covNorm0_le`, metric norm comparison,
`nablaRicReal_normSq`, and the order-zero moving Shi bound. Thus the only
remaining `sorry` is under the branch `q >= 1`.

## Exact obstruction in the existing route

The compact-set proof lives in:

```text
HCGCompactness/AkMFold.lean
HCGCompactness/RicBoundClaims.lean
HCGCompactness/RicBound.lean
```

Its relevant chain is:

```text
AkMFold.claim1_abstract
  -> AkMFold.claim1
  -> RicBoundClaims.claim1_LC
  -> RicBoundClaims.claim2_component
  -> RicBoundClaims.mixed_descent
  -> RicBoundClaims.aN_component
  -> RicBound.perDomain
  -> RicBound.ric_tower_const
  -> RicBound.ric_bound_field
  -> RicBound.covOrderBound_stage
```

`claim1_abstract` actually constructs a numeric recursive witness from
`m,C0,KR,K`. `claim2Double` is already pure numeric, and `mixed_descent` writes
an explicit numeric witness. Nevertheless, the public existential witnesses
of `claim1_LC`, `claim2_component`, `aN_component`, and `perDomain` occur after
the manifold, reference metric, local frame, and frame domain arguments.

`ric_tower_const` therefore chooses potentially different constants for each
good-frame domain and combines them using a finite subcover of a compact set.
For `SourceDomain Phi k`, neither the whole source nor the family over `k` has
such a finite cover. Applying the compact theorem after fixing `k` has the
wrong quantifier order, and subsequence extraction cannot manufacture a
positive uniform bound.

The issue is stronger than proof irrelevance around a frame: even the manifold
type `SourceDomain Phi k` varies with `k`, so a witness selected after the
manifold argument is not usable as a common source constant.

## Candidate routes

### Route A: expose genuinely numeric constants

Refactor the existing component proof so its constants depend only on

```text
q, dim(E), Bmax, lower-order Cg, KShi
```

and not on the manifold, reference metric, frame, center, or frame domain.
Conceptually:

```text
claim1Const
  -> claim1_LC with a fixed numeric witness
  -> claim2Const / mixedDescentConst
  -> aNConst
  -> perDomain with the same witness for every good frame
  -> ric_tower_univ (pointwise good frame, no finite subcover)
  -> global covariant Gronwall induction
  -> srcCovLip_of_soln
```

Old existential APIs should remain as corollaries where downstream callers use
them.

### Route B: invariant connection-difference inequality

Avoid local-frame witness selection by proving directly, in tensor norms, that
the fixed-reference Ricci tower is bounded linearly by the top
fixed-reference metric derivative plus lower-order constants and the moving
Shi bound. Then feed that bound into the already checked
`metricCovOrderWindow_of_evolution` induction.

This is mathematically cleaner if the current tensor API is sufficient, but it
must not create several new algebraic frontiers merely to avoid the component
code that is already checked.

### Possible staged route

One could first close `q = 1` with the zeroth connection-difference/Koszul
estimate, then generalize. Please say whether this is useful reusable progress
or merely duplicates the eventual arbitrary-order proof.

## Questions

1. Are the stated inputs mathematically sufficient for one global constant at
   every finite order on every whole source, without any spatial compactness?
   If not, give the sharp counterexample or the exact missing hypothesis.
2. Which route is smallest and safest in this Lean codebase: explicit numeric
   witnesses from the existing component proof, or a new invariant tensor-norm
   proof?
3. For the recommended route, give the exact smallest theorem/definition
   signatures, their owning files, and their dependency order.
4. In Route A, should `claim1Const` be an explicit well-founded recursive
   function, or should the theorem quantify all manifold/frame data inside a
   constants-first existential? Account for the fact that the manifold type
   varies with `k`.
5. Can `claim2Double` and the explicit body of `mixed_descent` be lifted without
   reproving their geometric bodies? Give the clean compatibility-corollary
   pattern for the existing APIs.
6. How should the pointwise good-frame proof eliminate
   `ric_tower_const`'s finite subcover while retaining one common tensor-norm
   constant?
7. Give feasibility gates and a stop condition. In particular, identify the
   first declaration that must check before changing `srcCovLip_of_soln`.

## Constraints on the answer

- Do not propose a per-`k` compact exhaustion, finite minimum, diagonal
  subsequence, or shrinking domain: all have the wrong quantifier order.
- Do not add a wrapper hypothesis equivalent to the desired positive-order
  bound.
- Preserve one canonical API per concept and keep reusable numeric/algebraic
  lemmas in the lowest natural module.
- Prefer a precise `sorry` frontier over an apparently green theorem that moves
  the same mathematics into a new assumption.
- Separate mathematical feasibility from Lean/API effort, and call out any
  expected performance or universe/typeclass risk.
