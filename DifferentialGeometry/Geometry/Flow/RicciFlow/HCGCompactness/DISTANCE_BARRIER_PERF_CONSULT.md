# Distance-barrier elaboration consultation

I need a repository-specific Lean 4 elaboration/performance diagnosis, not a
new mathematical route.

Repository: https://github.com/liao9yuan/differential-geometry  
Branch: `codex/short-time-existence-align`  
Remote-visible commit: `00de305b01554dbe63df5d5ea2edc78836dea6c5`  
Lean: `v4.29.0`

Important visibility caveat: the remote branch currently points to that commit,
but the relevant changes in

`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/DistanceBarrier.lean`

are uncommitted local changes and are therefore not visible on GitHub. Treat
the architecture and code excerpts below as authoritative; the remote file is
only background.

## Goal

Keep the public theorem `scaledDist_calabiUpperSupport_of_sol` unchanged. It
states that, under a Ricci-flow solution, initial completeness, a closed-slab
curvature bound, positive time, finite nonzero distance, and no additional
geometric assumptions, the rescaled distance

```text
exp (Lambda * t) * d_{g(t)}(O, ·)
```

has a smooth local Calabi upper support with the required value, neighborhood
upper-support inequality, time differentiability, spatial smoothness, gradient
bound, and parabolic lower bound.

Its proof is mathematically assembled and contains no `sorry`, `admit`, or new
axiom. The only blocker is elaboration/kernel-normalization performance in one
private orchestration theorem.

## Current helper architecture

The implementation deliberately separates the mathematics into private
declarations:

- `ScaledDistSupport`: bundles the support function `rho` and exactly the seven
  conclusions later projected by the public theorem: `eq_at`, `upper_nhds`,
  `time_diff`, `space_diff_nhds`, `grad_diff`, `grad_sq`, and `par_lower`.
- `exists_calabi_coeff`: chooses the dimension-normalized Bishop comparison
  coefficient.
- `ricci_quad_of_curv`: turns the scalar curvature-norm bound into a uniform
  quadratic Ricci bound and proves `0 <= Lambda`.
- `CalabiFlowCore`: bundles the unscaled fixed-time Calabi support, broken-path
  time variation, spatial regularity, unit gradient, and Laplacian estimate.
- `calabi_core_of_sol`: constructs `Nonempty CalabiFlowCore` after installing
  the fixed-time Riemannian metric and completeness instances.
- `CalabiFlowCore.scale`: multiplies the unscaled core by `exp (Lambda * t)` and
  returns `Nonempty ScaledDistSupport`.
- `scaled_of_quad`: given the quadratic Ricci bound and completeness of the
  selected time slice, installs the local metric instances, calls the
  fixed-time Calabi producer, and scales the result.

All these declarations elaborate without diagnostics in the current focused
proof loop.

The remaining private orchestration theorem is:

```lean
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem scaledDist_support
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    Nonempty (ScaledDistSupport (I := I) S O T t x d Λ r) := by
  classical
  dsimp only
  obtain ⟨hΛ, hricQuad⟩ :=
    ricci_quad_of_curv (I := I) S hK hcurv
  have hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    complete_of_ricBound
      (I := I) (D := D) (a := 0) (b := T)
        (K := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
        (s := t) S hS hslab hreg hΛ hricQuad hcomplete ht
  exact scaled_of_quad
    (I := I) (D := D) (T := T) (t := t)
      (Λ := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
      S hS O hT hreg hΛ hricQuad hcomplete_t ht htpos x hfinite hOx
```

The public theorem merely calls this private theorem, destructures the bundled
witness, and projects its fields:

```lean
  obtain ⟨h⟩ :=
    scaledDist_support
      (I := I) S hS O hT hslab hreg hcomplete hK hcurv
        ht htpos x hfinite hOx
  exact
    ⟨h.rho, h.eq_at, h.upper_nhds, h.time_diff, h.space_diff_nhds,
      h.grad_diff, h.grad_sq, h.par_lower⟩
```

## Verified failure

`scaledDist_support` deterministically exceeds the heartbeat limit during
`whnf`.

- It fails with the default `200000` heartbeats.
- A separate narrowly scoped test at `500000` heartbeats also fails. The live
  source has been restored to the default setting.
- There is no ordinary theorem-body goal, type mismatch, missing declaration,
  or stale-import diagnostic before the timeout.
- Because this private declaration is never created, the public wrapper
  subsequently cannot use it; that is only a downstream consequence.
- The constituent mathematical helpers listed above elaborate successfully.

The likely expensive term is the interaction among:

- `complete_of_ricBound`;
- its proof-valued `RiemannianMetricComplete` result;
- the induced `CompleteSpace M` instance installed inside `scaled_of_quad`;
- the fixed-time metric-generated `RiemannianBundle`, `PseudoEMetricSpace`, and
  related dependent instances;
- normalization of the large `Nonempty (ScaledDistSupport ...)` expected type.

## Three proof layouts already tried

1. One monolithic proof directly inside the public theorem.
2. A bundled `ScaledDistSupport` wrapper, with separate fixed-time
   `CalabiFlowCore`, `calabi_core_of_sol`, and `CalabiFlowCore.scale`.
3. A further setup split:
   `ricci_quad_of_curv -> complete_of_ricBound -> scaled_of_quad`, leaving
   `scaledDist_support` as only the three-line orchestrator shown above.

The third layout is the current source. Making all important arguments to
`complete_of_ricBound` and `scaled_of_quad` explicit did not remove the `whnf`
timeout.

## Constraints

Please preserve:

- the exact public statement of `scaledDist_calabiUpperSupport_of_sol`;
- all current mathematical hypotheses: do not add completeness at time `t`, an
  injectivity-radius assumption, connectedness, or a new HCG input;
- the single canonical metric/completeness APIs already used;
- the existing fixed-metric Calabi and metric-time-comparison producers.

Private implementation helpers may be refactored, but do not introduce a
parallel public API or move the mathematical frontier into a new assumption.

Please avoid recommending a giant or unlimited heartbeat setting unless you
can explain why no Lean-native elaboration boundary is available. A small,
narrowly scoped increase is acceptable only as a justified last resort.

## Questions

1. What is the most likely source of `whnf` blow-up in this exact proof shape?
2. What is the smallest Lean-native refactor that prevents reduction of the
   large metric-instance/completeness proof term?
3. In Lean 4.29, would one of the following genuinely create the needed
   elaboration boundary, and exactly where should it be placed?
   - an `opaque` private definition/theorem;
   - a small private structure packaging `hΛ`, `hricQuad`, and `hcomplete_t`;
   - an `abstract` block around the completeness proof;
   - an explicitly typed intermediate `have` whose result is consumed by
     `refine`/`apply`;
   - moving the `CompleteSpace` installation outside or inside a different
     helper;
   - changing only the final `exact scaled_of_quad ...` tactic shape.
4. Please provide the smallest concrete Lean patch or proof skeleton you expect
   to compile, including any needed `show`, `change`, `refine`, `apply`, `let`,
   or `have` boundaries.
5. If an opaque boundary cannot help because the timeout happens before
   declaration compilation, explain precisely why and give the next-smallest
   tactic or declaration-level split.

The desired answer is a surgical elaboration fix, not a redesign of the Calabi
argument.
