# TransverseCrossingPath

Label: `lem:scn-good-point-buffered-canonical`, item 2, last clause (`master05b.tex`, the
"replacing only the pieces inside the buffered core by axial arcs" paragraph). New leaf,
Chapter25 worker W6; not yet registered in `DifferentialGeometry.lean` (reviewer's job).
Continues `NeckArmNoReturn` (worker W2), whose two-arm no-return conclusion is the exact
hypothesis pair `hano` / `hbno` consumed here.

## What is proved

Given a `StrongNeck S eps x t`, two `MinimizingArm (S.base.metric t) x` with exit points
`a.point s = neck.map (p, k)` and `b.point v = neck.map (q, l)` at axial heights of **opposite
signs** (`k * l < 0`) inside the neck's axial window (`|k|, |l| < eps⁻¹`), and the no-return
clauses for the two tails, there is a `TransversePath (a.point a.length) (b.point b.length)
(neck.map '' (univ ×ˢ {0}))` whose recorded algebraic intersection is `1` when `l > 0` and `-1`
when `l < 0`.

## Construction

`curve τ :=`

* `τ ≤ 1/3`: `a.point (a.length - 3 τ (a.length - s))` — arm `a` backwards from its endpoint
  (`τ = 0`) to its exit point (`τ = 1/3`);
* `1/3 < τ ≤ 2/3`: `neck.map (γ τ, k + (l - k) (3 τ - 1))` with `γ : ℝ → Sphere 2` continuous,
  `γ (1/3) = p`, `γ (2/3) = q`;
* `2/3 < τ`: `b.point (v + (3 τ - 2) (b.length - v))` — arm `b` forwards to its endpoint.

`collar := neck.map`, `central_eq := rfl`, `crossings := {τ₀}` where `τ₀ = (1 + u₀)/3` and `u₀`
is the unique root in `(0,1)` of `k + (l - k) u = 0` (`u₀ = -k/(l-k)` when `k < 0 < l`,
`u₀ = k/(k-l)` when `l < 0 < k`; both are `div_pos` / `div_lt_one` one-liners once the sign case
is split). `deriv (fun w => (collar.symm (curve w)).2) τ₀ = (l - k) * 3 ≠ 0`, whence
`intersection = 1` or `-1` according to the sign of `l - k`, i.e. of `l`.

Key mechanisms:

* **Curve as an opaque local constant.** The three-piece `if`-function is introduced with
  `obtain ⟨c, hcA, hcM, hcB⟩ : ∃ c, … := ⟨fun τ => if … , …⟩` and never unfolded again. The three
  raw clauses are stated on `τ ≤ 1/3`, `1/3 < τ ≤ 2/3`, `2/3 < τ` so each is a bare
  `if_pos`/`if_neg` composition (`exact` absorbs the beta-redex); the closed-interval versions
  `hcleft`/`hcmid`/`hcright` are then derived, the two boundary parameters being handled by
  `ha` / `hb` and the ring identities `3·(1/3) - 1 = 0`, `3·(2/3) - 2 = 0`.
* **Continuity of a minimizing arm.** `MinimizingArm.edistOf_eq` upgrades the recorded
  `metricDistance g (point y) (point z) = |y - z|` to the `ENNReal` identity (the `⊤` branch
  forces `y = z`, where the distance is `0`). Under
  `let : RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩`,
  `let : IsContinuousRiemannianBundle ThreeSpace _ := ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩`,
  `Manifold.locallyCompact_of_finiteDimensional`, `RegularSpace M := inferInstance` and
  `PseudoEMetricSpace.ofRiemannianMetric I3 M`, the arm is `LipschitzOnWith 1` on
  `Icc 0 a.length` (`IsRiemannianManifold.out`), hence `ContinuousOn`. The pseudo-emetric
  topology is defeq to the manifold one by construction of `PseudoEMetricSpace.ofEDistOfTopology`.
* **Gluing.** `Set.Icc_union_Icc_eq_Icc` twice plus `ContinuousOn.union_of_isClosed`, with
  `ContinuousOn.congr` transporting each piece's continuity to `c`.
* **The crossing.** On the middle arc, `neck.map (γ τ, ℓ τ) ∈ neck.map '' (univ ×ˢ {0})` iff
  `ℓ τ = 0`: both points lie in `neck.map.source` (the level `0` slice and the segment between
  `k` and `l` are inside `Ioo (-eps⁻¹) eps⁻¹`), and `PartialEquiv.left_inv'` gives injectivity.
  `ℓ` is injective because `l - k ≠ 0`, so `ℓ τ = 0` forces `τ = τ₀`.
* **Transversality.** `curve = fun w => neck.map (γ w, ℓ w)` on `Ioo (1/3) (2/3)`, which is a
  neighbourhood of `τ₀`, and `collar.symm (neck.map z) = z` on the source, so
  `(fun w => (collar.symm (curve w)).2) =ᶠ[𝓝 τ₀] ℓ` and `Filter.EventuallyEq.deriv_eq` reduces the
  derivative to `HasDerivAt.deriv` for the affine `ℓ`.

## Public declarations

Namespace `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`:

* `MinimizingArm.edistOf_eq`
* `MinimizingArm.continuousOn_point`
* `exists_spherePath`
* `exists_transversePath_of_opposite_arms`
* `exists_transversePath_of_neg_pos`
* `exists_transversePath_of_pos_neg`
* `exists_transversePath_of_far_arms`

## Real dependencies

`NeckArmNoReturn.exists_fixed_neck_two_arm_no_return_depth` (the only Chapter25 producer used),
`Chapter25Geometry.StrongNeck`, `Chapter25Extension.MinimizingArm` / `TransversePath` /
`TransversePath.intersection`, `Geometry/Metric/DistanceScaling.riemannianEDistOf`
(`riemannianEDistOf_self`), Mathlib's `Manifold.PseudoEMetricSpace.ofRiemannianMetric`,
`IsRiemannianManifold.out`, `Manifold.locallyCompact_of_finiteDimensional`,
`isPathConnected_sphere`, `isPathConnected_iff_pathConnectedSpace`, `Path.extend`,
`ContinuousOn.union_of_isClosed`, `Set.Icc_union_Icc_eq_Icc`,
`Filter.EventuallyEq.deriv_eq`, `PartialEquiv.left_inv'`.
Imports: `NeckArmNoReturn` and `Mathlib.Analysis.Normed.Module.Connected` only. Nothing from the
`sorry`-bearing producers of `Chapter25Extension` is used.

## Pitfalls found

* `IsContinuousRiemannianBundle` lives in the root namespace but the instances deriving
  `NormedAddCommGroup (TangentSpace I x)` from `RiemannianBundle` are **scoped to `Bundle`**;
  without `open Bundle` the `let : IsContinuousRiemannianBundle …` line fails with
  `failed to synthesize (x : M) → NormedAddCommGroup (TangentSpace I3 x)`.
  `RiemannianBundle` itself resolves as `Bundle.RiemannianBundle` either way.
* Do not name `riemannianEDist` explicitly in a goal here: with
  `Tensor0SBundle.tangentSpaceNormedAddCommGroup` locally removed, the `ENorm` instance for the
  tangent fibres is not found. Keep the statement in terms of `edist` /
  `riemannianEDistOf` and let `IsRiemannianManifold.out` plus defeq do the bridging
  (`exact le_of_eq (a.edistOf_eq hy hz)`).
* `refine ⟨fun τ => f τ, ?_, ?_⟩` against `∃ γ, … γ (1/3) = p …` leaves the goal as the
  **beta-redex** `(fun τ => f τ) (1/3) = p`, and `rw` cannot see inside it. Prove the endpoint
  equalities as separate `have`s about `f` and close the existential with `exact`.
* Multi-line `nlinarith [ … ]` argument lists must be indented past the tactic's own column or
  the tactic block ends at the newline (`unexpected token '('; expected ']'`). Splitting the
  product hints into `have p1 := mul_nonneg …` lines is both safer and faster.
* `linarith`/`nlinarith` do not see through `(y, w).2`; state the real-number bound first and let
  `exact` absorb the projection (`neck.domain ⟨mem_univ _, hLb τ hτ⟩`).
* `le_or_lt` no longer exists in this Mathlib; use `le_or_gt`. `push_neg` is deprecated in favour
  of `push Not`; `not_lt.mp` / `not_lt.mpr` avoid both.
* `letI` on a `Prop` goal triggers `linter.style.haveILetI`; use `let : T := v`.

## Verification (2026-09-11)

`LEAN_NUM_THREADS=2 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/TransverseCrossingPath.lean`
— exit 0, **empty output**, 35.96 s.

Repeated with the lakefile's own options
(`-DautoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true
-Dlinter.style.header=false -Dlinter.style.longLine=false`) — exit 0, empty output. So the
mathlib standard linter set is clean too (no unused variables, no `unusedTactic`,
no `haveILetI`).

Host note: `lake env lean` on this import cone aborts intermittently at import time with
`failed to read file '….olean'` or a segfault (host memory/mapping glitch, roughly one run in
two while other workers are active). A retry loop with a 45 s pause gets through; each such
abort is a *transient*, not a proof failure.

No `sorry` / `nolint` / `maxHeartbeats` / `maxRecDepth` / `skipKernelTC` / `set_option backward.*`.
No existing file was edited; `DifferentialGeometry.lean` untouched.

### Axiom audit

Run on a scratch copy of this file (in the session scratchpad, outside the tree) with
`#print axioms` appended, so the declarations are freshly elaborated rather than read from an
olean:

```
MinimizingArm.edistOf_eq                    [propext, Classical.choice, Quot.sound]
MinimizingArm.continuousOn_point            [propext, Classical.choice, Quot.sound]
exists_spherePath                           [propext, Classical.choice, Quot.sound]
exists_transversePath_of_opposite_arms      [propext, Classical.choice, Quot.sound]
exists_transversePath_of_neg_pos            [propext, Classical.choice, Quot.sound]
exists_transversePath_of_pos_neg            [propext, Classical.choice, Quot.sound]
exists_transversePath_of_far_arms           [propext, Classical.choice, Quot.sound]
exists_fixed_neck_two_arm_no_return_depth   [propext, Classical.choice, Quot.sound]
```

Standard axioms only, no `sorryAx`, including the one inherited producer. The same scratch run
carried a deliberate `example : (1 : Nat) = 2 := rfl` as a control; it reported the expected type
error, confirming the run really elaborates and reports.

## Next step

`good_point_buffered_canonical` (`Chapter25Extension.lean` L163–190) still needs:

1. the buffered `2*alpha`-neck at `x` itself (`ComparisonComposition.StrongNeck.transport` is the
   candidate producer, modulo its open `hback` field);
2. the **opposite-sign** axial heights `k * l < 0` for the two exiting arms — this leaf takes them
   as a hypothesis; producing them is the "axial coordinate takes opposite signs on the two
   exiting truncated arms" step of the book, which uses the angle hypothesis
   `theta ≤ arccos (…)` and the `Lmin`/`Lmax` window;
3. the neck diameter bound `∀ y z ∈ neck.map '' (univ ×ˢ Icc (-10) 10), metricDistance … ≤ C / √Q`.

Items 2 of the conclusion (the path, its `±1` intersection, and the two no-return clauses) are
delivered in full by `exists_transversePath_of_far_arms` once 2 above is available.

Upstream candidates: `MinimizingArm.edistOf_eq` and `MinimizingArm.continuousOn_point` belong
next to `MinimizingArm` once `Chapter25Extension` stops being a skeleton module;
`exists_spherePath` is generic and belongs with the sphere model in
`Surgery/Topology/LoopModel.lean` or a metric-sphere file.
