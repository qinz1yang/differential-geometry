# MovingShiRestrictOpen.lean — the moving-Shi restriction transport

**Goal:** the frontier deferred by Brick 2 of the P4 conv engine — transport
`MovingShiBoundOn` from a metric sequence `gSeq` on `M` to its open restriction
`t ↦ (gSeq i t).restrictOpen U` on an open submanifold `U`. The restriction-analog
of `MovingShiPullback.lean` (which transports along a diffeomorphism `Φ : M ≃ₘ N`).

## Status — DONE, sorry-free, axiom-clean

Targeted build green (3880 jobs); `#print axioms movingShiBoundOn_restrictOpen`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Focused check clean,
no warnings from this file.

## What landed (mirrors `MovingShiPullback.lean` step by step)

- `covDerivOfField_succ_eval` (private) — public re-derivation of the single-`covStep`
  recursion (the pullback file's `covDerivOfField_succ_eval_smooth_slots` is `private`
  there, so it could not be reused). 4-line body: `covDerivOfField_succ` +
  `metricCovDerivStep_apply` + `totalNabla0SFun_apply_section` + `nabla0SFun_eval_smooth_slots`.
- **`covDerivOfField_restrictOpen`** — general base tower naturality under restriction
  (`covDerivOfField (restrictOpen g) A0U a x slots = covDerivOfField g A0M a ↑x slots`,
  with `hA0 : A0U x slots = A0M ↑x slots`). Induction on `a`, mirroring
  `covDerivOfField_pullback`'s `succ` case **but with NO `mfderiv`** — the tangent
  vectors are literally shared. Ambient (`M`) witness sections `X, V` at `↑x` (via
  `exists_eq_at_gen`), U-restricted by `restrictOpenTangentSection`. Leading-slot term:
  `extDerivFun_restrictOpen` (banked, `OpenSubtypeNaturality`). Connection corrections:
  `metricCov_restrictOpen_globalSection` (banked). No `pushFwdSection`, no `metricCov_pullback`.
- `ricciSection_restrictOpen` — Ricci base: both sides `→ ricciTensor` via
  `ricciSection_eq_ricciTensor`, then Brick-1 `ricciTensor_restrictOpen`.
- `covDerivOfField_apply_eq_iterCov'` (private) — local copy of MovingShiPullback's
  `covDerivOfField_apply_eq_iterCov` (avoids a cross-file dependency; `covDerivOfField_eq_iterCov` + `rfl`).
- **`ricCovTower_restrictOpen`** — slot-wise tower naturality (`... s x slots = ... s ↑x slots`),
  reindexed to the `iterCov`/`ricCovTower` `(2+s)` indexing.
- `ricCovTower_normSq0S_restrictOpen` — tensor-level `ricCovTower_restrictOpen`
  (`ext slots`) fed to banked `normSq0S_restrictOpen_apply`.
- **`movingShiBoundOn_restrictOpen`** (endpoint) — `MovingShiBoundOn U₀ … gSeq …` on `M`
  ⟹ `MovingShiBoundOn V … (fun i t => (gSeq i t).restrictOpen U) …` on `V ⊆ U` with
  `hV : ∀ x ∈ V, ↑x ∈ U₀`. Per-point via `ricCovTower_normSq0S_restrictOpen` + `hShi`.

## TangentSpace-flavor gotchas (all hit; all in SolutionRestrictOpen.md's warning)

`x : U` vs `↑x : M` give separately-tracked-but-defeq `TangentSpace I x` / `TangentSpace I ↑x`.
A `vec2`/`slots`/composition term's flavor is pinned by the expected argument type at each
site, so `rw` across flavors fails ("did not find pattern"). Fixes used:

- **`ricciSection_restrictOpen`**: proving `slots = vec2 (slots 0)(slots 1)` and `rw`-ing it into
  BOTH sides at once fails (each `ricciSection_eq_ricciTensor` has its `vec2` at a different
  flavor). Split into two per-flavor `have hLHS`/`hRHS`, each `rw [hvec]; exact …` at its own flavor.
- **connection sum** (`covDerivOfField_restrictOpen` succ): `simpa […] using hcov'` over-normalized
  `covL`'s `fun y:U => VU p y` to `fun y => (V p) ↑y` while leaving `hcov'`'s
  `restrictOpenTangentField U (fun y => (V p) y)` — mismatch. Fix: `set covL/covR with …_def`,
  then `rw [hcovL_def, hcovR_def]; rw [hXU]; exact hcov'` (don't simp the connection args away).
  The slot-update transport is a `calc` (`ih` then `congrArg _ hslots`), NOT `rw [hih, hslots]`.
- **`Fin.cons` reassembly**: `rw [← hcons, ← hconsM]` picks the wrong `slots` occurrence /
  flavor. Fix: `rw [hcons, hconsM] at hsmooth; exact hsmooth` (rewrite the hypothesis, not the goal).
- **`ricCovTower_restrictOpen` acEquiv-cancel**: `rw [e1]` (with `e1 : (slots∘e.symm)∘e = slots`
  built at U-flavor) will NOT fire on `hrestrict`'s M-flavored RHS occurrence, and
  `simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]` also doesn't match
  under the `⇑` coercions. Fix: unfold `ricCovTower`→`iterCov` implicitly (defeq) and
  `convert hrestrict using 2 <;> (funext i; simp only [Function.comp_apply, Equiv.symm_apply_apply])`.
  `convert` descends up to defeq, sidestepping the flavor of the bare `slots`. (A leading
  `show iterCov … = iterCov …` is unnecessary AND trips `linter.style.showTactic` — dropped it.)

## Reused banked bricks (no new curvature API needed)

`extDerivFun_restrictOpen`, `metricCov_restrictOpen_globalSection`, `restrictOpenTangentSection`(`_apply`)
(`Curvature/OpenSubtypeNaturality.lean`); `ricciSection_eq_ricciTensor`, `covDerivOfField_pullback`
infra publicity (`MetricCovDerivPullback.lean`); `ricciTensor_restrictOpen` (Brick 1,
`SolutionRestrictOpen.lean`); `normSq0S_restrictOpen_apply` (`MetricDerivNormRestrict.lean`);
`covDerivOfField_succ`/`metricCovDerivStep_apply`/`covDerivOfField_eq_iterCov`
(`MetricCovDerivLinear`/`MetricCovDerivArityBridge`); `nabla0SFun_eval_smooth_slots`/
`totalNabla0SFun_apply_section` (Tensor layer); `tensor0SSpace_ext` (Tensor `Defs`).

The `SourceDomainFlow.md` prediction was accurate: no missing curvature-restriction API —
the banked Rm04/LC/metricCov/normSq0S restriction bricks + `extDerivFun_restrictOpen` were
exactly enough. The tower induction is the only genuine work; it is a routine (no-`mfderiv`)
simplification of the pullback induction.

## Consumption

`movingShiBoundOn_restrictOpen` is the restriction half of the Brick-2 cited-input transport:
it composes with `movingShiBoundOn_pullback` (P1.3, `MovingShiPullback.lean`) to land the
moving-Shi bound on the recentered source flows (`sourceFlow`, `SourceDomainFlow.lean`).
