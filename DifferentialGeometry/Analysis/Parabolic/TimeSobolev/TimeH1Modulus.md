# TimeH1Modulus.lean — the `√t` Hölder-½ time modulus

Executor session (Opus 4.8) on worktree `C:/Users/liao9/.codex/worktrees/e87b/...`,
branch `codex/analytic-producers-e87b` @ `922dbc4ac`.  This is **ruling item 1**
of the six-item R1τ frontier in
`Geometry/Flow/RicciFlow/ShortTime/UNIF_N_PRO_RULING.md` — the generic `timeH1`
`√t`-modulus lemma.  It is consumed later by **item 5** (the fixed-horizon
representative), and replaces the naked `ContinuousWithinAt` δ used at
`Analysis/Spectral/Intrinsic/DeTurck/MaxRegSolutionJointlySmooth.lean:1138`.

## What was delivered

Two public theorems, in namespace `DifferentialGeometry.Analysis.Parabolic.TimeSobolev`:

1. `integral_norm_Icc_le (f : timeL2 X T) (ht : t ∈ Icc 0 T) :`
   `∫ s in Icc 0 t, ‖f s‖ ≤ √t · ‖f‖`
   — the sharp-horizon (`√t`) companion of the existing whole-horizon (`√T`)
   `TimeSobolev.integral_norm_le` (`BochnerL2.lean:278`).

2. `timeH1.norm_toFun_sub_init_le (u : timeH1 X T) (ht : t ∈ Icc 0 T) :`
   `‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖`
   — the main deliverable: the explicit ½-Hölder modulus.  Stated in the
   carrier's own currency (`u.init` = value at 0 = `trace0 X T u`; `u.deriv` =
   the time-`L²([0,T];X)` field = `timeDeriv X T u`; both defeq via the `rfl`
   simp lemmas `trace0_apply`/`timeDeriv_apply`), matching the ruling's item-1
   wording exactly.  Weakest carrier hypotheses: only `t ∈ Icc 0 T` (the carrier
   already fixes `X` a real Hilbert space).

## Route (feasible, implemented)

Carrier facts reused from `TimeH1.lean` (no re-derivation of absolute
continuity — the FTC increment already exists):
- `toFun_apply` + `abel` gives `u.toFun t − u.init = ∫ s in 0..t, u.deriv s`
  (equivalently the committed `toFun_sub_toFun` with `t₀ = 0`, `toFun_zero`).
- `intervalIntegral.integral_of_le` (`0 ≤ t`) → integral over `Ioc 0 t`.
- `norm_integral_le_integral_norm` → `∫_{Ioc 0 t} ‖deriv‖`.
- `setIntegral_mono_set` (`Ioc 0 t ⊆ Icc 0 t`) → `∫_{Icc 0 t} ‖deriv‖`.
- `integral_norm_Icc_le` → `√t · ‖deriv‖`.

`integral_norm_Icc_le` is a faithful copy of `BochnerL2.integral_norm_le` but on
the **sub-measure** `timeMeasure t`: `L¹ ⊆ L²` Hölder nesting
(`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, total mass `= t`) plus one
monotonicity step `eLpNorm ⇑f 2 (timeMeasure t) ≤ eLpNorm ⇑f 2 (timeMeasure T)`
(`eLpNorm_mono_measure` with `timeMeasure t ≤ timeMeasure T` from
`Measure.restrict_mono`).  The `√t` (not `√T`) is exactly what makes this a
modulus that vanishes as `t → 0` — the whole point of item 1.

## Reuse audit

No existing `√t` modulus anywhere (grepped TimeSobolev + ShortTime): `TimeH1.lean`
has only `norm_toFun_le` (bounds `‖toFun t‖`, not the difference, and with `√T`)
and `norm_toFun_le_norm`.  So this is genuinely new, not a duplicate.  Canonical
home of `integral_norm_Icc_le` would be `BochnerL2.lean` next to `integral_norm_le`;
kept in this additive leaf per the dispatch guardrail (do not edit committed-clean
tracked files — `TimeH1.lean`/`BochnerL2.lean` are both clean).

## Verification status

**GREEN — verified sorry-free (2026-07-23).**  `scripts/lake-locked.ps1` is
absent in this worktree, so verification was the CLAUDE.md-sanctioned read-only
form `LEAN_NUM_THREADS=4 lake env lean …/TimeH1Modulus.lean` (imports built;
fresh file ⟹ no stale-olean false-green risk).  Result: exit 0, no errors, no
warnings.  `#print axioms` on both theorems =
`[propext, Classical.choice, Quot.sound]` (the sanctioned trio; no `sorryAx`, no
extra axioms).  Concurrency note: a fully quiet window was caught by the poll
waiter, but 2–3 Codex `lean.exe` had respawned by the time each check launched,
so both checks ran with mild concurrency — acceptable because concurrency risks
only false *failures* (thread exhaustion), never false passes; both runs
produced clean, meaningful output.  Temporary `#print axioms` lines were stripped
after the green.

All Mathlib primitives were also confirmed present with matching signatures
against `.lake/packages/mathlib` before writing: `eLpNorm_mono_measure (f) (ν ≤ μ)`,
`AEStronglyMeasurable.mono_measure`, `Ne.lt_top`, `Lp.eLpNorm_ne_top`,
`ENNReal.rpow_ne_top_of_nonneg`, `ENNReal.toReal_mono`, `setIntegral_mono_set`,
`intervalIntegral.integral_of_le`.  The proof mirrors the already-verified
`integral_norm_le`/`norm_toFun_le` in the same file family.

## Honest accounting

(N) `ricci_flow_unif_existence` remains **0%** (unstated in Lean terms; this is
pure supporting infrastructure).  This brick is 1 of 6 R1τ ruling items and is
the shallowest (generic functional-analytic modulus, no geometry).  It does not
by itself move (N); item 2 (the decisive second-order tame estimate) is the
route test, and items 3–6 remain.
