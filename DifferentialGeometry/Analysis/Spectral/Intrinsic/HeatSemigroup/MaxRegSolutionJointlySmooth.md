# MaxRegSolutionJointlySmooth.md

Same-name note for
`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean`.

Scope of this session: **R1τ ruling item 5 — the FIXED-HORIZON representative**
(`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`).  Additive
sibling; the existing public theorem
`maxreg_solution_jointly_smooth_representative_of_nemytskii` (:957) is left
UNTOUCHED.

## Position in the project

- End goal: fill the single `sorry` of black box (N)
  `ricci_flow_unif_existence`.  Route ratified = R1τ (see
  `ShortTime/UNIF_N_PRO_RULING.md`).  Six-item lemma frontier; items 1 ✓, 3 ✓,
  4 ✓ (verified green by the planner); item 2 IN FLIGHT (deTurckLie/lieCorr0
  constituents, a different executor's lane); items 5, 6 open.
- This session = item 5.  (N) itself remains 0% (its `sorry` untouched); item 5
  is machinery.

## The three existential shrinks of the existing representative (:957)

Witness horizon (:1141): `T₁ = min (min (min T (d/2)) d₂) d₂F`.  Component map,
with quantitative-floor verdict:

| component | where | what it protects | quantitative-floor verdict |
| --- | --- | --- | --- |
| `d` | :1138 δ from `Metric.continuousWithinAt_iff` of `timeH1.toFun u` at `t=0`, at ε = `1/(2C)` | fibre-operator smallness `gFibreOpBound (ccTensorBilinSymm g₀ (F t)) (1/2)` on `[0,T₁)` (needs `‖u(t)‖_{Hᵃ} ≤ 1/(2C)`) | **DERIVABLE** — replace the qualitative δ by item-1 `timeH1.norm_toFun_sub_init_le`: `‖u.toFun t − u.init‖ ≤ √t·‖u.deriv‖`, with `u.init = 0` (from `htrace`).  Floor: `√T·‖u.deriv‖ ≤ 1/(2C)` (equiv. `T ≤ 1/(4·C²·‖u.deriv‖²)`).  `C` = the lossy fibre constant of `ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy g₀ a` (`SobolevNonlinearityExistence.lean:1271`). |
| `d₂` | :1140 from `hHorizon` existential input | `H^{a+2}` realizability ball `‖smoothCcToTensorHs g₀ (a+2) (F t)‖ ≤ R₀` on `[0,T₁)` — the ruling's "wrong-topology identity guard" | **NO intrinsic floor at this layer.**  It is the `H^{a+2}`-ball admissibility.  For the fixed-horizon variant, take it as a **full-interval hypothesis** on `[0,T]` (honest input; the class-uniform packet item 6 must supply it).  The DEEP clean resolution (ruling item 5 proper) replaces the `H^{a+2}` ball by the item-3 `H^{a+1}` cutoff + item-4 tame Nemytskii — MULTI-SESSION and item-2-dependent; NOT this session. |
| `d₂F` | :979 existential input `{d₂F} (hd₂F_pos) (hd₂F_le)` | forcing / mode-mass control (`hf_mass`, `hf_id` on `[0,d₂F]`, `hForceRepr_fam` needs `T₁ ≤ d₂F`) | **No floor needed** — set `d₂F := T` (full interval).  Just an input-choice, folds away. |

Conclusion: the fixed-horizon variant returns EXACTLY `T` by (i) the √t-modulus
floor for `d`, (ii) full-interval `H^{a+2}`-ball admissibility as an honest
hypothesis for `d₂`, (iii) `d₂F := T`.

## Design — `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`

Additive sibling in the SAME file (file goes 1286 → ~1420 lines, under the 3000
cap).  Name per ruling item 5 (line 69 of the ruling); parallels the existing
`_of_nemytskii` public name (grandfathered long name, planner-chosen).

Reuses the two big private helpers verbatim at `T₁ = d₂F = T`:
`realizedFamily_flowDeriv_of_repr` (:121) and
`realizedFamily_jointChartGramSmooth` (:475).

Hypotheses (vs the existing theorem):
- DROP `Nfun` (unused in the existing body — verified by grep; only the
  signature mentions it).
- DROP `{d₂F} (hd₂F_pos) (hd₂F_le)`; use `T` throughout.
- DROP `hHorizon` (existential `d₂`); ADD full-interval
  `hball_full : ∀ t ∈ Icc 0 T, ∀ S, S.toL2 = [u(t) realized in Hᵃ] →
    ‖smoothCcToTensorHs g₀ (a+2) S‖ ≤ R₀`.
- ADD the lossy fibre constant as explicit inputs (so the floor is stated in
  named constants, and item 6 can thread a class-uniform `C`):
  `(C : ℝ) (hC_pos : 0 < C)
   (hC : ∀ S, gFibreOpBound g₀ (ccTensorBilinSymm g₀ S) (C * ‖smoothCcToTensorHs g₀ (a:ℝ) S‖))`
  — exactly the output shape of `ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy`.
- ADD the floor `hfloor : Real.sqrt T * ‖u.deriv‖ ≤ 1 / (2 * C)`.
- `hf_mass`, `hf_id` restated on `Icc 0 T`.
- `hForceRepr` = the existing `hForceRepr_fam` SPECIALIZED to `T₁ = T`
  (drop the `{T₁} hT₁_pos hT₁_le hT₁_le_d2F` prefix; pins on `Icc 0 T`, ball on
  `Ico 0 T`).

Conclusion: strip the outer `∃ T₁, 0<T₁ ∧ T₁≤T ∧`; the package is stated on the
GIVEN `T` (pin on `Icc 0 T`, flow-deriv on `Ico 0 T`, `JointChartGramSmooth T`).

Only novel proof content: `hF_small` via the √t-modulus (replaces existing
:1133–:1206 continuity dance):
```
‖smoothCcToTensorHs g₀ a (Fdef t)‖ = ‖u.toFun t‖ = ‖u.toFun t − u.init‖
  ≤ √t·‖u.deriv‖ ≤ √T·‖u.deriv‖ ≤ 1/(2C)   -- last step = hfloor
```
then `hC (Fdef t) x v w` + `C·‖…‖ ≤ 1/2` closes fibre smallness (mirrors
:1184–:1199 verbatim, only `hnorm_le` changes source).

Everything else (F-construction via `duhamel_into_all_tensorHs` +
`spectralSmoothRealizesAsSmooth_holds`; `hF_pin`; `hcoeff`; `hmodemass`; the two
helper calls; final assembly) is the existing body with `T₁,d₂F ↦ T`.

Import ADDED: `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Modulus`
(item-1 module; not previously in the transitive closure — verified by grep).

### Duplication note (deliberate)

The F-construction (~55 lines, existing :1049–:1128) is duplicated into the
sibling rather than factored, to keep the verified-green existing theorem at
ZERO risk (additive-only).  A future simplification pass (once both are settled)
can extract a private `forcingRealize_pin` helper and retrofit both — recorded
here per CLAUDE.md "prove first, factor after".

## Scope honesty

This delivers the MISSION's focused item-5 layer (√t-modulus fixed-horizon,
`H^{a+2}`-ball admissibility as honest full-interval input).  It is NOT the
ruling's deepest item-5 (which swaps the `H^{a+2}` ball for the item-3 `H^{a+1}`
cutoff and consumes item-4's tame Nemytskii forcing map) — that is
multi-session and blocked on item 2.  The `d₂` verdict above is the honest
boundary: no floor exists in the `H^{a+2}` topology; the architectural fix is
the lower-topology cutoff, deferred.

## Implemented (this session)

- Import ADDED: `...TimeSobolev.TimeH1Modulus` (line 21).
- New public theorem
  `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
  (after the existing `_of_nemytskii`, before the closing `end`), under
  `set_option linter.unusedVariables false in` (matches the file's pattern for
  parallel-API hypotheses such as `ha_eq`).
- Existing `_of_nemytskii` LEFT UNTOUCHED (zero risk).
- Hypothesis order: `…, hf_id, C, hC_pos, hC, hfloor, …` — `hfloor` (which reads
  `u.deriv`) placed AFTER `hf_id` so `u`'s spectral space `tensorHs g₀ 0 2 a` is
  fixed by `hf_id` before `u.deriv` is elaborated.
- Floor hypothesis: `hfloor : Real.sqrt T * ‖u.deriv‖ ≤ 1 / (2 * C)` (equivalent
  closed form `T ≤ 1/(4·C²·‖u.deriv‖²)`).  `C, hC_pos, hC` are the verbatim
  output shape of `ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy g₀ a`
  (`SobolevNonlinearityExistence.lean:1271`), taken as explicit inputs so item-6
  can thread a class-uniform `C`.
- Reuses `realizedFamily_flowDeriv_of_repr` and
  `realizedFamily_jointChartGramSmooth` at `T₁ = d₂F = T` (the `_le` args become
  `le_refl T`).

## Build-environment finding (buildDir olean gaps)

The buildDir `C:/dgb2/e87b/lib/lean` was only PARTIALLY seeded: the target
module's own olean and several of its imports
(`DeTurckChartRegularityFromJoint`, `MildSolutionTimeH1`, `ForcingTimeBootstrap`,
`SpectralPointwiseFlowDeriv`, …) were absent, so `lake env lean <file>` fails at
import resolution before elaborating.  Fix = `lake build +…MaxRegSolutionJointlySmooth`
(builds the missing deps + elaborates the sibling).  First foreground attempt
timed out at 10 min after building the ShortTime deps; resumed in background.
`TimeH1Modulus.olean` (item 1) WAS already present.

## Status — DONE (verified green + axiom-clean)

- `lake build +…MaxRegSolutionJointlySmooth`: "Build completed successfully
  (9581 jobs)", EXIT=0.  Final job `✔ [9581/9581] Built …MaxRegSolutionJointlySmooth`
  (✔, not ⚠) ⟹ ZERO warnings on this module under the authoritative build.
- Axiom audit (direct `lean` binary + full captured `LEAN_PATH`, `#print axioms`
  on the new public theorem): exactly `[propext, Classical.choice, Quot.sound]`.
  Audit line stripped after green.
- The two `unusedSectionVars` warnings that appear ONLY under bare `lean`
  (lines 48/65) are on the PRE-EXISTING private helpers
  `tensorL2_ext_of_tensorL2Coeff_jsmooth` / `ccTensorBilinSymm_zero_apply_jsmooth`
  (shifted +1 by the new import); not this session's code, and not emitted under
  `lake build`'s lakefile options.
- (N) still 0% (its `sorry` untouched).  Ruling scoreboard: items 1 ✓, 3 ✓,
  4 ✓, and now item 5's FIXED-HORIZON layer ✓ (this file); item 2 in flight
  (other executor's LieCorr0 lane); item 6 open.

## Remaining frontier for the FULL clean item 5 (deferred, multi-session)

The delivered variant removes all three shrinks by (i) the √t-modulus floor for
`d`, (ii) a full-interval `H^{a+2}`-ball hypothesis for `d₂`, (iii) `d₂F := T`.
The ruling's DEEPEST item 5 additionally swaps the `H^{a+2}`-ball admissibility
(`hball_full`) for the item-3 `H^{a+1}` cutoff (`LowScaleCutoff.lean`) fed
through the item-4 tame Nemytskii forcing map (`TameNemytskii.lean`), so that
admissibility no longer costs any high-frequency initial regularity.  That
rework needs the item-2 smooth-core tame estimate (IN FLIGHT) and re-plumbs
`Nsec`/`hRepr`/`hForce` through the cutoff — a separate multi-session brick.
Also deferred: extract the shared F-construction into a private
`realizedForcingFamily_pin` and retrofit both representatives (removes the
~55-line duplication; kept inline this session to protect the verified-green
existing theorem).
