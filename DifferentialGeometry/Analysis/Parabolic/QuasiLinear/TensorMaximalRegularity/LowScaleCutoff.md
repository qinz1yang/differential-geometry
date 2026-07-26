# LowScaleCutoff.lean — R1τ ruling item 3 (lower-topology cutoff on H^{a+2})

Executor brick for the R1τ frontier (GPT Pro ruling
`ShortTime/UNIF_N_PRO_RULING.md`, small-lemma frontier **item 3**): the
`H^{a+1}`-controlled scalar cutoff `U ↦ χ(‖ιU‖_{H^{a+1}})·U` acting on an
`H^{a+2}` element, staying an `H^{a+2}` input to the second-order operator.
Gateway to items 4 (tame Nemytskii) and 5 (fixed-horizon representative).

## Design (decided after reconnaissance)

`BallRetraction.lean` (the top-scale radial retraction used by the current
totalisation) is **itself abstract** over a real inner-product space `X`.  The
lower-topology cutoff is its sibling, so it too is written **abstractly**, next
to it, over a continuous linear inclusion

```
ι : X →L[ℝ] H          -- X = H^{a+2} (NormedSpace ℝ), H = H^{a+1} (InnerProductSpace ℝ)
lowScaleCutoff ι ρ U = (min 1 (ρ / ‖ι U‖)) • U
```

The scalar is computed from the **lower** norm `‖ι U‖` but scales the **top**
element `U`.  Everything factors through the ι-commutation identity

```
incl_lowScaleCutoff : ι (lowScaleCutoff ι ρ U) = ballRetraction ρ (ι U)
```

which holds because `ι` is linear and the scalar depends only on `‖ι U‖`
(`simp only [lowScaleCutoff, ballRetraction, map_smul]`).  Through it, (i) and
(iii) transfer verbatim from the corresponding `ballRetraction` facts.

**Why abstract, not concrete tensorHs:** keeps the leaf Codex-independent
(imports only Mathlib + committed-clean `BallRetraction`), mirrors ballRetraction's
own abstraction, and the abstract lemmas apply directly to the concrete `ι` with
zero glue (see instantiation recipe below).  Concrete instantiation belongs with
the consumer (items 4/5), not this leaf.

## The four required lemmas (all proved, no sorry)

- **(i) `lowScaleCutoff_mem_ball`** `(hρ : 0 ≤ ρ)` : `‖ι (lowScaleCutoff ι ρ U)‖ ≤ ρ`.
  Via `incl_lowScaleCutoff` + `ballRetraction_mem_closedBall`.
- **(ii) `lowScaleCutoff_eq_self`** `(hι : Injective ι) (hU : ‖ι U‖ ≤ ρ)` :
  `lowScaleCutoff ι ρ U = U`.  Direct: `‖ιU‖ > 0 ⟹ scalar = 1`; `‖ιU‖ = 0 ⟹ U = 0`
  by injectivity.
- **(iii) `lowScaleCutoff_incl_lip`** `(hρ : 0 ≤ ρ)` :
  `‖ι (cutoff U) − ι (cutoff V)‖ ≤ ‖ι U − ι V‖` (1-Lipschitz in the H^{a+1}
  topology).  Via `incl_lowScaleCutoff` + `lipschitzWith_ballRetraction`
  (Hilbert radial retraction is 1-Lipschitz).
- **(iv) `lowScaleCutoff_sub_le`** `(hι : Injective ι) (hρ : 0 < ρ)` :
  `‖cutoff U − cutoff V‖ ≤ ‖U − V‖ + (1/ρ)·max ‖U‖ ‖V‖·‖ι U − ι V‖`.
  Endpoint top-scale norms `‖U‖,‖V‖` appear **linearly** as tame factors; the
  driving difference is the **lower** `‖ι U − ι V‖`.  **No pointwise H^{a+2}-ball
  hypothesis** — exactly the R1τ tame cross term `max‖U‖_{a+2}·‖U−V‖_{a+1}`.
  Proof = 4-case adaptation of `norm_map_ballRetraction_sub_le` (both inside /
  U in–V out / U out–V in / both out), with `‖u‖`→`‖ιU‖`, `‖u−u'‖`→`‖ιU−ιV‖`,
  `J(u−u')`→`U−V`, `‖Ju‖`→`‖U‖`.

Private helper `lowScaleCutoff_eq_smul` (`ρ < ‖ιU‖ ⟹ cutoff = (ρ/‖ιU‖)•U`),
mirror of `ballRetraction_eq_smul_of_lt`.

## KEY mathematical point — injectivity of ι is genuinely required for (ii),(iv)

The scalar `min 1 (ρ/‖ιU‖)` collapses to **0** (not 1) when `‖ιU‖ = 0` (Lean
`ρ/0 = 0`).  Verified counterexample WITHOUT injectivity: `U` in `ker ι` with
`‖U‖_{a+2}=100`, `V=U+εw`, `‖ιw‖=1`, ε tiny ⟹ `cutoff U = 0`, `cutoff V = V`,
LHS of (iv) ≈ 100 while RHS ≈ 0.  So (iv) is FALSE without injectivity.
`ballRetraction` avoids this because at its degenerate point the ELEMENT is 0;
the lower-topology sibling does not, so `Function.Injective ι` is a real
hypothesis (discharged at instantiation by `tensorHsInclusion_injective`).
This is NOT the ruling's stop signal (that is an unavoidable pointwise
`‖U‖_{a+2},‖V‖_{a+2} ≤ R₂` in the estimate — never appears here).

## Concrete instantiation recipe (for items 4/5, downstream)

All committed-clean (verified `git status`):
- `X := tensorHs g r s (a+2)`, `H := tensorHs g r s (a+1)` — both carry
  `NormedAddCommGroup` + `InnerProductSpace ℝ` (`SobolevScale/Defs.lean:507,514`).
- `ι := tensorHsInclusion (hτσ : (a+1 : ℝ) ≤ a+2)` (`SobolevScale/Inclusion.lean:170`).
- `hι := tensorHsInclusion_injective hτσ` (`Inclusion.lean`).
- `‖ι U‖ ≤ ‖U‖` available as `tensorHsInclusion_norm_le` if a bound in `H^{a+2}`
  is later wanted; not needed by the four lemmas themselves.
- coordinate transparency: `tensorHsInclusion_coeff` (rfl on eigenbasis).

The four lemmas then apply verbatim; e.g.
`lowScaleCutoff_sub_le (tensorHsInclusion hτσ) (tensorHsInclusion_injective hτσ) hρ U V`.

## Verification

Header: `set_option autoImplicit false` + `relaxedAutoImplicit false` +
`maxSynthPendingDepth 3` (matches lakefile).  Direct `lean` typecheck recipe from
`Sobolev/TensorHilbert/RemainderCoeffTopSeparated.md` (LEAN_PATH over
`C:/dgbuild/e87b/lib/lean` + mathlib packages; import is LIGHT — only
committed-clean `BallRetraction.olean` + 2 Mathlib files).

Status: **written + line-by-line proofread; verification <PENDING/GREEN>** (see
plan status log).  `#print axioms` on each public theorem must be
`[propext, Classical.choice, Quot.sound]`; audit lines stripped after green.

## Guardrails honoured

New leaf + this same-name `.md` only.  No commit.  No dirty tracked file
imported or edited (BallRetraction, Inclusion, Defs all committed-clean).
Imports Mathlib + committed-clean BallRetraction only — Codex-independent.

## Honest accounting

Ruling item **3 of 6**.  Items 1–2 are the prior bricks; 4 (tame Nemytskii),
5 (fixed-horizon representative), 6 (class-uniform packet) remain, then
instantiate `τ₀`.  The black box **(N)** itself is still **0%** — this brick is
pure analytic infrastructure that item 4 consumes; it does not by itself close
any `sorryAx` on `short-time-existence`.
