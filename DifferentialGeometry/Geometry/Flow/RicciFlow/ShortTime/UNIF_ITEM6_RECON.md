# UNIF_ITEM6_RECON — R1τ ruling item 6: the narrow class-uniform packet

Recon executed 2026-07-24 (Opus 4.8, LANE C) in worktree
`C:/Users/liao9/.codex/worktrees/e87b/...`, branch `codex/analytic-producers-e87b`.
**RECON ONLY — no `.lean` written.**  Deliverable of the LANE C dispatch in
`UNIF_EXISTENCE_PLAN.md` (Parallel lanes, 2026-07-24).  Spec = the item-6
paragraph of `UNIF_N_PRO_RULING.md`.

Scope: the FINAL packet of the R1τ route — after items 2–5 (tame estimate,
cutoff, time-level Nemytskii, fixed-horizon representative) rebuild the
per-datum lane in `H^{a+1}`-controlled form, item 6 makes the engine's
surviving `g₀`-intrinsic constants class-uniform so the Stage-3/(N) assembly
can replace each `Classical.choose(g₀)` by a `gBase`-level `Λ`-formula and read
off a horizon floor `τ₀(gBase, Λ, S) > 0`.

Orders (fixed once and for all, per the Stage-0 audit `UnifClassBounds.md` §3):
`a = 4·finrank + 10` (EVEN), `a+1` (ODD), `a+2 = A(n) = 4·finrank + 12` (EVEN).
The packet lives ONLY at these three orders.  Do NOT design a general `H^s`
theory.

---

## 0. LEAD RISK (read first) — the spectral scale has no high-order min-max transfer

`tensorHs g r s σ` (`Analysis/Spectral/Tensor/SobolevScale/Defs.lean:227`) is a
**genuine spectral scale**, NOT a covariant-derivative-sum norm:

- an element is a coordinate family `coeff : TensorEigenIdx g r s → ℝ` against
  the **connection-Laplacian eigenbasis of `g`**, with norm²
  `‖u‖²_{H^σ_g} = ∑ᵢ (1+λᵢ)^σ · (coeff i)²`
  (`tensorSobolevWeight i σ = (1 + λᵢ)^σ`, `Defs.lean:100`; `λᵢ ≥ 0` = the
  Bochner/rough-Laplacian eigenvalue of `g`, `TensorEigenIdx.lambda`).
- the eigenbasis AND the eigenvalues depend on `g`; `tensorHs g₀ …` and
  `tensorHs gBase …` are literally DIFFERENT spaces over different index types
  `TensorEigenIdx g₀` vs `TensorEigenIdx gBase`.

Consequence for the three-order comparison, and the packet's single biggest
mathematical risk:

> **There is no cheap operator/min-max transfer at orders `a, a+1, a+2`.**  Even
> if `Δ_∇^{g₀} ≍_Λ Δ_∇^{gBase}` as quadratic forms (which follows from
> `Λ`-comparability + jets), operator monotonicity of `A ↦ A^σ` holds only for
> `0 ≤ σ ≤ 1` (Löwner–Heinz).  At `σ = a, a+1, a+2 ≈ 4n+10…12 ≫ 1` a form
> comparison `Δ^{g₀} ≤ Λ·Δ^{gBase}` does NOT give `(1+Δ^{g₀})^σ ≤ C·(1+Δ^{gBase})^σ`.
> So the high-order spectral norms CANNOT be compared spectrally; the comparison
> is forced through covariant derivatives, and every route must pay the
> **elliptic-regularity (Gårding) constant** that relates the `g₀`-spectral norm
> to the `g₀`-covariant-derivative-sum norm.  That constant exists today only as
> a `Classical.choose` existential (§1).  Making it `Λ`-uniform is a genuine
> spectral-geometry re-derivation — it is the crux of the whole packet, and it is
> NOT dissolved by the `connDiff` covariant-difference tools (those only serve
> the covariant middle step).

This is exactly the risk the ruling's stop-condition anticipated ("spectral
scale with no clean min-max transfer").  It is real here.  The packet is
otherwise routine-to-medium; this one level is the gate.

**Mitigant (why it is hard-but-not-hopeless):** the existing per-metric proof of
the hard direction (`DirichletSpectralBochnerGap.lean`) is an **iterated Bochner
integration-by-parts recursion whose per-step constants are curvature
contractions of `g`** (Weitzenböck commutators), plus the metric/volume
contraction.  Under `Λ`-comparability to a FIXED `gBase` on a FIXED closed `M`
with curvature/metric jets `≤ Λ`, every per-step constant is a polynomial in
`Λ` and `n`.  So the Gårding constant is `Λ`-boundable in principle by re-running
the SAME recursion with the constant tracked explicitly instead of
`Classical.choose`d.  The difficulty is bookkeeping at high order (≈ `4n+12`
nested steps, even+odd parity), not a missing idea — UNLESS a hidden dependence
on a non-`Λ`-controlled quantity surfaces (see §4 risk row).

---

## 1. INVENTORY

### 1.1 What EXISTS (per-metric, existential constants)

The `g₀`-intrinsic spectral↔covariant equivalence is already built, two-sided,
at every integer order, as **`∃ C` existentials** (`Classical.choose`, no
formula, `g₀`-dependent):

| direction | lemma (file:line) | shape |
|---|---|---|
| spectral ≤ covariant (`Ca`) | `exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general` (`Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.lean:902`) | `∃C≥0, ∀T, ‖smoothCcToTensorHs g₀ n T‖ ≤ C·∑_{j≤n}‖iteratedCovGrad g₀ j T‖` |
| covariant ≤ spectral (`Cb`, ELLIPTIC REG.) | `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general` (`…SobolevNonlinearityExistence.lean:774`) | `∃C≥0, ∀S, ∑_{j≤n}‖iteratedCovGrad g₀ j S‖ ≤ C·‖smoothCcToTensorHs g₀ n S‖` |

The HARD direction's engine (private, `Classical.choose`):
`Analysis/Spectral/Tensor/SobolevScale/DirichletSpectralBochnerGap.lean`
— `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general_local:1063` (even
`:834` + odd `:896`), built from the **Bochner recursion**
`iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower:1220`, the
**Weitzenböck commutator** `iteratedRoughLapGrad_commutator_l2Norm_le_local:616`,
the **Dirichlet gap** `cc_dirichlet_gap:1539`, and Parseval
`rawConnLapIter_l2NormSq_eq_tsum:87`.  Imports show the analytic backbone:
`GreenIdentityAndIBP.TensorCovDivergence` (IBP), `CovGradRoughLap.
PointwiseToL2Packaging`, `GagliardoNirenbergLpFiberNorm`,
`SobolevScale.SpectralPouNormEquiv`.

The EASY direction's engine: `smoothCcToTensorHs_rawTensorConnLapSmooth_le_self`
(`DirichletSpectralBochnerGap.lean:148`), `cc_raw_hs_le:286`, `cc_mass_le:352`.

Symmetrization is a **contraction in the covariant-sum norm** (constant 1, NOT a
`Ca·Cb` blow-up): `norm_iteratedCovGrad_symmS_le`
(`SobolevNonlinearityExistence.lean:2707`).  This is the ruling's "expose the
norm contraction, do not transfer `Csym1/Csym2`" — the `Csym1/Csym2 = Ca·Cb`
packaging at `exists_norm_smoothCcToTensorHs_symmS_le:2727` only blows up
because it round-trips through the spectral scale.  **`Csym1/Csym2` are NOT in
the packet.**

Spectral↔PoU-covariant scaffolding at general order (all within ONE metric,
existential constants), useful as templates:
`Analysis/Sobolev/Embedding/RawConnLapToHsOrderDropping.lean` —
`exists_rawConnLapSmooth_toHs_le_toHs_succ:3785`,
`exists_rawConnLapIter_toHs_le_toHs:3824`, `toHs_norm_mono:3862`;
`Analysis/Sobolev/Tensor/PouWeightedHsNorm.lean` (the PoU covariant `H^k` norm
`tensorPouSobolevHsNorm:98`, `_le_succ:295`, `_smul:518`, `NormSq:1023`);
`SobolevScale/SpectralPouNormEquiv.lean` (spectral↔PoU norm equivalence, per
metric); `SobolevScale/Order2Equivalence.lean` (`tensorHs g 2 ≃ₗᵢ TensorL2` —
isometric, but only order 2).

**Fiber-level cross-metric precedent (SCALAR, H² only):**
`Analysis/Spectral/Intrinsic/Garding/CrossMetricEnergy.lean` — `cross_energy_le
:265` compares Hessian/differential energies of a scalar in one metric against
its fixed spectral `H²` norm in another, holding the spectral reference measure
fixed.  This is the ONLY genuine cross-metric norm statement in the tree.  It is
a template for the pattern, NOT the packet (rank 0, order 2, one-sided, fixed
measure).

Fiber/measure comparison building blocks (routine level, exist):
`Sobolev/HebeyBlock/FiberNorm/FiberNormRiemannianBridge.lean`, `GramTwist.lean`,
`Sobolev/Manifold/MeasureBridge.lean` (+ `MeasureBridgeUniform.lean`, but that is
single-metric chart-cover uniformity).

Covariant-derivative difference building blocks (the `∇^{g₁}−∇^{g₀}` engine that
the mission asked about — the `TensorHilbert` `connDiff` layer):
`Sobolev/TensorHilbert/ConnDiffJetL2Summed.lean`
(`connDiffContrInsertionField_…_topSeparated`),
`CometricInverseDifferenceMultiplier.lean`, `CometricDifferenceSlotPairing.lean`,
`InverseMetricPerturbationFibreBound.lean`.  **Caveat:** these are per-order
top-separated jet-L² bounds for the DeTurck REMAINDER coefficient fields
(`g₁` = solution vs `g₀` = initial), tuned for item 2, NOT a packaged two-sided
covariant-sum norm equivalence `∑‖∇^{g₀,j}u‖ ≍ ∑‖∇^{gBase,j}u‖`.  They supply the
Christoffel/cometric-difference ATOMS, so the middle step is an assembly, not a
from-scratch build.

### 1.2 What is genuinely MISSING

1. **Any two-metric `tensorHs` comparison.**  Grep across `Analysis/**` for a
   norm relation between `tensorHs g₀` and `tensorHs gBase` (or any `Λ`-uniform
   spectral↔covariant constant) returns NOTHING.  Confirmed the Stage-0 audit's
   "No cross-metric layer was found."
2. **A `Λ`-uniform Gårding constant** (both directions) at `s ∈ {a,a+1,a+2}` —
   the §0 crux.  The per-metric versions (§1.1) are `Classical.choose`.
3. **A packaged covariant-sum cross-metric equivalence**
   `∑_{j≤s}‖∇^{g₀,j}u‖_{L²(g₀)} ≍_{F(Λ,n,s)} ∑_{j≤s}‖∇^{gBase,j}u‖_{L²(gBase)}` (atoms
   exist, assembly does not).
4. **`Λ`-uniform named-constant transfers**: uniform `‖N(0)‖_{H^a_{g₀}}`, uniform
   tame `K`, uniform `H^{a+1}→C⁰` admissibility radius `R₀`.

---

## 2. STATEMENT LIST (narrow — the minimum for Stage-3/(N))

Class-hypothesis bundle (spell out; propose predicate `IsUnifClass`, or reuse a
`MetricCovDerivOrderBoundOn`-based bundle if the Evolution lane already has one):

```
hΛ    : 1 ≤ Λ
hcmp  : ∀ x u, (1/Λ)·gBase x u u ≤ g₀ x u u ∧ g₀ x u u ≤ Λ·gBase x u u   -- Λ-comparable
hjet₀ : MetricCovDerivOrderBoundOn Set.univ (A n) g₀   gBase Λ           -- jets of g₀ (≤ a+2)
hjetB : (gBase fixed; its jets are absolute constants, folded into F)     -- no uniformity needed
```
(`M` closed, `gBase` fixed and smooth ⟹ its injectivity radius, volume, and
curvature jets are fixed positive constants; this is what makes the geometric
constants below `Λ`-uniform rather than merely "class-uniform over abstract
manifolds" — see §4.)

The packet, `s` ranging over `{a, a+1, a+2}` only:

**S1 (SPINE, hard). `hs_covsum_unif` + `covsum_hs_unif`** — the `Λ`-uniform
`g₀`-side spectral↔covariant Gårding equivalence.
```
theorem hs_covsum_unif  (…class hyps…) (s ∈ {a,a+1,a+2}) :
  ∃ C : ℝ, 0 ≤ C ∧ C ≤ F₁(Λ, n) ∧ ∀ T : SmoothCcTensor g₀ 0 2,
    ‖smoothCcToTensorHs g₀ s T‖ ≤ C · ∑_{j≤s} ‖iteratedCovGrad g₀ j T‖
theorem covsum_hs_unif  (…class hyps…) (s ∈ {a,a+1,a+2}) :
  ∃ C : ℝ, 0 ≤ C ∧ C ≤ F₂(Λ, n) ∧ ∀ S : SmoothCcTensor g₀ 0 2,
    ∑_{j≤s} ‖iteratedCovGrad g₀ j S‖ ≤ C · ‖smoothCcToTensorHs g₀ s S‖
```
i.e. exactly `exists_{…}_general` (§1.1) but with the choose-constant bounded by
an explicit `F(Λ,n)`.  This is the operational core: once S1 holds, every
`g₀`-spectral quantity is bounded by a `g₀`-covariant computation with a
`Λ`-uniform factor, and covariant computations with jets `≤ Λ` are the routine
part.

**S0 (MEDIUM, feeds S2/S1b). `covsum_cross_unif`** — covariant-sum cross-metric
equivalence via jets + `connDiff`.
```
theorem covsum_cross_unif (…class hyps…) (s ∈ {a,a+1,a+2}) :
  ∃ C ≥ 0, C ≤ F₀(Λ,n) ∧ ∀ u smooth,
    ∑_{j≤s}‖∇^{g₀,j}u‖_{L²(g₀)} ≤ C·∑_{j≤s}‖∇^{gBase,j}u‖_{L²(gBase)}   (and reverse)
```

**S1b (MEDIUM, packaging = the ruling's "smooth-core norm comparison at
(a,a+1,a+2)"). `hs_cross_unif`** — the g₀↔gBase spectral comparison, a corollary
`S1 ∘ S0 ∘ (fixed gBase Gårding choose)`:
```
theorem hs_cross_unif (…class hyps…) (s ∈ {a,a+1,a+2}) :
  ∃ C ≥ 0, C ≤ F(Λ,n) ∧ ∀ u, ‖u‖_{H^s_{g₀}} ≤ C·‖u‖_{H^s_{gBase}}   (and reverse)
```
NOTE: the (N) assembly does NOT strictly consume S1b — it consumes S1 + the
covariant bounds S2–S4 to produce absolute `F(Λ,n)` numbers.  S1b is the
mission's headline "three-order comparison" and the clean statement of the
packet, so state it, but it is packaging, not the load-bearing input.

**S2 (MEDIUM). `embed_ball_unif`** — uniform `H^{a+1}→C⁰` admissibility radius
(the ruling's "class-uniform `(H^{a+1}→C⁰)`/fibre-operator bound"; under R1τ this
replaces the old `H^{a+2}` radius `R₀` at `:2175`).
```
theorem embed_ball_unif (…class hyps…) :
  ∃ ρ > 0, ρ ≥ φ(Λ,n) ∧ ∀ u, ‖u‖_{H^{a+1}_{g₀}} ≤ ρ → (fibre-smallness / C⁰ bound)
```
Route: `S1(covsum_hs_unif)` at `s=a+1` (spectral→covariant) then uniform Morrey
(`Sobolev/Manifold/MorreyManifoldHigherOrder.lean`, covariant, constant fixed by
`gBase` inj-radius on closed `M`).

**S3 (MEDIUM, coupled to item 2). `tame_const_unif`** — uniform tame constant `K`
(the ruling's "uniform tame constant"; the ball-Lipschitz `K` at `:2050`).
```
theorem tame_const_unif (…class hyps…) : ∃ K ≥ 0, K ≤ ψ(Λ,n) ∧ (the item-2 tame
  two-orientation difference bound holds at g₀ with constant K)
```
Route: `S1` + uniform Sobolev multiplication (`Sobolev/Manifold/SobolevAlgebra
.lean` / `MoserTameProduct.lean`) + the item-2 tame estimate (its leading
coefficient is already R-free per plan §№12/№13 `TameNemytskii`).

**S4 (ROUTINE given S1). `nfun0_norm_unif`** — uniform `‖N(0)‖_{H^a_{g₀}}`
(`deTurckSobolevNHa2Symm g₀ g_bg a 0`, `:2783`; `≈ −2Ric(g₀)` + connection
corrections).
```
theorem nfun0_norm_unif (…class hyps…) : ‖deTurckSobolevNHa2Symm g₀ gBase a 0‖_{H^a_{g₀}} ≤ D(Λ,n)
```
Route: `S1(hs_covsum_unif)` at `s=a` ⟹ `≤ Ca_unif·∑_{j≤a}‖∇^{g₀,j}N(0)‖_{L²(g₀)}`;
`N(0)` is a curvature term, its covariant jets `≤ Λ` (Lemma-3.11 producers,
`AllTimesBounds.lean`), the `L²(g₀)` integral over closed `M` has volume `≍ Λ`.

Deliberately EXCLUDED (per ruling): `Csym1/Csym2` transfer (S-contraction,
constant 1 in covariant norm — §1.1); the qualitative near-`t=0` `d` and
horizons `d₂,d₂F` (item 5's fixed-horizon representative removes them, not the
packet); any general/fractional-order `H^s` theory.

---

## 3. ROUTE per statement (fiber × derivative × spectral; hard level marked)

Every statement decomposes into three levels.  The hard level is ALWAYS the
spectral one, and only for the `g₀` side.

| level | content | difficulty | machinery |
|---|---|---|---|
| **fiber** | `Λ`-comparable metrics ⟹ fibre-norm + volume equivalence (`|·|_{g₀} ≍_{√Λ} |·|_{gBase}`, `dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}`) | ROUTINE | `FiberNormRiemannianBridge`, `GramTwist`, `MeasureBridge`; scalar precedent `cross_energy_le` |
| **derivative** | jets + `connDiff` ⟹ `∇^{g₀,j}` vs `∇^{gBase,j}` comparison (Christoffel-difference tensor `≤` 1-jet `≤ Λ`, iterated) | MEDIUM (assembly of existing atoms) | `ConnDiffJetL2Summed`, `CometricInverseDifferenceMultiplier`, `iteratedCovGrad` |
| **spectral** | `g₀`-spectral `H^s` ↔ `g₀`-covariant sum, `Λ`-uniform constant | **HARD** (§0) | re-derive `DirichletSpectralBochnerGap` recursion with tracked constant |

- **S1**: pure spectral level (single metric `g₀`).  **HARD.**  Re-run the
  Bochner IBP recursion (`iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_
  lower`) tracking the per-step curvature-commutator constant as a `Λ`-polynomial
  through `a+2` steps and both parities.  The gBase side of any g₀↔gBase compare
  is a FIXED `Classical.choose` (one number, no uniformity).
- **S0**: fiber × derivative levels only (NO spectral).  MEDIUM — the routine and
  assembly levels; this is where `connDiff` is the right engine.
- **S1b** = `S1(g₀) ∘ S0 ∘ Gårding(gBase, fixed)`.  MEDIUM once S1+S0 exist.
- **S2**: `S1` (spectral→covariant) then covariant Morrey (fiber-level embedding,
  `gBase`-fixed inj-radius).  Hard part inherited from S1.
- **S3**: `S1` then covariant Sobolev multiplication + item-2 tame estimate.  Hard
  part inherited from S1; extra coupling to the in-flight item-2 constant.
- **S4**: `S1` then curvature-jet-to-`L²` (routine, jets `≤ Λ`).  Hard part
  inherited from S1.

**The whole packet has ONE hard level, reached by S1; S2–S4, S1b inherit it and
are otherwise routine-to-medium.**  The `connDiff` tools do NOT touch S1.

---

## 4. RISK + EFFORT

| stmt | difficulty | sessions | note |
|---|---|---|---|
| **S1** | **HARD** | **3–5** | the gate; high-order Bochner-recursion constant, even+odd parity |
| S0 | medium | 2–3 | tame tensor-algebra assembly of `connDiff` atoms into a two-sided covariant-sum equivalence |
| S1b | medium | 1–2 | corollary once S1+S0 land (mostly packaging) |
| S2 | medium | 1–2 | after S1; uniform Morrey on covariant norm |
| S3 | medium | 2 | after S1 AND item-2 tame estimate lands (coupled) |
| S4 | routine | 1 | after S1; curvature-jet→L² |

**Single biggest mathematical risk of the packet:** the `Λ`-uniform
elliptic-regularity (Gårding) constant of S1.  Sub-risks, in priority order:

1. **High-order bookkeeping blow-up.**  Iterating the Bochner recursion to
   order `a+2 ≈ 4n+12` yields a constant that is a length-`(a+2)` product of
   per-step curvature/metric contractions.  It is a polynomial in `Λ,n` (fine
   for a bound `F(Λ,n)`), but tracking it sorry-free through the existing
   private `_even_local`/`_odd_local` split is heavy.  Likely the true
   multi-session cost.
2. **Hidden non-`Λ` dependence (the killer risk).**  Audit the
   `DirichletSpectralBochnerGap` per-step constants for any dependence on a
   quantity NOT controlled by `Λ`-comparability + jets — a spectral gap
   `λ₁`, an injectivity radius, or a Poincaré/`cc_dirichlet_gap` constant.  For
   the covariant↔spectral EQUIVALENCE (S1) the constants should be pure
   curvature/metric contractions (`Λ`-controlled).  For the Sobolev EMBEDDING
   (S2) a lower injectivity-radius bound IS classically needed — but it is
   supplied FREE here because the class is comparable to a FIXED `gBase` on a
   FIXED closed `M`, so `inj(g₀) ≥ c(gBase,Λ) > 0`.  **Confirm this in the S1
   pre-build**: if a genuine `λ₁(g₀)`-type gap that `Λ`-comparability does not
   control appears in the equivalence constant, the packet stalls and R1τ's
   uniformization is in question (this is the §0 stop-condition materializing).
3. **Odd order `a+1`.**  The odd-parity branch (`…_odd_local:896`,
   `covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd_local:391`) is a separate,
   slightly messier recursion; it must be uniformized too (one of the three
   orders is odd).

The routine/medium statements carry no comparable risk: fiber comparison is
algebraic in `Λ`, derivative comparison is a bounded assembly of existing atoms,
and the named-constant transfers are direct once S1 is in hand.

---

## 5. HOME (canonical homes)

- **S1** (`hs_covsum_unif`, `covsum_hs_unif`): NEW leaf beside the per-metric
  engine, `Analysis/Spectral/Tensor/SobolevScale/UnifBochnerGap.lean`
  (namespace `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral`, mirroring
  `DirichletSpectralBochnerGap.lean`).  Its private Bochner-recursion deps live
  there; the uniform version must sit next to them (a leaf cannot see the
  privates otherwise, and re-deriving them elsewhere is forbidden parallel API).
- **S0** (`covsum_cross_unif`): NEW leaf `Analysis/Sobolev/CrossMetric/
  CovGradSumCrossUnif.lean` (or under `Sobolev/HebeyBlock/` next to the covariant
  tensor-Sobolev block).  Imports the `connDiff` atoms from
  `Sobolev/TensorHilbert/`.
- **S1b** (`hs_cross_unif`): with S1, in `SobolevScale/UnifBochnerGap.lean`
  (it is the spectral packaging), importing S0.
- **S2/S3/S4** (`embed_ball_unif`, `tame_const_unif`, `nfun0_norm_unif`): the
  DeTurck-specific named-constant transfers → the plan's already-named Stage-1
  file `Geometry/Flow/RicciFlow/ShortTime/UnifClassBounds.lean` (one lemma per
  engine input, per plan Stage 1), importing S1/S0 and the DeTurck defs from
  `Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.lean`.
- Class-hypothesis predicate `IsUnifClass`: with the (N) statement, i.e. beside
  `Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean`, or in
  `UnifClassBounds.lean` if not already present in the Evolution lane.

---

## 6. RECOMMENDED FIRST BUILD BRICK

**Build S1 first, and before writing any Lean, do the §4-risk-2 audit of
`DirichletSpectralBochnerGap.lean`'s per-step constants** (are they pure
curvature/metric contractions, or is there a hidden `λ₁`/gap/inj-radius term
`Λ`-comparability does not control?).  Concretely, the first brick:

> A `Λ`-uniform version of the SINGLE Bochner step
> `iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`
> (`DirichletSpectralBochnerGap.lean:1220`): show its base + lower-order
> constants are `≤ P(Λ,n)` under the class hypotheses (curvature commutator
> `iteratedRoughLapGrad_commutator_l2Norm_le_local:616` bounded by the Riemann
> jet `≤ Λ`; metric/volume contraction `≤ Λ`).  If that one step is `Λ`-uniform,
> the induction to order `a+2` (both parities) is the same recursion the file
> already runs, and S1 follows; if it is NOT (risk 2 fires), STOP and report —
> that is the R1τ-endangering signal, and the packet should not be built on a
> `Classical.choose` masked as uniform.

Rationale: S1 is the gate and the only real risk; S0/S2/S3/S4 are mechanical
once S1 is known achievable, and there is no point assembling the covariant
cross-metric layer (S0, medium effort) if the spectral gate (S1) turns out to
need a quantity `Λ` cannot control.

---

## 7. S1 CONSTANT AUDIT (session 2, STAGE 1 — the §6/§4-risk-2 audit executed)

**VERDICT: CLEAN. No type-(iii) constant anywhere in the Bochner recursion.**
Every constant in the single Bochner step, and in the full induction chain, is
either (i) a curvature-jet contraction (pointwise sup of the Riemann tensor `R`
and its covariant derivatives `∇^a R`) or (ii) a dimension/metric-contraction
constant.  Both are controlled by `Λ`-comparability + `MetricCovDerivOrderBoundOn`
jets.  The §0 stop-condition ("spectral scale with no min-max transfer") remains
the strategic risk, but the specific fear that the per-metric proof hides an
uncontrollable `λ₁`/injectivity/spectral-gap quantity is **REFUTED by inspection**.

### 7.1 `cc_dirichlet_gap` is a red herring (NOT a spectral gap)

`cc_dirichlet_gap` (`DirichletSpectralBochnerGap.lean:1539`) reads
`‖∇^{n+1}u‖²_{L²} ≤ ‖u‖²_{H^{n+1}} + Cgap·‖u‖²_{H^n}` — a **coefficient-one
Gårding inequality** (the `H^{n+1}` term has coefficient exactly 1; the "gap" is
the ORDER gap between consecutive Sobolev norms, controlled by lower orders).  Its
`Cgap` is the accumulated `Cstep·Csob² + Cih` from
`exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower:1439/1466` —
a product of the single-step constants (§7.2) and the Sobolev-jet constant
(§7.3).  There is NO eigenvalue-gap `λ₁`, NO injectivity radius, NO Poincaré
constant.  The name misleads; the content is elliptic regularity.

### 7.2 Single Bochner step — per-constant provenance
`iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower g₀ s k`
(`DirichletSpectralBochnerGap.lean:1220`), producing order `k+2` from order `k`,
constant `C = Cgap_comm + K 0`:

| # | constant | source (file:line) | what it is | TYPE |
|---|---|---|---|---|
| 1 | `K 0` (Weitzenböck curvature) | `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` (`AllOrderGardingConstant.lean:193`), `= √(2·ccR 0 + 2·ccdR 0)` | `ccR/ccdR` = appFullSec window sup of the Riemann hom-field `H_R` (`= R`) and `H_dR` (`= ∇R`) via `exists_pointwiseTensorCurv_firstOrder_homField_section` + `exists_appFullSec_on_jet_iteratedCovGrad_window_bound` (`HomFieldActionIteratedCovGradWindow.lean:342`) | **(i)** curvature-jet |
| 2 | `Cfun 0`, `Cfun 1` (commutator `[Δ_∇,∇^k]`) | `iteratedRoughLapGrad_commutator_l2Norm_le_local` (`…:616`), recursion `Cfun p = K p + Cm(p+1)`, base `0`; every `K` from row 1 | finite sum of `∇^a R` sups (docstring `:307–312`: "contractions of `∇^a R`, `a ≤ m`") | **(i)** curvature-jet |
| 3 | `Crc` | `exists_iteratedCovGrad_rawConnLap_l2Norm_le_local` (`…:759`), `= K_lap + Cfun 0` | metric/curvature (row 4) + commutator (row 2) | **(i)/(ii)** |
| 4 | `K_lap` | `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` (`RoughLaplacianSecondCovGradL2Bound.lean:537`) | `Δ_∇ = −trace_g ∇²`: metric-contraction / dimension | **(ii)** |
| 5 | `dimR` | `Real.sqrt (finrank E)` (`:1109`) | pure dimension | **(ii)** |
| — | Weitzenböck IBP | `weitzenbock_integrated_covGrad_l2_normSq` (`IntegratedOrder2Weitzenbock.lean:196`) | an EQUATION — no free constant | — |
| — | `covDiv ≤ covGrad` | `covDivergence_l2Norm_le_covGrad_local` (`:1179`) | one-slot trace | **(ii)** |

The Weitzenböck defect `pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇S)`
(`PointwiseTensorBochner.lean:95`) is, by `pointwiseTensorCurv_toSection_eq_frame_sum
:208`, the frame-trace gradient-slot reordering = "the genuine off-diagonal
Riemann curvature" — a purely algebraic contraction of `R` with `S`.  Confirmed
type (i).

### 7.3 Assembly-level (full induction; not in the single step, audited for completeness)
- `Csob` = `hsJet_le` (`IteratedCovGradHsJetBound.lean:834`) → `jet_even`/`jet_odd`
  (`:842/:847`): the covariant-sum ↔ spectral Sobolev-jet bridge, same
  rawConnLap/curvature family (sibling `hs_le_jet:855` gives the reverse).
  Expected type (i)/(ii); not separately unrolled (out of single-step scope) —
  it must be re-audited when the full induction is uniformized, but it shares the
  curvature/dimension backbone and shows no spectral-gap surface.
- `cc_dirichlet_gap`'s `Cgap` (§7.1): product of §7.2 + `Csob`.

### 7.4 ORDER-BUDGET finding (sharpens Stage-0 `A(n)`)
The commutator `[Δ_∇, ∇^m]` needs curvature jets `∇^a R` up to `a ≈ m`
(`AllOrderGardingConstant.lean:307–312`).  In the single step at inner order `k`
the commutator is at level `m = k`, so the step needs `∇^a R` up to `a ≈ k`.  The
FULL induction to order `a+2` therefore needs `∇^a R` up to `a ≈ a+2`, i.e.
**metric jets up to ≈ `A(n)+2 = 4·finrank+14`** (Riemann `= 2` metric
derivatives).  This is `+2` beyond the Stage-0 data order `A(n)=4n+12` — the
standard Gårding phenomenon (the coefficients' jets sit two orders above the
data order).  **ACTION for the (N) statement:** the class hypothesis
`MetricCovDerivOrderBoundOn … Λ` for S1 should be at order `≈ A(n)+2`, not `A(n)`;
confirm the exact reach (`k−1` vs `k` vs `k+1`) when building §7.5(2a).  This does
not endanger R1τ — the Lemma-3.11 producers are order-generic (`AllTimesBounds`),
so raising the order is free on the input side.

### 7.5 STAGE-2 decomposition — why the single step is NOT a clean one-session landing
The planner's STAGE-2 target (single step with an explicit `F(Λ,n)` constant
under hypotheses `Λ`-comparability + `MetricCovDerivOrderBoundOn`) does not land
directly: its constant (§7.2) is built from `Classical.choose` curvature-jet
SUPS (`ccR, ccdR, K_lap`) that are NOT yet bounded by `Λ`.  The missing bridge is
the genuine first Lean brick, in three sub-bricks:

- **(2a) [MISSING — the real gate]** `MetricCovDerivOrderBoundOn Set.univ N g₀ gBase Λ ⟹
  sup_x ‖∇^a Riemann(g₀)‖ ≤ Fᵣ(Λ,n)` for `a ≤ N−2`.  Bridges metric jets to the
  Riemann-curvature jet sup (`Riemann = 2` metric derivatives).  A
  `MetricCovDerivOrderBoundOn → curvature-jet-sup` lemma was searched for and NOT
  found (`MetricCovDerivArityBridge.lean`/`MetricCovDerivContinuity.lean` cover the
  `metricCovDerivNorm` mechanics, not a curvature-sup bound).  This is itself a
  small multi-lemma sub-brick.
- **(2b)** `ccR p, ccdR p, K_lap ≤ G(Λ,n)`: feed (2a) through
  `exists_appFullSec_on_jet_iteratedCovGrad_window_bound` (already the pointwise
  sup of the Riemann hom-field) — mechanical once (2a) lands.
- **(2c)** assemble `C = (Cfun 0)² + 2·Crc·dimR·Cfun 1 + K 0 ≤ F(Λ,n)` — the
  single-step lemma the planner named; consumes (2a)+(2b)+dimension.

**Recommended first Lean brick: (2a)** — the `Λ`-uniform pointwise
Riemann-curvature-jet sup bound from `MetricCovDerivOrderBoundOn`.  It is the
narrowest genuinely-missing input, it is the gate for the whole S1, and building
(2c) before it would either reduce S1 to multiple open frontiers or leave an
unverifiable half-build (CLAUDE.md: at most one visible frontier; no
sorry-masking).  Home: a new leaf under
`Geometry/Flow/RicciFlow/HCGCompactness/` (next to the `MetricCovDeriv*` bridges)
or `Geometry/Curvature/`, exporting the curvature-jet sup so `UnifBochnerGap.lean`
(S1) can consume it.

**SESSION-3 UPDATE (2a recon — full design note in
`HCGCompactness/UnifCurvatureJetBound.md`).**  Four findings refine the above:
- **A (de-risking):** (2a) is an ASSEMBLY of existing jet-envelope
  curvature-difference machinery, not a missing layer —
  `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`
  (`Curvature/PerturbedRiemannOpDifferenceBound.lean:88`, the order-0 Riemann
  difference), `exists_norm_covGrad_connDiffSection_le_of_jetEnvelope`
  (`Curvature/CovDerivConnDiffQuadraticBound.lean:43`), plus the HCG
  `CurvDerivBoundOn`↔`MetricCovDerivOrderBoundOn` layer (`AllTimesBounds.lean:3556`).
  (The session-1/§7.5 "MISSING" call on the curvature difference was WRONG.)
- **B (scope-changing):** that machinery is `_of_lt_one` / `gFibreOpBound δ₀<1`
  = SMALL-perturbation.  For `P = g₀−gBase`, `Λ`-comparability forces
  `|P|_{gBase-op} = Λ−1`, so it applies only to `Λ < 2`.  The full class needs a
  telescoping chain (`≈Λ` links of the linear path `g_t`, each op-step `<1`) or a
  large-`δ` re-derivation.
- **C (corrects §5 HOME):** `MetricCovDerivOrderBoundOn` is DOWNSTREAM of S1's
  `Analysis` home ⟹ S1 (`UnifBochnerGap.lean`) must take the curvature-jet bound
  as an ABSTRACT hypothesis; (2a) discharges it downstream in `HCGCompactness`.
- **D:** envelope currency uses `∇^{g₀}`; `MetricCovDerivOrderBoundOn` uses
  `∇^{gBase}` — bridged by `∇^{gBase}gBase=0` (`j≥1`) + a connDiff conversion;
  assets are order-0/1, higher orders `∇^{g₀,a}Riemann` need iteration.
- **Revised first brick:** **2a-abs** — the abstract curvature-jet interface in
  `UnifBochnerGap.lean` (landable in `Analysis` now, mandated by Finding C,
  unblocks S1 independent of the `Λ<2`/telescoping question) — ahead of the
  downstream 2a-0/2a-tel/2a-hi/2a-pkg.

---

## Status
- 2026-07-25 (brick 2a-tel (a) link lemmas, LANE C, Opus): **(a) LINK LEMMAS landed** in
  `HCGCompactness/UnifCurvatureJetBound.lean` — `convexCombPath` (= `convexComb` path
  `g_t=t·g₀+(1−t)·gBase`), `convexCombPath_comparable` ((a)(i) mutual comparability, modulus
  `μ=|t−s|·Λ(Λ−1)`, `Λ_link=(1−μ)⁻¹<2` for `μ<½`, `N≈2Λ(Λ−1)` links), and
  `convexCombPath_jetBound` ((a)(ii) fixed-`gBase` jet inheritance
  `MetricCovDerivOrderBoundOn (a+1) g_t gBase Λ`, via `metricCovDeriv`-linearity +
  `covDeriv_self_succ` + `sqrt_normSq0S_smul`).  Composition (b) to the full class NOT closed:
  it needs the metric jets against the MOVING base `g_{t_k}` (`k≥1`) = order-`≤2`
  change-of-reference-connection currency, a DECLARED frontier of the active lane
  `UnifCovSumCross.lean` (order-≥2 iterated `iterCov_telescoping`/`diffStep_norm_le` assembly)
  PLUS an ungated `∇connDiff` bound (only `δ<1`-gated version exists).  Verification (2026-07-25):
  **GREEN, axiom-clean** — `lake build …UnifCurvatureJetBound` EXIT=0 (9654 jobs); `#print axioms`
  on all five public names = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  See
  `UnifCurvatureJetBound.md` session 10.
- 2026-07-24 (brick 2a ENVELOPE + Λ<2 single link, LANE C, Opus): **2a-0 COMPLETE** — the full
  order-0 curvature sup from comparability + jets alone (Λ<2), sorry-free + axiom-clean
  (`[propext, Classical.choice, Quot.sound]` on all 4 new public theorems; `lake build
  +…UnifCurvatureJetBound` EXIT=0, 9653 jobs).  `normBridge` (session 8 gate) is now proved, so the
  order-`≤2` jet envelope landed in `HCGCompactness/UnifCurvatureJetBound.lean`:
  `metricDiff_order0_bound` (j=0 Parseval HS bound `≤ n·(Λ−1)`), `metricDiff_orderPos_bound`
  (j≥1 `≤ Λ` via normBridge + the pre-existing self-zero `covNorm_self_succ`), `metricDiff_jetEnvelope`
  (`∑_{j<3}‖…‖ ≤ n·(Λ−1)+2Λ` = **B(Λ)**, c₀(n)=n), and the endpoint **`unifCurvatureSup_singleLink`**
  (tie + D1 + envelope → asset `hdiff` → session-4 composition core; **F = Λ²·(Cd+√Kbase)**).  Full
  ledger + 5 Lean lessons + the 2a-tel (Λ≥2) remaining-work note in
  `HCGCompactness/UnifCurvatureJetBound.md` §"Session 9".  **2a-tel remaining**: convexComb link
  comparability/jet inheritance + ~2Λ(Λ+1)-link g-norm triangle composition (the per-link discharge
  is now done).  2a-hi (higher orders ∇^a Riemann, a≤b) + 2a-pkg (H_R/H_dR currency) still open.
- 2026-07-24 (S0 session 4, LANE C, Opus): **T (connection-change telescoping) recon + identity
  activation.**  Route r1 CONFIRMED and the identity layer is a **FALSE WALL** — `nabla0SFun_sub_cov`
  (generic `(0,s)` multi-slot connection difference, proved by the subtraction route) +
  `diffStep`/`iterCov`/`iterCov_telescoping` (the full pointwise telescoping identity) already exist
  sorry-free in `HigherOrder.lean` + `MetricCovDerivLinear.lean`.  Currency = `normSq0S`/`iterCov`
  (chart/model).  **LANDED** in `HCGCompactness/UnifCovSumCross.lean`: `covStep_zero'` + `iterCov_one_eq`
  (order-1 reduction, first consumers of `iterCov_telescoping`); `lake build` EXIT=0 (3906 jobs), axioms
  standard triple.  **REMAINING for the S0 `L²` endpoint `covsum_cross_unif`:** the j=1 NORM atom
  `diffStep_norm_le` is BLOCKED on the **generic-rank tensor-bundle EVAL instance diamond**
  (`totalNabla0SFun_apply_section` won't synth `NormedSpace ℝ (Tensor0SModel (s+1) ℝ E)` at variable
  rank — concrete-rank only, no `attribute [-instance]` fix found), then the component Cauchy–Schwarz,
  then the T-B base-Leibniz induction (multi-session).  Full analysis + 3 route options in
  `HCGCompactness/UnifCovSumCross.md` §"Session 4".  Plus the RS↔0S currency bridge (sibling
  `MetricCovDerivBridge` lane) for the final `iteratedCovGrad`-endpoint assembly.
- 2026-07-24 (S0 session 3b, LANE C, Opus): **VOLUME brick (V) COMPLETE** — step 4
  `volumeMeasure_cross_le` LANDED sorry-free + verified (`dV_{g₀} ≤ √(Λ^n)·dV_{gBase}`, two-sided,
  `HCGCompactness/UnifCovSumCross.lean` `section VolumeMeasure`).  Planner authorized the scope-limited
  `CompactVolumeEquiv.lean:366/:371` latent-break repair (indicator `Set.indicator s 1` + explicit `rw`,
  statement-preserving; `CompactVolumeEquiv.md` records it).  `lake build +…CompactVolumeEquiv` EXIT=0
  (2873 jobs); `lake build +…UnifCovSumCross` EXIT=0 (3904 jobs); `#print axioms volumeMeasure_cross_le`
  = `[propext, Classical.choice, Quot.sound]`.  All four V levels (fibre + steps 1–3 + step-4 measure
  lift) done.  Remaining for the S0 `L²` endpoint `covsum_cross_unif`: **T** (iterated connection-change
  telescoping — the main tensor-calculus frontier, separate dispatch) and the RS↔0S currency bridge
  (sibling `MetricCovDerivBridge` lane).
- 2026-07-24 (S0 session 3, LANE C, Opus): **VOLUME brick (V) steps 1–3 LANDED sorry-free +
  verified** (`lake build +…UnifCovSumCross` EXIT=0, 3903 jobs; axioms `[propext, Classical.choice,
  Quot.sound]`).  In `HCGCompactness/UnifCovSumCross.lean`: `det_le_of_posSemidef_le` (the general
  Loewner→determinant estimate Mathlib lacks, via the CFC matrix sqrt; the genuinely-missing brick),
  its plain-form bridge `det_le_one_of_dotProduct`, `chartGram_quad_le_of_equiv` (chart-Gram Loewner
  comparison), `chartDensity_cross_le` (`chartDensity g₀ ≤ √(Λ^n)·chartDensity gBase` on the base set).
  **Step 4 `volumeMeasure_cross_le` (the measure lift) is written and complete but BLOCKED**: it needs
  `chart_lintegral_le` from `Measure/CompactVolumeEquiv.lean`, and that file no longer compiles against
  the pinned Mathlib (`volume_uniform_equiv` :366/:371 — `lintegral_indicator_one` `simpa` API drift;
  its olean was silently missing).  Two-line fix is known (`Set.indicator s 1` + explicit `rw`) but
  CompactVolumeEquiv is outside this session's editable set; the full step-4 proof is preserved in
  `UnifCovSumCross.md` for drop-in.  T (connection-change telescoping) not started.  V fibre level
  (session 1) + V steps 1–3 (this session) done; V step 4 pending the CompactVolumeEquiv repair.
- 2026-07-24 (S0 session 2, LANE C, Opus): **VOLUME brick (V) core LANDED + verified**
  (`lake build` 3860 jobs EXIT=0; axioms standard triple).  Two reusable matrix lemmas in
  `HCGCompactness/UnifCovSumCross.lean` §MatrixDet: `eigenvalues_le_of_rayleigh` (upper companion
  of `JacobianBounds.eigenvalues_ge_of_rayleigh`) and `det_le_one_of_rayleigh` (`A≤I ⟹ det A≤1`,
  the `B=I` core of Loewner→det).  **MATERIAL FINDING**: the full explicit-`Λ` volume comparison
  needs a genuine Loewner→determinant estimate (Mathlib lacks matrix-sqrt-as-op / Weyl / Hadamard /
  det-order; `CompactVolumeEquiv.lean:9` records the existing measure-equiv was built to AVOID it) —
  NOT "generic matrix analysis available", but FEASIBLE via the CFC matrix sqrt
  (`Analysis/Matrix/Order.lean`: `CFC.sqrt`, `sqrt_mul_sqrt_self`, `PosSemidef.det_sqrt`).  The
  general `det_le_of_posSemidef_le` + chart-Gram comparability + `chartDensity`/measure lift are
  FULLY WORKED (mechanical next session) in `UnifCovSumCross.md`.  T (connection-change) skeleton
  recorded there too; its j=1-for-`(0,2)` needs the generic multi-slot connection difference
  (beyond single-covector `connectionDifferenceOutput`).
- 2026-07-24 (S0 session 1, LANE C, Opus): item-6 **S0** (`covsum_cross_unif`) build STARTED.
  HOME confirmed `HCGCompactness/UnifCovSumCross.lean` (NOT recon §5's `Analysis/Sobolev/
  CrossMetric/` — S0's `MetricCovDerivOrderBoundOn` hyps are downstream of `Analysis/`, same
  Finding-C layering as brick 2a).  Comparability predicate = REUSE `MetricUniformEquivalentOn`
  (`= Λ`-comparability, `C=Λ`).  **Fiber-level layer LANDED sorry-free + verified** (`lake build`
  3860 jobs EXIT=0; axioms `[propext, Classical.choice, Quot.sound]` on all three):
  `covsumCross_fibSq` (two-sided per-order, `Λ^{±s}`), `covsumCross_fibNorm` (`√`, `Λ^{s/2}`),
  `covsumCross_fibSum` (covariant-SUM shell, single constant `Λ^{(s+n)/2}`) — forwards the
  committed `normSq0S_le_of_metric_equiv` / `sqrt_normSq0S_le_of_metric_equiv`.  The L² S0 pair
  is NOT yet stated sorry-free: THREE located missing bricks remain (design note
  `HCGCompactness/UnifCovSumCross.md`): (i) **volume** `dV_{g₀}≍_{Λ^{n/2}}dV_{gBase}` — the
  explicit-`Λ` Loewner→determinant estimate the project deliberately avoided
  (`Measure/CompactVolumeEquiv.lean:9`), self-contained matrix analysis; (ii) **RS↔0S fibre
  currency bridge** (`riemannianFiberNormSq g 0 s` ↔ `normSq0S`) — the sibling
  `MetricCovDerivBridge` lane's `normBridge`; (iii) **iterated connection change**
  `∇^{g₀,j}=∇^{gBase,j}+Γ-diff` for generic `T`, the main tensor-calculus frontier (one-derivative
  machinery exists in `Garding/CrossMetricEnergy.lean cross_point_le`).  S0 remains recon-§4
  medium (2–3 sessions); session-1 boundary (green fiber layer) reached.
- 2026-07-24 (session 3, brick 2a recon): (2a) is an ASSEMBLY of existing
  jet-envelope curvature-difference machinery, NOT a missing layer (Finding A),
  but the machinery is small-perturbation `Λ<2` only (Finding B) and its home is
  downstream of S1 (Finding C ⟹ S1 takes curvature abstractly).  Full design
  note: `HCGCompactness/UnifCurvatureJetBound.md`.  Revised first brick = 2a-abs
  (abstract interface in `UnifBochnerGap.lean`, landable in Analysis now).
  Stopped at the recon boundary — Findings B/C are scope-changing (telescoping vs
  large-δ; abstract-hypothesis interface) and need planner ratification before a
  build.  No `.lean` written this session.
- 2026-07-24 (session 2, STAGE 1): audit COMPLETE, verdict CLEAN — no
  type-(iii); all Bochner-recursion constants are curvature-jet (i) or
  dimension (ii); `cc_dirichlet_gap` is a coefficient-one Gårding inequality, not
  a spectral gap (§7.1).  Order-budget sharpened: S1 needs metric jets `≈ A(n)+2`
  (§7.4).  STAGE 2 NOT run as the single step: it reduces to the MISSING
  curvature-jet-sup-≤-`Λ` bridge (2a), which is the recommended first Lean brick
  (§7.5).  Stopped cleanly at the audit boundary per the planner's stop
  condition.  No `.lean` written this session.
- 2026-07-24 (session 1): item-6 recon COMPLETE (LANE C, no Lean).  `tensorHs`
  confirmed a spectral scale ⟹ the §0 min-max-failure risk is real and leads the
  report.  Packet = S1 (hard gate) + S0/S1b/S2/S3/S4 (routine-medium, inherit
  S1).  Reported to planner.
- 2026-07-24: item-6 recon COMPLETE (LANE C, no Lean).  `tensorHs` confirmed a
  spectral scale ⟹ the §0 min-max-failure risk is real and leads the report.
  Packet = S1 (hard gate) + S0/S1b/S2/S3/S4 (routine-medium, inherit S1).  First
  brick = the S1 single-step `Λ`-uniform Bochner constant, gated on a
  hidden-dependence audit of `DirichletSpectralBochnerGap.lean`.  Reported to
  planner.
