# DeTurck / time-regularity handoff — Ricci-flow evolution black boxes

**Audience:** whoever takes on the analytic short-time-existence / DeTurck regularity
frontier. **Goal of this note:** pin down *exactly* the Lean predicates that are currently
assumed (the "black boxes"), what they mean mathematically, why they are not derivable from
the present `SolutionOn` interface, and what a discharge needs to supply. **Everything
geometric/algebraic downstream of these is already proved** — you only owe analytic
regularity, not Ricci-flow geometry.

This is the single remaining standing layer for the whole time-side of Hamilton's 3D
theorem (Lemma 6.1 Uhlenbeck base `∂ₜRm04`, Lemma 6.2 `∂ₜΓ`, Lemma 6.3 `∂ₜRic`, the scalar
evolution, and the iterated `∂ₜ∇ᵏRm` tower all bottom out here).

---

## 0. The one-sentence summary

The project's `SolutionOn`/`IsSolutionOn` interface gives a Ricci-flow solution that is
**`C∞` in the interior in time and merely continuous up to the time-carrier boundary**, and
it does **not** assert that `∂ₜ` commutes with the (fixed-base) spatial derivative. The real
DeTurck/short-time solution is **jointly smooth in `(t, x)` up to the carrier**, from which
every black-box predicate below follows. So the task is: **construct (or assume) the smooth
DeTurck solution and prove these regularity/existence/commutation predicates from it.**

The *coordinate formulas* these predicates feed into — `∂ₜg = −2Ric`, `∂ₜg⁻¹ = 2Ric`,
the Christoffel variation, the Ricci/scalar/`Rm04` Hamilton RHS — are **all already proved
in Lean**. The black boxes supply only derivative-*existence*, time-regularity-*up-to-the-
boundary*, and `∂ₜ`/`d` *commutation*.

---

## 1. Where the interface gap is

`SolutionOn` / `IsSolutionOn` (see `…/RicciFlow/…` solution defs) provide:
- spatial `C∞` of each time slice;
- the PDE `∂ₜg = −2Ric` at **regular (interior) times**;
- continuity (not smoothness) of the metric family up to `D.carrier` (the closed time set).

They were deliberately weakened to interior-`C∞` + carrier-continuity (tasks #6–#7) so that
short-time existence could feed them. The price: every theorem that needs a **time
derivative at a carrier endpoint**, a **`ContDiffOn ⊤`-in-time** statement, or **`∂ₜ d = d ∂ₜ`**
now carries one of the predicates in §2 as a hypothesis instead of proving it.

---

## 2. The black-box predicates to discharge

All live in `Geometry/Flow/RicciFlow/Evolution/` (namespace
`DifferentialGeometry.PDE.RicciFlow`). `Idx` is the frame index type (`Fin 3` in the 3-D
application), `frame i x` a local frame, `u : Set M` its domain, `D.carrier` the closed time
set, `RegularTime D` the interior times.

### 2a. Inverse-metric time regularity — `InverseMetricTimeRegularityBlackBoxInFrameOn`
`Evolution/BlackBox.lean:49`
```
structure InverseMetricTimeRegularityBlackBoxInFrameOn (gInv) where
  gInvDt : Real → M → Idx → Idx → Real
  inverseMetricDerivative : InverseMetricDerivativeComponentsOn gInv gInvDt
  uniqueTimeDerivatives   : ∀ t : RegularTime D, UniqueDiffWithinAt ℝ D.carrier t
```
**Meaning:** the supplied inverse-metric components `gInv` have a time derivative `gInvDt`
(as a `HasDerivWithinAt` on `D.carrier`), and interval derivatives are unique at regular
times. **Already proved (not your job):** `∂ₜgInv^{ij} = 2 Ric^{ij}`
(`inverseMetricEvolutionEquationInFrame_of_inverse_components`). You supply only existence +
unique-diff. Consumer: `inverseMetricEvolution_of_timeRegularityBlackBox` (`BlackBox.lean:61`).

### 2b. Metric-frame time regularity — `MetricFrameTimeRegularityInFrameOnLocal`
`Evolution/Metric/Basic.lean:241`
```
structure MetricFrameTimeRegularityInFrameOnLocal (S gInv gInvDt frame u) where
  metricSmooth : ∀ x ∈ u, ∀ i j, ContDiffOn ℝ ⊤
      (fun t => metricCompInFrame S frame t x i j) D.carrier      -- ★ the core gap
  nondegenerateGram : InvMetricLocal S gInv frame u
  inverseMetricDerivative : InverseMetricDerivativeComponentsOn gInv gInvDt
  uniqueTimeDerivatives : ∀ t : RegularTime D, UniqueDiffWithinAt ℝ D.carrier t
```
**Meaning:** ★ `metricSmooth` is the central DeTurck fact — the frame metric components are
`C∞` in time **on the whole carrier `D.carrier`, including its boundary**, not just the
interior. Plus the frame Gram matrix is nondegenerate (two-sided inverse `gInv`), the inverse
has a time derivative, and unique-diff at regular times. This is the input to the moving
Levi-Civita / `∂ₜΓ` construction.

### 2c. Metric-frame spacetime regularity (mixed partials) — `MetricFrameSpacetimeRegularityInFrameOnLocal`
`Evolution/Metric/Basic.lean:270` (extends 2b)
```
  frameMetricSpacetimeSmooth : ∀ i j, ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ⊤
      (fun p : ℝ × M => metricCompInFrame S frame p.1 p.2 i j) (D.carrier ×ˢ u)
  frameMetricExtDerivTimeDerivative : ∀ t x ∈ u, ∀ d a b,
      HasDerivWithinAt
        (fun s => extDerivFun (fun y => metricCompInFrame S frame s y a b) x (frame d x))
        ((-2) * extDerivFun (fun y => ricciCompInFrame S frame t y a b) x (frame d x))
        D.carrier t
```
**Meaning:** joint `(t,x)`-smoothness of the metric components on `D.carrier ×ˢ u`, and the
**mixed-partial swap** `∂s d_x(g_s) = d_x(∂s g_s) = −2 d_x(Ric_s)` (specializing `∂ₜg = −2Ric`
under the fixed-base spatial exterior derivative). This is the `hmix`/spacetime-regularity
content. NB: it does **not** assert `∂ₜ` commutes with the *evolving covariant* derivative —
only with the fixed-base `extDerivFun`.

### 2d. Connection-variation black box — `ConnectionVariationBlackBoxInFrameOn`
`Evolution/BlackBox.lean:82`
```
structure ConnectionVariationBlackBoxInFrameOn (S frame u nablaRic) where
  metricCovDerivDt : Real → M → Idx → Idx → Idx → Real
  metricCovDerivDerivative : MetricCovDerivDerivativeComponentsInFrameOnLocal S frame u metricCovDerivDt
  metricCovDerivRicciFlow  : MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic
```
**Meaning:** the fixed-base spatial covariant derivative of the metric components has a time
derivative (`metricCovDerivDt`), and that time derivative equals the Ricci-flow value
(`−2∇Ric`). Equivalent to "`∂ₜ` commutes with the fixed-base `∇g` of metric components, and
`∂ₜ∇g = −2∇Ric`." Consumers: `variableMetricConnectionDiffDerivative_of_blackBox`,
`christoffelEvolution_of_blackBox` (`BlackBox.lean:97,114`) → gives `∂ₜΓ`.

### 2e. (built on 2d) Ricci-evolution time-regularity — `RicciEvolutionTimeRegularityBlackBoxInFrameOn`
`Evolution/BlackBox.lean:141`
```
structure RicciEvolutionTimeRegularityBlackBoxInFrameOn (S Rm04 gInv frame) where
  nabla2Ric : Real → M → Idx → Idx → Idx → Idx → Real
  ricciVariation : RicciVariationFormulaInFrameOn S frame (nablaGammaDtFromNabla2RicInFrame gInv nabla2Ric)
  contractedCommutators : RicciContractedCommutatorsInFrame S Rm04 gInv frame nabla2Ric
```
**Mostly NOT a black box anymore:** `contractedCommutators` is **discharged** from the Ricci
identity (`RicciContractedCommutatorsInFrame_of_tensor0S_ricciIdentity_lc`,
`Ricci/Commutator.lean:933`), and `ricciVariation` is **produced** from `∂ₜΓ`
(`ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2`,
`Ricci/GammaCoord.lean:830`), which in turn comes from 2d. The proved reduction
`ricciEvolution_of_variation_commutators` (`Ricci/Commutator.lean:1201`, no `sorry`) finishes
the Hamilton RHS. So Lemma 6.3 reduces to 2a–2d; **no Ricci-specific analytic gap remains.**

### 2f. Aggregate — `Section62TimeRegularityBlackBoxInFrameOn`
`Evolution/BlackBox.lean:176` bundles 2b-`metricFrame` + 2d-`connection` + 2e-`ricci`. This is
the single package the Section-6.2 assembly consumes; discharging 2a–2d (and the smooth
solution behind `metricSmooth`/`frameMetricSpacetimeSmooth`) discharges everything.

---

## 3. What a discharge looks like

Two layers, in order of payoff:

1. **Strengthen the solution interface.** Add to (or alongside) `SolutionOn`/`IsSolutionOn`
   a record that the metric family is **jointly `C∞` in `(t,x)` on `D.carrier ×ˢ M`** (up to
   the boundary), supplied by the DeTurck short-time existence construction. From a single
   `ContMDiffOn (ℝ×M) ⊤` metric-family fact, essentially all of §2 follows by standard
   calculus:
   - `metricSmooth` (2b ★) = the `x`-section of the joint smoothness;
   - `frameMetricSpacetimeSmooth` (2c) = the joint smoothness restated in the frame;
   - `frameMetricExtDerivTimeDerivative` (2c) and the `metricCovDeriv*` (2d) = `∂ₜ d = d ∂ₜ`,
     i.e. **Clairaut / Schwarz** for the jointly-smooth map, composed with `∂ₜg = −2Ric`;
   - `gInvDt`/`inverseMetricDerivative` (2a, 2b) = differentiating the matrix inverse of a
     jointly-smooth nondegenerate `g` (Cramer / `ContDiffOn` of inversion);
   - `nondegenerateGram` (2b) = positive-definiteness of the Riemannian metric in the frame;
   - `uniqueTimeDerivatives` = `UniqueDiffWithinAt ℝ D.carrier` — a property of the time set
     `D.carrier` (true when it is, e.g., a nondegenerate interval).

2. **Discharge the predicates.** With the joint-smoothness record in hand, prove each
   structure in §2 and feed the existing `*_of_timeRegularityBlackBox` / `*_of_blackBox`
   consumers. No new geometry — the Ricci-flow identities are already there.

**Mathematical source (paper level):** Hamilton/DeTurck short-time existence gives, for a
smooth closed initial metric, a smooth family `g(t)` on `[0,T) × M` solving Ricci flow, smooth
jointly in `(t,x)` and extending smoothly to `t=0`. Morgan–Tian Ch. 3 (and the GSM Ricci-flow
texts under `RicciFlow/`) treat the regularity. The Lean side only needs the *output*: a
`ContMDiffOn (ℝ×M) ⊤` metric family on the relevant `D.carrier ×ˢ M`.

---

## 4. Scope checklist (what's in / out)

**In scope (you):** the joint-smoothness solution record + §2a–2d structures + the
`UniqueDiffWithinAt` of `D.carrier`. Roughly: one regularity theorem + ~4 structure-builder
lemmas, each "smoothness ⇒ derivative exists / Clairaut swap / inverse differentiates."

**Out of scope (done):** `∂ₜg=−2Ric`, `∂ₜg⁻¹=2Ric`, Christoffel variation + `∂ₜΓ` reduction,
Ricci identity + 2nd Bianchi, `∂ₜRic`/`∂ₜS`/`∂ₜRm04` Hamilton RHS, the dim-3 KN diffusion
split `ΔRm04 = KN(ΔRic,ΔS,g)`, all the BBS Bernstein/Bochner machinery.

**Independent of you:** the BBS combinatorial assembly (`StarSum2` spatial decomposition →
time recursion → `extends_of_rmBounded`) is being done in parallel and only consumes the
*already-proved* `∂ₜ∇ᵏRm` producer, not these black boxes directly.

---

## 5. Entry points to read first
- `Evolution/BlackBox.lean` — all the assumption packages + their consumers in one file.
- `Evolution/Metric/Basic.lean:241,270` — the two metric-regularity structures.
- `Evolution/Connection/MetricCovDerivProducer.lean` — the `∂ₜ∇g → ∂ₜΓ` chain that consumes 2d.
- `Evolution/Ricci/Commutator.lean`, `Ricci/GammaCoord.lean` — the (already proved) Ricci
  evolution reduction that sits on top.
- Search the repo for `…TimeRegularityBlackBox…` / `…VariationBlackBox…` to see every
  consumer; each is a `theorem …_of_…blackBox` waiting for the discharged structure.
