# POINCARÉ PROGRAM PLAN — Perelman's proof as the project endpoint

Written 2026-07-05 (planning lane), at the user's request: a detailed plan for
taking **Perelman's proof of the Poincaré conjecture, excluding its topological
part**, as the long-range endpoint.  Anchor text: **Morgan–Tian** (local LaTeX
under `RicciFlow/Morgan-Tian/`) — the only complete Poincaré-only writeup, and
the project rule is to follow the book's structure exactly.  Chapter names
below refer to its files (`prelim`, `nonnegcurv`, `flowbasics`, `maxprin`,
`converge2`, `newcompar`, `newcomp2`, `noncoll`, `temp2kappa`, `bddcurvbdddist`,
`singlimit2`, `stdsoln`, `surgery` (4 chapters), `energy1`, `canonnbhd`).

Companion documents: `DimensionThree/HAM3_BLACKBOX_PLAN.md` (the Hamilton
endpoint = Phase P0 of this program), `HCGCompactness/PROJECT_MAP.md` (the
compactness lane).

## 0. Scope ruling and the endpoint statement

**"除拓扑 surgery 部分" is interpreted as:** the GEOMETRIC/ANALYTIC surgery
construction (δ-necks, the surgery metric, Ricci flow with surgery as an
analytic object, its noncollapsing and canonical-neighborhood induction) is IN
scope; the purely TOPOLOGICAL inputs and readouts are OUT of scope and enter as
an explicitly cited input bundle, exactly in the `MetricCompactnessInputs`
pattern.  The excluded topology bundle (`PoincareTopologyInputs`, to be stated
at assembly time) contains, per Morgan–Tian's usage:

* T1 — a closed simply-connected 3-manifold has `π₃ ≠ 0` (homotopy-sphere
  facts: Hurewicz + Poincaré duality; not in Mathlib);
* T2 — reconstruction after extinction: if the Ricci flow with surgery on `M`
  goes extinct in finite time, `M` is a connected sum of space-form quotients
  and `S²×S¹`-pieces (the topological bookkeeping of surgeries);
* T3 — the final identification: a simply-connected such connected sum is `S³`
  (uses T2's pieces + elementary 3-manifold topology).

**Endpoint (conditional form):**
`poincare_of_inputs : Closed3Manifold M → SimplyConnected M →
PoincareTopologyInputs M → PerelmanAnalyticInputs M → HomeomorphicToSphere M`
— where `PerelmanAnalyticInputs` is expected to be EMPTY by program end (every
analytic item below is planned to be proved, none cited), and the topology
bundle stays.  If any analytic item is later demoted to a citation, it moves
into an explicit bundle field, never a hidden wrapper (2026-07-05 audit rule).

## 1. What the tree already has (assets inventory, 2026-07-05)

| Layer | State |
|---|---|
| Tensor/curvature calculus, evolution equations | mature (`Evolution/` 51 files; Uhlenbeck/BBS bricks) |
| Weak maximum principles (scalar + tensor) | in-tree (`MaximumPrinciple/`) |
| Dimension-3 pinching (Hamilton §9/§10) | checked (`DimensionThree/`) |
| Short-time existence (DeTurck) | active lane, ~5 frontier files |
| Extension/maximal time | active lane (`extends_of_rmBounded` + BBS track) |
| **Riemannian volume, divergence thm, IBP, L², volume variation** | **0-sorry** (`Analysis/Integration/`) |
| W/F entropy definitions + first-variation lane | started (`Entropy/`) |
| Comparison geometry: geodesics, Jacobi, Gauss lemma, index form, convexity, Bonnet–Myers, Hopf–Rinow(proper), injectivity radius | substantial (`Geometry/Comparison/`, `Exponential/`) |
| HCG compactness (M–T Ch `converge2` ≈ MSM135 3.9/3.10) | ~30%, active (`HCGCompactness/`) |
| Smooth gluing / jet splice (surgery seed) | engine built, 2 gates (`hglue` lane) |
| Space forms / quotients | active lane |
| Parabolic rescaling formalism, pointed flow sequences | in-tree |

Missing layers are the subject of §3.

## 2. Phase plan (mapped to Morgan–Tian)

**P0 — Hamilton positive Ricci endpoint (running).**  `ham3_main` modulo 8
frontiers; see `HAM3_BLACKBOX_PLAN.md`.  P0 is the program's toolchain
validator: it forces short-time, extension, compactness, NLC(W-route), and
space forms to production quality.  Est. 12–20 months, all lanes already live.

**P1 — Comparison-geometry and volume upgrades** (M–T `prelim`, `nonnegcurv`).
1. P1a Bishop–Gromov relative volume comparison.  Route: polar-coordinates
   Jacobian along radial geodesics + Riccati comparison; below-injectivity
   version needs NO cut locus, and upper bounds extend past `inj` via
   `vol(exp(B)) ≤ ∫_B Jac` (surjectivity onto balls from Hopf–Rinow).  Assets:
   `JacobiFormula`, Jacobi-field ODE bricks, `riemannianVolumeMeasure`.
   **Also discharges the HCG honest inputs A0′ (`VolumeComparisonInput`) and
   `PackingBound`.**  (~1–2 months.)
2. P1b Cheeger–Gromov–Taylor injectivity-radius decay (volume ⟹ inj via
   Cheeger's lemma / short geodesic loops).  **Discharges HCG A0.** (~2–3 months.)
3. P1c Laplacian comparison + Busemann functions + Cheeger–Gromoll splitting
   (needed by P3's asymptotic-soliton argument; M–T `nonnegcurv`).  (~3–4 months.)
4. P1d Toponogov comparison, the M–T-used statements only.  Hardest classical
   item; audit `temp2kappa`/`bddcurvbdddist` first for the exact list actually
   consumed and prove only those.  (~3–6 months, deferrable until P3.)

**P2 — Perelman reduced geometry (L-length) + κ-noncollapsing** (M–T
`newcompar`, `newcomp2`, `noncoll`).
L-geodesics, L-exponential, L-Jacobi/index comparison, reduced length/volume,
monotonicity (Jacobian route, no PDE existence), κ-noncollapsing of smooth
flows, and the bounded-curvature-complete-flow chapter (`newcomp2`) it leans
on.  This layer is mandatory here even though P0 fills `ham3_noncollapse` via
the W-route: **surgery-stable noncollapsing (P6) is L-length-based.**
Measure-theoretic pole: integrating over the L-exponential domain with a
measurable cut-type decomposition.  (~8–12 months.)

**P3 — κ-solutions** (M–T `temp2kappa`).  Ancient κ-noncollapsed solutions:
Hamilton's Li–Yau–Hamilton Harnack inequality (new tensor-MP computation, big
but native to the tree's strengths), strong maximum principle (scalar Hopf
lemma + tensor kernel-holonomy splitting — NEW layer, see §3-6), asymptotic
shrinking soliton via reduced volume (consumes P2), classification of 3d
shrinking solitons, compactness of κ-solutions, universal κ, the
`canonnbhd` appendix vocabulary.  The heaviest pure-geometry phase.
(~6–10 months.)

**P4 — Bounded curvature at bounded distance + limits of generalized flows**
(M–T `bddcurvbdddist`, `singlimit2`).  Blow-up arguments against κ-solution
structure; extends the HCG compactness interface to generalized (space-time)
flows and partial/local convergence.  Depends: P2, P3, HCG done.  (~4–6 months.)

**P5 — The standard solution** (M–T `stdsoln`).  Existence + uniqueness +
canonical-neighborhood structure of the standard flow on ℝ³.  Noncompact
existence/uniqueness is genuinely hard analysis; M–T's own route keeps it
semi-self-contained.  Needs the linear parabolic layer (§3-1) at full strength.
(~4–6 months.)

**P6 — Surgery** (M–T `surgery.tex` chapters 13–15: δ-neck surgery, Ricci flow
with surgery as a formal object, controlled RFWS).  Two distinct workloads:
1. P6a the surgery METRIC: δ-neck recognition + the gluing construction —
   direct continuation of the live `hglue` lane (jet splice engine done).
2. P6b the RFWS FORMAL OBJECT: space-time generalized flows, surgery times,
   parameter sequences `(r_i, δ_i, κ_i)`.  This is the largest formalization
   DESIGN problem of the program (manifold changes at surgery times); M–T's
   space-time formulation is the design template.  Prototype the object early
   (see execution order).  (~6–9 months combined.)

**P7 — Noncollapsing and canonical neighborhoods for RFWS + existence of the
controlled flow** (M–T `surgery.tex` ch. 16 + completion chapter).  The grand
induction on surgery times: L-length arguments crossing surgery regions
(consumes P2 hard), canonical neighborhoods propagate, parameters can be
chosen.  The assembly summit of the program.  (~5–8 months.)

**P8 — Finite-time extinction** (M–T `energy1`).  Curve-shortening flow in an
evolving metric (Altschuler–Grayson-grade parabolic theory for curves — new
analytic layer, §3-7), ramps, width monotonicity `W₂`, extinction for
`π₃ ≠ 0` (input T1).  Independent of P3–P7 except for RFWS vocabulary — can
run in parallel after P6b's object exists.  (~5–8 months.)

**P9 — Assembly.**  `poincare_of_inputs` from P6–P8 + T1–T3.  (~1–2 months.)

## 3. Infrastructure gap list (the direct answer to "还需要哪些东西")

Ordered by how many phases consume them:

1. **Linear parabolic PDE on closed manifolds** (existence, uniqueness,
   regularity/Schauder-or-L² for scalar and tensor equations with
   time-dependent smooth coefficients).  Consumers: P0/A1 (conjugate heat),
   P5, P8; the DeTurck short-time lane is its seed.  **Start first.**
2. **Volume comparison package** (P1a/P1b): Bishop–Gromov + Cheeger lemma +
   CGT.  Consumers: P0 (discharges HCG A0/A0′ making conditional 3.9 → closer
   to unconditional), P2, P3.  **Also start first — it is the highest
   value-per-effort item in the whole program.**
3. **L-geometry layer** (P2): L-geodesics through reduced volume.  Consumers:
   P3, P7.
4. **Splitting/Busemann + Toponogov (used-statements-only)** (P1c/P1d).
   Consumers: P3, P4.
5. **Hamilton's Harnack inequality** (matrix LYH).  Consumer: P3.
6. **Strong maximum principles** (scalar Hopf lemma; tensor strong MP with
   kernel holonomy/splitting).  Consumers: P3 (soliton classification), P5.
7. **Curve-shortening flow in evolving backgrounds** (existence, curvature
   bounds, Grayson-type behavior as M–T uses it).  Consumer: P8 only —
   self-contained lane, delegable.
8. **Generalized/space-time flows + the RFWS object** (P6b).  Consumers:
   P4, P6, P7, P8.  Design-heavy; prototype early, freeze late.
9. **Compactness extensions** (P4): HCG for generalized flows, local limits.
   Builds directly on the HCG Step-D direct-limit machinery.
10. **Noncompact uniqueness** (standard solution scope only; M–T's argument,
    not full Chen–Zhu).  Consumer: P5.
11. (Excluded, input bundle) 3-manifold topology T1–T3.

Explicitly NOT needed (avoid scope creep): full Alexandrov-space theory
(M–T avoids it; only Toponogov-level statements), prime decomposition and
geometrization-grade topology, Perelman's §8–§10 function theory beyond what
`noncoll` uses, harmonic-map spectral machinery (M–T's extinction is
curve-shortening based).

## 4. Execution order, parallel lanes, and the first quarter

Dependency spine:
```
P1a/P1b ──→ (HCG inputs discharged) ──→ P0 closes ──┐
   §3-1 parabolic layer ──→ P0/A1 ──────────────────┤
P1c/P1d ──→ P3 ──→ P4 ──→ P7 ──┐                    ├──→ P9
P2 ────────↗           P5 ──→ P6 ──→ P7             │
P6b prototype ─────────↗       P8 ──────────────────┘
```

Recommended immediate lanes (next ~3 months, all parallelizable with today's
active work):
1. **P1a Bishop–Gromov** (new lane; highest leverage: unblocks HCG honest
   inputs + starts the comparison package).
2. **§3-1 parabolic layer**, scoped to scalar equations on closed manifolds
   (continues the ShortTime lane's linear machinery; target: conjugate-heat
   existence = `ham3_noncollapse`/A1).
3. Continue the running lanes untouched: HCG Step-D/D3, B1 assembly,
   short-time, extension, space forms, Entropy/F.
4. **P6b design note only** (no implementation): a 5-page RFWS object design
   against M–T's space-time definitions, to de-risk the largest unknown early.

## 5. Honest scale estimate

Sequential sum of the phase estimates is ≈ 40–70 months; with the parallelism
above and current multi-lane velocity, a realistic program span is **≈ 2.5–4
years**, with `ham3_main` (P0) landing first at 12–20 months as the toolchain
proof-of-concept.  Calibration: the HCG compactness lane (≈ one M–T chapter,
`converge2`) has taken ~1 month to reach ~30% with mature tensor
infrastructure underneath it; the program is ~15 such chapters of increasing
novelty, plus three genuinely new analytic layers (§3-1, -3, -7) and one design
problem (§3-8).  Percentage bookkeeping starts at: **Poincaré program ≈ 3–5%**
(= the P0-shared assets + integration/entropy layers + HCG progress, measured
against the full gap list).  Do not report higher numbers because P0 lanes are
far along — P0 itself is ≈ 15–20% of the program.

## Status log

- 2026-07-05: plan written (with `HAM3_BLACKBOX_PLAN.md`).  Decisions OPEN for
  the user: (i) adopt the program (this document is a plan, not a commitment);
  (ii) `ham3_noncollapse` Route A vs B (recommendation: A); (iii) green-light
  the two immediate new lanes (P1a Bishop–Gromov, §3-1 parabolic scalar layer).
- 2026-07-05 (later): user reports §3-1 (linear parabolic PDE) is essentially
  done by a collaborator, pending merge — gap list item 1 becomes an
  integration task, and NLC Route A's pole shrinks accordingly.  **P1a volume
  comparison green-lit and planned**: `Geometry/Comparison/
  VOLUME_COMPARISON_PLAN.md` (asset audit + stages V1–V3; V1 needs no new
  foundations — the integration layer and the Jacobi/Grönwall/Bonnet–Myers
  engines are all in-tree and 0-sorry).
