# POINCARÉ PROGRAM PLAN — Perelman's proof as the project endpoint

Written 2026-07-05 (planning lane), at the user's request: a detailed plan for
taking **Perelman's proof of the Poincaré conjecture, excluding its topological
part**, as the long-range endpoint.  Anchor text: **Morgan–Tian** (local LaTeX
under `RicciFlow/Morgan-Tian/`) — the only complete Poincaré-only writeup, and
the project rule is to follow the book's structure exactly.  Chapter names
below refer to its files (`prelim` (two chapters), `flowbasics`, `maxprin`,
`converge2`, `newcompar`, `newcomp2`, `noncoll`, `temp2kappa`, `bddcurvbdddist`,
`singlimit2`, `stdsoln`, `surgery` (4 chapters), `energy1`, `canonnbhd`).
There is no `nonnegcurv.tex` in this snapshot: that chapter (`Manifolds of
non-negative curvature`, label `nonnegcurv`) is the second chapter of
`prelim.tex`, starting at `prelim.tex:1068`.

Live status refreshed 2026-08-27.  The current companion sources are:

* `DimensionThree/PositiveRicci/AxiomCheck.lean` for the checked Hamilton
  endpoint (Phase P0);
* `Compactness/` for the provider-native Hamilton compactness implementation;
* `../../../Comparison/P1_COMPARISON_PLAN.md` for the ordered P1a--P1c
  comparison-geometry campaign;
* `Perelman/L_GEOMETRY_PLAN.md` for the active P2 execution lane.

The former `DimensionThree/HAM3_BLACKBOX_PLAN.md` and
`HCGCompactness/PROJECT_MAP.md` paths no longer exist in this checkout and must
not be used as live status sources.  Older dated entries in this document are
historical snapshots; the inventory, phase annotations, execution order, and
scale estimate below are the current authority.

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
  (uses T2's pieces + elementary 3-manifold topology);
* T4 — (**open ruling, 2026-08-27 audit; not settled here**) needed only if
  P8 is run in the Poincaré-only form that skips Morgan–Tian's π₂ section:
  every time-slice component of the Ricci flow with surgery started from a
  closed simply-connected `M` is again closed and simply connected, hence has
  `π₂ = 0`.  Without T4 the π₂ half of `energy1` is IN scope and pulls in the
  Sacks–Uhlenbeck minimal-2-sphere layer.  See P8 in §2 and §3 items 11–13.

**Endpoint (conditional form):**
`poincare_of_inputs : Closed3Manifold M → SimplyConnected M →
PoincareTopologyInputs M → PerelmanAnalyticInputs M → HomeomorphicToSphere M`
— where `PerelmanAnalyticInputs` is expected to be EMPTY by program end (every
analytic item below is planned to be proved, none cited), and the topology
bundle stays.  If any analytic item is later demoted to a citation, it moves
into an explicit bundle field, never a hidden wrapper (2026-07-05 audit rule).

## 1. What the tree already has (live inventory, 2026-08-27)

| Layer | State |
|---|---|
| Tensor/curvature calculus, evolution equations | mature (`Evolution/` 51 files; Uhlenbeck/BBS bricks) |
| Weak maximum principles (scalar + tensor) | in-tree (`MaximumPrinciple/`) |
| Dimension-3 pinching (Hamilton §9/§10), compact smooth flow | checked (`DimensionThree/`) |
| Short-time existence (DeTurck) | checked on the P0 path; included in the direct axiom audit |
| Extension/maximal time | checked on the P0 path through `exists_max_flow` and `rmUnbounded_of_maximal` |
| **Riemannian volume, divergence thm, IBP, L², volume variation** | **0-sorry** (`Analysis/Integration/`) |
| W/F entropy definitions + first-variation lane | started (`Entropy/`) |
| Comparison geometry: geodesics, Jacobi, Gauss lemma, index form, convexity, Bonnet–Myers, Hopf–Rinow(proper), injectivity radius | substantial; the Bishop–Gromov/CGT producers used by P0 are checked |
| Hamilton compactness (M–T Ch `converge2` ≈ MSM135 3.9/3.10) | provider-native endpoint checked under `RicciFlow/Compactness/` |
| Hamilton positive-Ricci endpoint | `hamilton_positive_ricci` checked and direct-axiom audited |
| Fixed-manifold L-geometry | monotonicity, zero-time limit, half-dimension fence, half-open late floor, and arbitrary-tail fixed-time ball bound checked; `smooth_nlc` remains absent |
| Smooth gluing / jet splice (surgery seed) | engine built, 2 gates (`hglue` lane) |
| Space forms / quotients | active lane |
| Curvature *pinched toward positive* for generalized flows / RFWS | **absent** — the checked pinching is the compact smooth-flow version only (§3 item 11) |
| Shi derivative estimates | compact whole-manifold versions checked; complete-flow `estimate_complete` is a `sorry`, local ball version `shiRm1_ball` does not exist (§3 item 12) |
| Parabolic rescaling formalism, pointed flow sequences | in-tree |
| Final Poincaré assembly | `poincare_of_inputs` is not yet declared |

Missing layers are the subject of §3.

Two traps for future agents (2026-08-27 audit).
`Compactness/CheegerGromov/Pointed/Compactness.lean:1321` defines
`metricCompactness` as `by sorry`; it is dead legacy code superseded by the
live producer of the SAME NAME at `Compactness/Metric/Endpoint.lean:48`, which
is the one P0 actually routes through.  And `Estimates/Shi/Complete.lean:2866`
(`BernsteinTower.estimate_complete`) is a `sorry` that is already imported and
applied at `Compactness/Shi/Local.lean:512`.  Both are off the audited P0 path;
neither may be cited as “checked”.

## 2. Phase plan (mapped to Morgan–Tian)

**P0 — Hamilton positive Ricci endpoint (complete).**  The provider-native
chain through short-time existence, maximal extension, volume/injectivity,
Hamilton compactness, and space forms closes
`HamiltonPositiveRicci.hamilton_positive_ricci`.  The dedicated
`PositiveRicci/AxiomCheck.lean` audit reports only `propext`, classical choice,
and quotient soundness.  P0 is **100%** as a theorem and remains the program's
completed toolchain validator.  This does not complete any later Poincaré
phase automatically.

**P1 — Comparison-geometry and volume upgrades** (M–T `prelim`, both chapters).
1. P1a Bishop–Gromov relative volume comparison.  Route: polar-coordinates
   Jacobian along radial geodesics + Riccati comparison; below-injectivity
   version needs NO cut locus, and upper bounds extend past `inj` via
   `vol(exp(B)) ≤ ∫_B Jac` (surjectivity onto balls from Hopf–Rinow).  Assets:
   `JacobiFormula`, Jacobi-field ODE bricks, `riemannianVolumeMeasure`.
   **Live status:** the comparison/packing producers consumed by the P0
   compactness route are checked.  Any broader Morgan–Tian use must still be
   audited against its exact hypotheses rather than inferred from P0.
2. P1b Cheeger–Gromov–Taylor injectivity-radius decay (volume ⟹ inj via
   Cheeger's lemma / short geodesic loops).  **Live status:** the P0/Hamilton
   producer is checked (`intrInj_ge_cgt` through `injDecay_of_bg`).
3. P1c Laplacian comparison + Busemann functions + Cheeger–Gromoll splitting
   + the **Cheeger–Gromoll soul theorem** (needed by P3's asymptotic-soliton
   argument; M–T `prelim.tex` ch. 2, `soul` stated at `prelim.tex:1304`).
   The soul theorem is a separate classical endpoint, not a corollary of
   splitting, and the 2026-08-27 audit found it consumed in two different
   ways: `temp2kappa.tex:2293` uses “positive curvature ⇒ the soul is a
   point”, while `temp2kappa.tex:3581/3612/3714/3727` use soul POINTS `p_k`
   of noncompact κ-solutions as the basepoints of a blow-up sequence.  Both
   uses belong in the frozen P1c consumer list.  (~3–4 months.)
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

Execution plan: `Perelman/L_GEOMETRY_PLAN.md`.  The fixed-manifold ordinary
flow layer is built first; generalized surgery-space-time paths are a later
extension and must not contaminate the basic L-length API.

**Live status:** the compact fixed-manifold L0–L7 core is essentially complete:
`redVolume_anti` and `redVolume_zero_lim` are checked. The later chain now also
contains checked `exists_redLen_le`, `redVolume_late_low`, and the arbitrary-
tail fixed-terminal estimate `redVolume_ball_eta`. The theorem `smooth_nlc` is
still unstated and unproved (**0%**). Its current missing producer chain is

```text
shiRm1_ball -> lGrad_ball -> lRegSpeed_unif
  -> lMetric_ball + lRegRange_unif -> lExp_ball_unif
  -> redVolume_ball_unif
  + redVolume_late_low -> IsKappaNoncollapsed -> smooth_nlc.
```

The obstruction is not the Gaussian tail or late reduced-volume floor: both
are now complete. The present short-scale threshold uses a global compact-slab
gradient constant and is chosen after the terminal time; compactness cannot
uniformize it on `[a, omega)`. A genuine scale-invariant local derivative
estimate on a smaller cylinder inside the controlled parabolic ball is
required. The exact missing lowest producer is `shiRm1_ball`; the existing Shi
theorems require curvature control at every spatial point and cannot supply it
from `FlowMetricBall.IsRmControlled`. The remaining complete bounded-curvature
L8 work and the surgery/eventwise L9 extension stay separate later endpoints.

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
**Prerequisite added by the 2026-08-27 audit:** essentially every statement of
`bddcurvbdddist` and `singlimit2` is hypothesized on flows whose curvature is
*pinched toward positive* (`bddcurvbdddist.tex:22`, `:65`, `:140`, weak form at
`:709`) — the Hamilton–Ivey estimate in its GENERALIZED-flow form, preserved by
surgery and stable under blow-up limits.  The checked `DimensionThree/`
pinching is the compact smooth-flow version and does not supply this.

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

**P8 — Finite-time extinction** (M–T `energy1`).  The 2026-08-27 audit found
the previous entry described only the second of TWO analytically different
halves, and mislabelled `W₂`:

1. P8a, the π₂ half (`energy1.tex:280` ff.).  `W₂(t)` is the minimal AREA of a
   homotopically non-trivial 2-sphere in a component; it is used to prove that
   after a finite time every component has trivial π₂.  Its existence theory is
   harmonic-map / minimal-sphere theory: `energy1.tex:597` cites Sacks–Uhlenbeck
   Theorem 3.3 directly, and the α-energy / Palais–Smale / bubbling argument is
   reproduced at `energy1.tex:597-636`.  This layer is not in the tree.
2. P8b, the π₃ half (`energy1.tex:93` ff.).  A non-trivial element of `π₃(M)`
   is represented in `π₂(ΛM)`, the width `W` of a loop sweepout is estimated
   under curve-shortening plus ramps, and the derivative estimate forces
   extinction (input T1).  This is the Altschuler–Grayson-grade
   curve-shortening layer of §3-7.  It consumes P8a: the loop-width argument
   runs on components with trivial π₂.

**Open ruling, required before P8 starts.**  Either (a) build the
Sacks–Uhlenbeck minimal-2-sphere layer — a genuine new analytic frontier,
comparable in size to §3-7 — or (b) take the Poincaré-only shortcut and skip
P8a, which is legitimate ONLY with T4 of §0 added to the topology bundle, since
T4 is exactly the statement that no time-slice component ever acquires
non-trivial π₂.  Do not leave the pre-audit situation, in which the plan
assumed (b)'s conclusion while §3 declared harmonic-map machinery out of scope
and §0 carried no T4.

Dependency correction: P8's statement consumes Theorem `MAIN`, the RFWS defined
for all `t ∈ [0,∞)` (`energy1.tex:7`).  P8 may therefore be DEVELOPED against
the RFWS interface as soon as P6b exists, but it is not provable before P7.
(~5–8 months for P8b, plus a comparable block for P8a under ruling (a).)

**P9 — Assembly.**  `poincare_of_inputs` from P6–P8 + T1–T3, plus T4 if P8
took ruling (b).  (~1–2 months.)

## 3. Infrastructure gap list (the direct answer to "还需要哪些东西")

Ordered by how many phases consume them:

1. **Linear parabolic PDE on closed manifolds** (existence, uniqueness,
   regularity/Schauder-or-L² for scalar and tensor equations with
   time-dependent smooth coefficients).  Consumers: P0/A1 (conjugate heat),
   P5, P8.  **Current ruling:** the P0-required closed-manifold path is checked;
   noncompact standard-solution and curve-shortening variants remain future
   scope and must be audited separately.
2. **Volume comparison package** (P1a/P1b): Bishop–Gromov + Cheeger lemma +
   CGT.  Consumers: P0, P2, P3.  **Current ruling:** the P0/Hamilton uses are
   discharged; audit any stronger P2/P3 use before declaring the whole package
   complete.
3. **L-geometry layer** (P2): L-geodesics through reduced volume.  The compact
   fixed-manifold monotonicity and zero-time normalization are checked; the
   live gap is the short-scale ball route to `smooth_nlc`, whose lowest
   missing producer is the local Shi estimate of item 12.
4. **Splitting/Busemann + the Cheeger–Gromoll soul theorem + Toponogov
   (used-statements-only)** (P1c/P1d).  Consumers: P3, P4.  The soul theorem
   (`prelim.tex:1304`) is a separate endpoint from splitting and is consumed
   by `temp2kappa` both as “soul is a point” (2293) and as soul BASEPOINTS of
   noncompact κ-solutions (3581, 3612, 3714, 3727).
5. **Hamilton's Harnack inequality** (matrix LYH).  Consumer: P3.
6. **Strong maximum principles** (scalar Hopf lemma; tensor strong MP with
   kernel holonomy/splitting).  Consumers: P3 (soliton classification), P5.
7. **Curve-shortening flow in evolving backgrounds** (existence, curvature
   bounds, Grayson-type behavior as M–T uses it).  Consumer: P8b only.  The
   analytic LAYER is self-contained and delegable; the P8 endpoint it feeds is
   not (it consumes item 13 or T4, and Theorem `MAIN` from P7).
8. **Generalized/space-time flows + the RFWS object** (P6b).  Consumers:
   P4, P6, P7, P8.  Design-heavy; prototype early, freeze late.
9. **Compactness extensions** (P4): Hamilton compactness for generalized flows
   and local limits.  Build on the checked `RicciFlow/Compactness/` machinery,
   not the removed `HCGCompactness/PROJECT_MAP.md` path.
10. **Noncompact uniqueness** (standard solution scope only; M–T's argument,
    not full Chen–Zhu).  Consumer: P5.
11. **Hamilton–Ivey pinching for generalized flows and RFWS** (“curvature
    pinched toward positive”): preserved by surgery, stable under blow-up
    limits, including the weak form at `bddcurvbdddist.tex:709`.  Consumers:
    P4, P6, P7.  Not supplied by the checked compact smooth-flow pinching.
12. **Shi derivative estimates beyond the compact whole-manifold case.**  Two
    concrete holes: `BernsteinTower.estimate_complete`
    (`Estimates/Shi/Complete.lean:2866`) is a `sorry` already consumed at
    `Compactness/Shi/Local.lean:512`; and the LOCAL ball estimate
    `shiRm1_ball` — currently the lowest missing P2 producer — does not exist
    at all.  Consumers: P2 (`smooth_nlc`), P3, P4, L8.
13. **(Conditional on the P8 ruling) minimal 2-spheres / Sacks–Uhlenbeck.**
    Needed iff P8a is proved rather than replaced by input T4.  Consumer: P8.
14. (Excluded, input bundle) 3-manifold topology T1–T3, plus T4 under P8
    ruling (b).

Explicitly NOT needed (avoid scope creep): full Alexandrov-space theory
(M–T avoids it; only Toponogov-level statements), prime decomposition and
geometrization-grade topology, Perelman's §8–§10 function theory beyond what
`noncoll` uses.  The former fourth entry, “harmonic-map spectral machinery
(M–T's extinction is curve-shortening based)”, was WRONG and is withdrawn
(2026-08-27 audit): M–T's extinction chapter uses Sacks–Uhlenbeck minimal
2-spheres for its π₂ half.  Whether that layer is in or out of scope is the
open P8 ruling above, not a settled exclusion.

## 4. Execution order, parallel lanes, and the first quarter

Dependency spine:
```
P0 Hamilton positive Ricci ───────────────────────────── complete
P2 smooth_nlc ───────────────┐
P1c/P1d ─────────────────────┴──→ P3 ──→ P4 ──┐
P5 standard solution ──────────────────────────┼──→ P6/P7 ──┐
P6b RFWS object ────────────────────────────────┘            ├──→ P9
P6b RFWS object ────────────────────────────────→ P8 ────────┘
```

The last row means P8 can be DEVELOPED against the RFWS interface as soon as
P6b exists; its final statement still consumes P7's Theorem `MAIN`, and its
π₂ half additionally consumes §3 item 13 or input T4.

Recommended immediate order:

1. **Build the missing local Shi producer.** Prove `shiRm1_ball` by a spatial
   cutoff/local maximum-principle argument on a controlled parabolic ball, with
   the estimate stated only on a strictly smaller cylinder.
2. **Finish the compact smooth-flow P2 consumer chain:** adapt this through
   `lGrad_ball`, local speed/metric/range/exponential bounds, and
   `redVolume_ball_unif`; combine it with checked `redVolume_late_low` to prove
   `smooth_nlc`.
3. **Audit and start P1c/P1d** against the exact P3 consumers: splitting/
   Busemann first, and only the Toponogov statements Morgan–Tian actually uses.
4. **Design P6b early but do not contaminate P2:** write and review the RFWS
   event/seam object before P4–P8 depend on it.
5. After compact `smooth_nlc`, implement the L8 complete bounded-curvature
   extension and only then the surgery/eventwise L-length extension.
6. **Two rulings that must be made before their phases open, not during
   them:** the P8a/T4 ruling of §2, and how “pinched toward positive” will be
   carried by the P6b RFWS object (it is a hypothesis of nearly every P4/P6/P7
   theorem, so the object must be able to state it from day one).

## 5. Honest scale estimate

Use two separate denominators:

* final theorem `poincare_of_inputs`: **0%**, because it is not yet declared;
* P0 theorem `hamilton_positive_ricci`: **100%**, direct-axiom audited;
* fixed compact-flow L-geometry through reduced-volume monotonicity and
  zero-time normalization: about **99%** dedicated machinery, with both named
  capstones **100%**;
* `smooth_nlc`: **0%** as a theorem; its dedicated reduced-volume-to-
  noncollapse L8--L9 machinery is about **76–78%**;
* full P0–P9 program infrastructure: approximately **10–18%**, with an
  explicitly unreliable denominator (see the warning below).

The last range uses the phase workload, not file or lemma counts, and avoids
double-counting infrastructure shared by P0, P1, and P2.  The old **3–5%**
snapshot is superseded: it predates the axiom-clean P0 endpoint and both
reduced-volume capstones.  The former 2.5–4 year calendar estimate is also not
treated as current until the P3–P6 design work is re-estimated.

**Denominator warning (2026-08-27 audit).**  P3–P8 have never been scoped at
file level, and this audit found three consumed layers the plan had not counted
at all (§3 items 11–13).  Any single percentage here is a guess about work that
has not been decomposed: treat the phase ordering and the gap list as the real
content, and the number as an upper-bounded guess.  The per-phase month
estimates are stale for the opposite reason — they predate the observed lane
throughput (the P2 lane went from kickoff on 2026-08-15 to a checked L0–L7 core
plus most of L8 within two weeks, at 153 files and ~63k lines) — so they should
be re-derived from measured lane velocity or dropped, not cited as planning
input.

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
- 2026-08-21 (P2 ordinary L-geometry): the fixed-manifold L0--L2 layer and the
  current L3 regularized-ODE layer are migrated and focused-green.  Local phase
  and intrinsic solutions have existence and arbitrary-base-time germ
  uniqueness.  In `Perelman/LGeometry/Exp.lean`, witness independence now
  propagates across connected overlap domains, the totalized maximal curve
  agrees with every witness, and a jointly smooth local phase flow produces
  regularized families for nearby initial tangent vectors.  Thus the
  regularized family is jointly smooth at `s=0`, and `lExp` is jointly smooth
  on a uniform short positive-time interval, with the correct `A(0)=2Z`
  normalization.

  The exact next P2 producer is `lRegFamily_extend`, which must continue the
  smooth parameter family across compact subintervals of a witnessed maximal
  solution before full-domain positive-time smoothness is claimed.  The
  capstone `redVolume_anti` remains **0%**; dedicated L-geometry is about
  **22--24%**, reusable generic prerequisites about **65--75%**, P2 remains
  below **1%**, and the whole program estimate remains **3--5%**.
- 2026-08-27 (live status supersedes the earlier snapshots): the dedicated
  Hamilton axiom check is green for short-time existence, the provider-native
  compactness route, and `hamilton_positive_ricci`; P0 is therefore 100% as a
  theorem.  `redVolume_anti` and `redVolume_zero_lim` are each stated, proved,
  and focused-check green. The later `exists_redLen_le`, `redVolume_late_low`,
  and fixed-terminal `redVolume_ball_eta` are also checked and pass the P2
  standard-axiom audit. `smooth_nlc` remains unstated and unproved. Its exact
  lowest missing producer is `shiRm1_ball`, because all current checked Shi
  theorems require whole-manifold curvature control. The final
  `poincare_of_inputs` theorem remains 0%; full-program infrastructure is
  estimated at 15–25% with the overlap caveat in §5.
- 2026-08-28 (plan audit against the Morgan–Tian source, performed 2026-08-27;
  read-only review, no code changed):
  three substantive plan defects and two smaller ones were fixed in this
  document.  (i) P8 described only its curve-shortening half and mislabelled
  `W₂`; the π₂ half needs Sacks–Uhlenbeck minimal 2-spheres, so the old
  “harmonic-map machinery not needed” exclusion is withdrawn and an explicit
  ruling — build P8a, or add T4 to the topology bundle — is now required before
  P8 starts.  (ii) P1c was missing the Cheeger–Gromoll soul theorem, which
  `temp2kappa` uses as basepoint data for noncompact κ-solutions.  (iii)
  “curvature pinched toward positive” for generalized flows/RFWS is consumed
  throughout P4/P6/P7 but was listed nowhere; the checked `DimensionThree/`
  pinching is only the compact smooth-flow version.  Also added: Shi beyond the
  compact whole-manifold case as a named gap (`estimate_complete` is a `sorry`,
  `shiRm1_ball` does not exist), the `nonnegcurv.tex` file correction
  (`prelim.tex:1068`), and the dead `metricCompactness := by sorry` name clash.
  Scale estimate lowered to 10–18% with an explicit denominator warning.  No
  theorem status changed by this audit: `smooth_nlc` and `poincare_of_inputs`
  both remain 0%, and P0 remains 100% and axiom-clean.
