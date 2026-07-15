# GoodCoveringOrdered.lean — faithful (book-ordered) Step A redo

## 2026-06-30 — proper-metric topology bridge

Added `ProperMetricOn.top_eq`: any `ProperMetricOn` whose `realizes` field
identifies its metric edistance with the stored Riemannian emetric induces the
stored manifold topology. The proof compares the two pseudo-emetric structures
by extensionality on `edist`; the canonical Riemannian emetric already carries
the stored topology by construction.

This discharges the Step-C partition topology seam: metric balls from
`ProperMetricOn.ms` can be transported to the manifold topology before invoking
Mathlib's smooth partition-of-unity theorem.

Verification status: focused check and targeted module build passed; axiom
check for `ProperMetricOn.top_eq` uses only the usual project axioms.

Decision (2026-06-08, user): redo Step A faithfully to MSM135 Ch4, using the book's
**distance-ordered greedy net** (not the Zorn packing). The original plan isolated the
complete-pointed-Riemannian-to-proper-metric step as the sole Hopf--Rinow deferral.
That deferral is now discharged by `Comparison/HopfRinowProper.lean`, using the
intrinsic endpoint `hopf_rinow_expMapIntrinsic_surjective_minimizing`.

## Reuse (verified, correct) from `GoodCovering.lean`
λ (A1), `lambda_ratio_le`, the dist=pseudometric bridge (`RealizesEdist`), `lambdaBall`,
`lambdaBallC`, `mem_lambdaBallC_dist`, `PackingBound`. Only the NET and the cover/count
built on it change to the ordered version.

## Plan (faithful, book-exact)
1. **Keystone** `exists_min_dist_base`: in a proper metric space, the distance-to-`O`
   minimum over a nonempty closed set is attained. Riemannian properness is supplied
   by the checked Hopf--Rinow adapter at the instantiation layer.
2. **`S^α` closed** — the varying-radius λ-ball disjointness set is closed (book: "balls
   open ⟹ S^α closed"; really a lower-semicontinuity lemma).
3. **Ordered net** (book L897–955): greedy `Nat.rec` with `r^α = d(S^α,O)` the attained
   min (keystone); prove `r^α↗`, pairwise-disjoint `B(x^α,λ[r^α])`, and the minimality
   used in the cover.
4. **Book theorems**: lbl387 (cover `B(O,r)⊂⋃_{α≤A(r)}B(x^α,2λ[r^α])` + A(r)), lbl388,
   **lbl389** (`r^α≤2αλ[0]`), lbl390 (K'(r)), lbl391 (5 radii), lbl383 (7 properties).

## Honest scope
This is the largest single piece of Step A; (2)+(3) are intricate (dependent recursion +
topology). Building methodically, verified per step. The properness keystone is no
longer a black box. The remaining Step A item-3 geometric scale/convexity inputs stay
with the separate `GoodCoveringItem3`/§5 boundary.

## Status — abstract net FOUNDATION DONE + verified + sorry-free (2026-06-08)
**Architecture revised:** build abstractly in `[MetricSpace M][ProperSpace M]` (Mathlib metric API); the
minimiser is then a GENUINE theorem (no black box). The old "complete pointed Riemannian manifold ->
ProperSpace under its Riemannian distance" Hopf--Rinow black box is now discharged in the instantiation.
The earlier emetric keystone was the wrong abstraction; dropped. Done + sorry-free: `availSet` (S^alpha),
`isClosed_availSet` (closed via `isClosed_le` + `infDist`), `exists_min_dist_base` (greedy minimiser of
`d(.,O)` over a closed nonempty set, from `ProperSpace` + `IsCompact.exists_isMinOn` on the compact slice
`S inter closedBall O (d s0 O)`).

**NET RECURSION + PACKING also DONE + sorry-free (2026-06-09):** `forbidden` (prior balls' union),
`netList` (greedy net as accumulator List via clean STRUCTURAL recursion — `netList 0 = [O]`, each step
appends the `availSet` minimiser, stops when empty), `O_mem_netList`, `netList_succ_spec` (the appended
center is in `availSet` and minimises `d(.,O)` there), and **`netList_ballsDisjoint`** (the λ-balls of the
net are pairwise disjoint — the packing). KEY: accumulator List ⟹ plain `Nat.rec`, no strong recursion;
the appended center's `availSet`-membership gives ball-vs-prior disjointness (`Set.disjoint_iUnion_right`).

**lbl387 COVER CORE + r^α MONOTONE DONE + sorry-free + axiom-clean (2026-06-09):**
- Helpers: `netList_zero` (@[simp]), `netList_succ_stop`, `mem_netList_succ`, `meets_of_not_avail`
  (∉availSet ⟹ λ-ball meets a listed center's ball), `dist_lt_two_lam` (meeting + `d(c,O)≤d(p,O)` +
  Antitone λ ⟹ `dist p c < 2λ(d(c,O))` — the book's factor-2 upgrade).
- **`netList_cover`** = book L974–1004 (lbl387 cover core), pointwise form with the EXACT factor 2:
  if at stage α the net stopped (`availSet=∅`) or has a center past `d(p,O)`, then p is within
  `2λ(d(c,O))` of some center c with `d(c,O) ≤ d(p,O)`. The book's minimality reductio = the
  `hxmin`/`hpastα` case split; induction on α; sortedness NOT needed (case analysis replaces "prefix").
- `availSet_antitone`, `forbidden_mono`, `availSet_succ_subset` (book `S^{α+1}⊆S^α`),
  `netList_dist_le_avail` (chosen centers ≤ any still-available point), **`netList_sorted`**
  (book: `r^α = d(x^α,O)` non-decreasing, as `List.Pairwise`).
All `#print axioms` = [propext, Classical.choice, Quot.sound] — the abstract ordered-net layer is
GENUINELY sorry-free (properness is the `[ProperSpace M]` instance hypothesis, not a sorry).

**Lean gotchas this pass:** `subst hc` with `hc : c = O` eliminates the RHS variable `O` (a theorem
parameter!) — later literal `O` references die; avoid subst, use `rw [hc]` at use sites. `simp [hemp]`
fails when a @[simp] lemma (netList_zero) normalizes the goal but not hemp's LHS — use `rw [hemp]; simp`.
`push_neg` deprecated → `push Not`.

**lbl389 + SEPARATION + A(r) COUNT DONE + sorry-free + axiom-clean (2026-06-09):**
- `netList_separated` (distinct centers: `λ(r) ≤ d(x,y)` when `d(x,O)≤r`; from `ballsDisjoint` via
  `List.Pairwise.forall` + `Metric.mem_ball_self`).
- `netList_count_le` (lbl387 second half: ≤ `A r` centers in `B(O,r)`, abstract packing input `pack`
  = Bishop–Gromov at instantiation).
- `netList_dist_ge` (lbl389 lower: non-basepoint centers have `d(c,O) ≥ λ(0)`; one-liner from separated
  with x:=O, r:=0).
- **`netList_dist_le`** (lbl389 upper `r^α ≤ 2αλ(0)`): the book's one-line "string of balls" sketch made
  rigorous as the jump bound `r^{α+1} ≤ r^α + 2λ(0)`. Input `hint`: every `t ∈ [0, d(p,O)]` is an
  attained distance (WEAKER than geodesics — exactly what the proof needs; supplied by Hopf–Rinow
  minimizing geodesics at instantiation, where connectivity will matter). Proof: by_contra; the attained
  point q at distance `2λ0(α+1) < d(x,O)` is non-available ⟹ within `2λ(0)` of an earlier center c'
  (meets + λ≤λ(0)) ⟹ `d(q,O) < 2λ0 + 2λ0·α` = its own value. nlinarith closes the cast arithmetic.
All `#print axioms` clean.

**INSTANTIATION FOUNDATION DONE (2026-06-09; properness deferral discharged 2026-06-21):**
- `GoodCovering.lambda_continuous` (clean, `fun_prop`) — the abstract layer's `hlam` input; `hanti` =
  `lambda_antitone`, `hpos` = `lambda_pos` (already proved).
- **`exists_proper_realization`** (Instantiation section): a
  complete CONNECTED pointed Riemannian manifold carries a `MetricSpace` realizing its Riemannian
  emetric (`edist = ofReal dist`), which is `ProperSpace`, and in which every `t ∈ [0, d(p,O)]` is an
  attained distance (the `hint` input). Connectivity is genuinely required (disconnected ⟹ edist = ⊤,
  no real metric realizes it). This is now proved through `HopfRinowProper.lean` and the intrinsic
  exponential endpoint; consumers no longer inherit a Hopf--Rinow `sorryAx` from this producer.

So the abstract ordered-net layer's inputs are all sourced: `[MetricSpace]+[ProperSpace]`+`hint` ←
checked intrinsic Hopf--Rinow adapter; `hlam/hanti/hpos` ← lambda lemmas; `pack` ←
`PackingBound`-style honest input (Bishop–Gromov).

(lbl391 tilde-disjoint done as `netList_disjoint_of_le`, 2026-06-09.)

---

# DESIGN (2026-06-09, for user review before implementation): lbl383 bundle + sequence layer

## Layering (3 layers, 2 new files)

- **L1 — abstract additions** (in `GoodCoveringOrdered.lean`, `OrderedNet` namespace): index API and
  saturation on the proved net. All genuine proofs, no sorry.
  - `netList_prefix : α ≤ β → netList α <+: netList β` (from succ-append).
  - `netList_nodup` (distinct centers: disjoint balls + `lam > 0` ⟹ no duplicates).
  - `netCenter α : Option M := (netList α)[α]?` — the book's `x^α`. Stage-stable by `netList_prefix`
    (so it is THE α-th center); `alive` (`(netCenter α).isSome`) is antitone in α.
  - `netRadius α : ℝ` (= `dist x^α O`, junk 0 if dead) — the book's `r^α`; sorted ⟹ monotone where alive.
  - **index-vs-count**: sorted ⟹ `{α : r^α ≤ r}` is a PREFIX; with `netList_nodup` + `netList_count_le`:
    `alive α ∧ r^α ≤ r → α < A r` (the book's "α ≤ A(r)" indexing).
  - **`netList_passes`**: for every `r`, some stage is past-`r`-or-stopped (else infinitely many sorted
    centers in `B(O,r)`, contradicting count ≤ `A r`). Feeds item 4's `hpast`.

- **L2 — instantiation glue** (same file, `Instantiation` section):
  - `structure ProperMetricOn (Y)`: data `ms : MetricSpace Y.M` + props `realizes` (edist = ofReal dist),
    `proper`, `hint` — exactly `exists_proper_realization`'s conjunction; producer
    `properMetricOn Y hc hconn : ProperMetricOn Y` by choice on the checked intrinsic Hopf--Rinow adapter.
  - `orderedNet (P : ∀ k, ProperMetricOn (X.obj k)) (k α) : List (X.obj k).M :=`
    `letI := (P k).ms; OrderedNet.netList (X.obj k).basepoint (hd.lambda D) (hd.lambda_continuous D) α`.
  - Per-k specializations: disjoint/sorted/cover/count/dist_le/dist_ge with `hanti := lambda_antitone`,
    `hpos := lambda_pos`, `hint := (P k).hint`, `pack := PackingBound` (bridged).
  - Bridge lemma `dist_eq` : `hd.RealizesEdist` + `(P k).realizes` ⟹ `hd.dist k = (P k).dist`
    (ofReal injective on nonneg) — transfers `hd.decay` (λ-balls ⊂ inj radius, for Step B) and
    `lambda_ratio_le` to the net's metric.

- **L3 — sequence layer** (NEW files):
  - `HCGCompactness/DiagonalSubseq.lean`: generic diagonal-refinement engine
    `diagonal_subseq : (tasks refinement-stable) → (each task attainable on any subseq) → ∃ ψ StrictMono, ∀ n, task n ψ`
    (+ two instances: eventually-constant Booleans; Bolzano–Weierstrass for sequences in `[0, C]`).
    Generic (pure ℕ/topology) and REUSABLE: 3.11's P3 spacetime Arzelà–Ascoli needs the same engine.
    Check Mathlib first; hand-roll (~80–150 lines) if absent.
  - `HCGCompactness/GoodCoveringSeq.lean`:
    - `structure NetLimitData` — the lbl389→lbl390 diagonal output: `φ` StrictMono, `N∞ : ℕ∞`
      (limit net size; alive-α's stabilize, antitone ⟹ well-defined), `r∞ : ℕ → ℝ`,
      `tendsto : r_{φ k}^α → r∞ α` (per α < N∞; B–W applies since lbl389 gives `r_k^α ∈ [0, 2αλ(0)]`),
      `K : ℕ → ℕ` with the **factor-2 window** `λ[r∞ α]/2 ≤ λ[r_{φk}^α] ≤ 2λ[r∞ α]` for `k ≥ K α`
      (= lbl390), and **item 6** intersection-stability (per pair (α,β), "5λ-balls meet" eventually
      constant — Boolean diagonal, radii `5·λ[r∞ ·]` fixed AFTER r∞ exists).
    - producer `exists_netLimitData` — genuine proof via the diagonal engine, NO new sorry.
    - `structure OrderedCoverCore` — the book-facing bundle = **lbl383 items 1,2,4,5,6,7** with the
      lbl391 radii `λ^α := hd.lambda D (r∞ α)` and BOOK constants:
      item 1 (concentric, `x^0 = O`), item 2 (B̃ = λ^α/2 disjoint — `netList_disjoint_of_le` + factor-2
      window), item 4 (`B(O_k,r) ⊆ ⋃_{α<A r} B̂`, B̂ = 4λ^α: per-k cover gives `2λ[r_k^α]` ≤ `4λ^α` by
      the window; stage from `netList_passes`; index cap from index-vs-count), item 5 (α-independent
      multiplicity from A0'), item 6 (from NetLimitData), item 7 (nesting `B ⊂ B̄ ⊂ B⃗`, constants
      `45e^{10cC}`, `205e^{20cC}`: λ-ratio `lambda_ratio_le` + triangle; book's slack absorbs the
      factor 2s — checked: 10e^{10cC}+5 ≤ 45e^{10cC}, 45e^{10cC}·e^{10cC}+10·... ≤ 205e^{20cC}).
    - **Item 3 (exp-diffeo + geodesic convexity) intentionally ABSENT** — it is the §5 scale/convexity
      frontier; the bundle is named `OrderedCoverCore` (not "lbl383") so the name does not overclaim.
      Step B will take item 3 separately when §5 lands.

## ⚠ One honest-input SHAPE CHANGE needing approval

`VolumeComparisonInput.ballMult` (StepAInputs.lean) hardcodes "separated by `r`, within `4r`" — calibrated
for the Zorn A10 use. **Item 5 needs the ratio parametrized**: balls intersecting `B^α` have centers
within ~`15·e^{10cC}·λ^α` but separation only ~`λ^α/(2e^{10cC})` — ratio is a CONSTANT(n, C·λ0) but ≫ 4.
Proposal: generalize to `ballMult : ∀ (m : ℝ) ..., (sep ≥ r) → (within m·r) → card ≤ Imult m` with
`Imult : ℝ → ℕ` (still pure Bishop–Gromov, book-external); keep a `4`-specialization for the Zorn file.

## Order of implementation (each step = focused check + build)
1. L1 abstract additions → 2. L2 glue → 3. DiagonalSubseq engine → 4. StepAInputs ballMult
generalization → 5. NetLimitData + producer → 6. OrderedCoverCore items (2,4 first; 5,7 next; 6 last).
New sorries: NONE. The former L2 Hopf--Rinow black box has been replaced by the checked
intrinsic-exp adapter.

## IMPLEMENTATION STATUS (2026-06-09): steps 1–5 DONE + verified; step 6 remains

- **L1 DONE** (this file, sorry-free): `netList_prefix`, `netList_stall`, `netList_length_le`,
  `netList_length_full`, `netList_alive_of_le`, `netList_nodup`, `netCenter`(+`_eq`,`_lt_length`,
  `_mem`,`_of_stage`,`_stable`), `netRadius`(+`_of_center`,`_mem`), `netCenter_index_lt`
  (index-vs-count via sortedness-prefix + pack), `netList_passes` (saturation).
- **L2 DONE**: `ProperMetricOn` + `properMetricOn` (choice on the checked adapter), `orderedNet`,
  `ProperMetricOn.dist_eq` (ms-dist = hd.dist via double realization), `packingBound_pack`.
- **DiagonalSubseq.lean DONE, sorry-free**: `exists_subseq_tendsto_pi` (countably many bounded real
  sequences converge along ONE subsequence — Tychonoff `Π n, Icc 0 (C n)` compact + first-countable +
  `IsCompact.tendsto_subseq`, NO hand-rolled diagonal) + `exists_subseq_eventually_eq` (Boolean
  stabilization via `ι → Bool` compact; `nhds_discrete` + `tendsto_pure`).
- **StepAInputs DONE**: `ballMult` ratio-parametrized (`Imult : ℝ → ℕ`, containment `≤ m·r`);
  Zorn consumer `net_multiplicity` updated to `Imult 4`.
- **GoodCoveringSeq.lean DONE**: `seqCenter`/`seqRadius`/`seqRadius_mem` (lbl389 window),
  `NetLimitData` (φ StrictMono, `alive` profile, `rInf`, tendsto), `exists_netLimitData` (two-stage
  extraction: radii then aliveness Booleans), **`NetLimitData.lambda_window` = lbl390** (factor-2
  λ-window, eventually-form; K(α) extractable via `eventually_atTop`).
  Axiom-check: all six key theorems `[propext, Classical.choice, Quot.sound]`, **sorryAx count 0** —
  the diagonalization layer is conditional on `P` and does not itself carry the black box.
- Lean gotchas this pass: `∞` is NOT an identifier character (`r∞` → `rInf`); `Option.noConfusion`
  universe metavars → `simp at hx`; `isCompact_Icc.compactSpace` → `isCompact_iff_compactSpace.mp`;
  push Not converts `¬(s=∅)` to `.Nonempty` directly; subst on `c = O` eliminates the PARAMETER O.

**STEP 6 — lbl383 ITEMS 1, 2, 4, 6, 7 DONE + verified (2026-06-09); item 5 + final bundle remain.**
All in `GoodCoveringSeq.lean` (+ helpers `netCenter_ne`/`netCenter_disjoint`/`netCenter_zero` in the
abstract layer, `lambda_exp_le` pure-radius ratio in GoodCovering.lean):
- item 1 `netCenter_zero` (`x^0 = O`, rfl).
- item 2 **`NetLimitData.tilde_disjoint`**: eventually-in-k, B̃ = B(x^α, λ^α/2) balls at distinct
  indices disjoint (k-uniform tilde radius ≤ per-k radius by the lbl390 window).
- item 4 **`NetLimitData.hat_cover`**: eventually-in-k, `B(O_k,r) ⊆ ⋃_{γ<A r} B(x^γ, 4λ^γ)` —
  per-k factor-2 cover at a `netList_passes` stage + `netCenter_index_lt` cap + window;
  finitely many windows combined via `Filter.eventually_all_finset`.
- item 6 **`exists_stableNet`**: refinement of the subsequence stabilizing every pairwise `B`-ball
  (5λ radii) intersection pattern (`BInter` Prop + classical `decide` + the Boolean engine); rInf
  unchanged.
- item 7 **`NetLimitData.nesting`** (book constants): if B-balls of α,β meet frequently, then at every
  meeting k: `B^α ⊆ B(y, 45e^{C·10λ(0)}λ^β)` and `B̄^α ⊆ B(y, 205e^{C·20λ(0)}λ^β)`. Via
  **`NetLimitData.rInf_close`** (limit closeness `r∞^β ≤ r∞^α + 5λ^α+5λ^β`, proved along the meeting
  subfilter: `frequently_iff_neBot` + `eventually_inf_principal` + `le_of_tendsto_of_tendsto`) +
  `lambda_exp_le` ratio + explicit E1/E2 = exp algebra (`E1*E1 = E2`) + nlinarith chains.
Build green; the former proper-realization Hopf--Rinow black box is discharged. Remaining `sorry`
warnings in broader targets are pre-existing upstream/frontier items, not this producer.
Lean gotchas: **`λ` is a KEYWORD — cannot appear in identifiers** (`hλβpos` → parse error); `_` metavars
don't unfold `lamInf`-style defs in elaboration (give explicit args); `rw [hxx, hyy] at hmeet` instead of
`subst` for statement variables.

**STEP A COMPLETE (2026-06-09): item 5 + capstone DONE + verified + sorryAx=0.**
- **item 5 `NetLimitData.inter_count`** (α-independent multiplicity `I(n,C₀)`): eventually-in-k, at most
  `Imult (50e^{C·20λ(0)})` indices β have B^β meeting B^α. Exactly per the recipe: a-priori index cap
  β < A(2αλ0+10λ0) (pointwise-in-k, via per-k lbl389 `seqRadius_mem` + `netCenter_index_lt`) licenses
  the finitely many lbl390 windows; per-k comparability via `lambda_exp_le` (no window); separation =
  `netList_separated` at scale λ[R_k], R_k = r_k^α+10λ0; containment ≤ 25e^{10cC}λ^α ≤ 50e^{20cC}λ[R_k];
  ratio-`ballMult` at m₀ = 50e^{20cC} (α-free) + `Fintype.card_ulift`/`card_coe`.
- **capstone `exists_stableNetData`**: ONE diagonal datum L with the item-6 stability; items 1/2/4/5/7
  apply to it as theorems (lamInf transported along rInf-equality).
- Axiom-check: inter_count/nesting/hat_cover/tilde_disjoint/exists_stableNetData all
  `[propext, Classical.choice, Quot.sound]`, **sorryAx = 0** (the layer is conditional on `P`;
  `properMetricOn` is now produced sorry-free by the intrinsic Hopf--Rinow adapter).
- Lean gotchas this pass: `choose!` totalization needs `Nonempty M` (provide `⟨basepoint⟩`); linarith
  sees `lamInf` vs `lambda (rInf ·)` as DIFFERENT atoms (defeq ≠ syntactic — align with rfl-rewrites);
  `ballMult`'s index type is `Type u` — a `Finset ℕ` subtype needs `ULift.{u}` + `ULift.down_injective`
  + `Fintype.card_ulift`.

**Step A boundary (honest):** item 3 (exp-diffeo + geodesic convexity) = the §5 radius/convexity
frontier, intentionally absent from the Step A capstone and supplied separately by `GoodCoveringItem3`.
The former `exists_proper_realization` Hopf--Rinow deferral is discharged. Inputs carried honestly:
A0 `InjRadiusDecayInput` (CGT, book-external), `PackingBound` + ratio-`ballMult`
(Bishop–Gromov, book-external), `RealizesEdist` (dist realization).

## 2026-06-21: Hopf--Rinow proper realization discharged

The old `exists_proper_realization` deferral is discharged via the intrinsic
endpoint in `Geometry/Exponential/MinimizingGeodesic.lean`, through the new
comparison adapter `Geometry/Comparison/HopfRinowProper.lean`.

The public C4 producer now honestly requires the extra hypotheses consumed by
that endpoint: model inner product, finite rank nonzero, and boundarylessness.
`ProperMetricOn` itself is unchanged, so downstream consumers that already take
`P : forall k, ProperMetricOn ...` do not need new fields.

The delicate proof point was not Hopf--Rinow mathematics but tangent-instance
selection. The C4 proof uses `PointedRiemannianManifold.riemBundle`,
`riemInner`, and `riemBundle_cont` with unannotated `letI` bindings under the
standard local suppression of the project tangent norm instances. Annotating
those instances makes Lean choose the wrong `Tensor0SBundle` normed group and
reopens the diamond.

Focused verification passed for `GoodCoveringOrdered.lean` after this wiring. Targeted downstream
builds also passed for `GoodCoveringSeq` and `GoodCoveringItem3`.
