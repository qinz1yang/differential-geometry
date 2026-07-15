# PLAN: geometric instantiation of Claim 1 (`Claim1Wiring.lean`)

Status: **PLAN ONLY — for user + GPT Pro review before implementation.**
Date: 2026-06-10.  Spec: `RicBoundProof.md` (Steps 1–5, Claims 1–2).
Engine (all sorry-free, in oleans): `AkMFold.lean`, see `AkMFold.md`.

## 0. Where we are

Proven, sorry-free, in oleans (`AkMFold.lean`):

- **`claim1`** — the textbook Claim-1 estimate at the component-array level:
  given a smooth local frame on open `u`, Christoffel data `chr`, and fields
  `A : M → (Fin 3 → Idx) → ℝ` (the would-be `A_k` components, upper slot LAST),
  `g : M → (Fin 2 → Idx) → ℝ` (the would-be `g_k` components), IF
  * `hkoszul` : `contrTail (A y) (g y) = ½·(∇g∘P₁) + ½·(∇g∘P₂) − ½·(∇g∘P₃)` on `u`
    (`∇g := iterCovComp … g 1`, `Pᵢ` the three Koszul slot permutations),
  * `hinv` : `∀ x ∈ u, Σ_l g[l,c]·Ginv[e,l] = δ_{ce}` (pointwise inverse array; **no
    smoothness of `Ginv` needed** — the proof never differentiates `g⁻¹`),
  * `hGinv` : `compL2 (Ginv x) ≤ C0` on `u`,
  * `hK` : `compL2 (iterCovComp … g j x) ≤ K` on `u` for `1 ≤ j ≤ m`,
  THEN `∃ C ≥ 0, ∀ x ∈ u, compL2 (iterCovCompU … A m x) ≤ C·(1 + compL2 (iterCovComp … g (m+1) x))`.
- Supporting engine: `claim1_abstract` (strong induction), `ISO(m)`, `isoTop`,
  inverse cancellation, `P(m)` binomial bound, both tower shifts, tower
  linearity (`add`/`smul`), tower smoothness, `iterCovComp_eq_iterCov`
  ((0,s) tower realization: component tower = `iterCov gRef` on frame tuples).

**Remaining = discharge `claim1`'s hypotheses on the actual geometry** — `A_k =
connectionDifferenceTensorAt (LC g_k) (LC gRef)`, `g_k` the flow metric, `gRef`
the reference — and state the result with geometric norms.  This file plans that.

## 1. Verified feasibility facts (checked in-repo 2026-06-10)

F1. `covOneCompDiff` (AllTimesBounds:2533) proves the two-term expansion
    `∇g(a,b,c) = ⟨A(e_a,e_b),e_c⟩_g + ⟨A(e_a,e_c),e_b⟩_g` at the INNER-PRODUCT level
    first; its `hinv` (g_k-ON basis) enters ONLY via `coord_eq_inner_id` to convert
    coordinates to inner products at the very end.  ⇒ the LOWERED identity is
    extractable frame-generally (Route R1 below).
F2. There is **no smooth gRef-ON local frame producer** in the repo (only parallel
    frames along curves; `exists_gOrthonormalBasis` is pointwise).  Design D2.
F3. `christoffelSymbolInFrame`-smoothness for LC connections exists
    (`LeviCivita/Smooth/Christoffel.lean`).
F4. General-frame `normSq0S` coordinate formula parametrized by an inverse array
    `gInv` exists (`Tensor0SMetric`), beyond the ON (`identityInvMetric`) case.
F5. `iterCovComp_eq_iterCov` (the (0,s) realization, any base field, any order) is
    proven — the g-side towers in `claim1` already ARE the geometric
    `metricCovDeriv g_k gRef j` components on frame tuples.
F6. metric-compatibility / LC facts available: `leviCivitaConnectionOfMetric_isLeviCivita`,
    `connDiffCompEq` (eq 3.7, g_k-ON pointwise), `metricGammaEquiv` (eq 3.8, the 3/2 & 2
    constants — consistency check: `claim1`'s `KR = |½|+|½|+|−½| = 3/2` matches).

## 1b. SIGN CONVENTION (this phase, authoritative)

`A_k := connectionDifferenceTensorAt (LC g_k) (LC gRef) = ∇_k − ∇_ref`
(matching the existing `covOneCompDiff`/`connDiffCompEq` orientation, which use
`connectionDifferenceTensorAt (LC h) (LC gRef)` with POSITIVE two-term expansion).
Consequences: two-term expansion `∇g(a,b,e) = Ǎ(a,b,e) + Ǎ(a,e,b)` (positive),
lowered-Koszul coefficients `(+½, +½, −½)`.  NOTE: the spec `RicBoundProof.md`
writes `A_k = ∇ − ∇_k` (the OPPOSITE orientation, coefficients `(−½,−½,+½)`);
`claim1` takes the coefficients as free parameters so the estimate is identical,
but all NEW lemmas in this phase MUST use the `∇_k − ∇_ref` orientation above —
do not prove the flipped identity.

## 2. Target statement (end of this phase)

```text
claim1_geom (working name; file Claim1Wiring.lean):
Let gRef, (g_k) be smooth metrics, u ⊆ M open with a smooth local frame
(IsLocalFrameOn … frame u), A_k := connectionDifferenceTensorAt (LC g_k) (LC gRef).
Assume on u: the frame-Gram bounds for gRef (D2), the two-sided equivalence
c·gRef ≤ g_k ≤ C·gRef (eq 3.3 output), and √normSq0S gRef (∇^j g_k) ≤ K for 1 ≤ j ≤ m.
Then ∃ C_m, ∀ x ∈ u,
  compL2 (iterCovCompU … (A_k components) m x) ≤ C_m·(1 + √(normSq0S gRef x (m+3) (metricCovDeriv g_k gRef (m+1) x))).
```

i.e. the conclusion's g-side is converted to the geometric norm (the (0,s)-side
bridges exist); the A-side stays the component-tower `compL2` (Route P below) —
exactly the quantity ric_bound Step 4's array estimate consumes.

## 3. Design decisions (for review)

**D1 — Route P (pragmatic) vs Route F (faithful).**
  * P: keep the A-side as `compL2 (iterCovCompU …)`; do NOT build the (1,2)
    geometric tower realization.  Step 4 of ric_bound is itself a component-array
    estimate (established route), and it consumes exactly this quantity.  The
    geometric `√normSqRS(∇^m A_k)` form is NOT load-bearing for eq (3.4).
  * F: additionally build `covDerivStepCompU_frameCompRS_eq` (the (1,2) upper
    single-step realization bridge, upper analogue of `covDerivStepComp_frameComp_eq`)
    + an `(r,s)` realization predicate + `frameCompRS` + the `normSqRS` bridge.
    ~2–3 sessions of new `(r,s)` realization API.
  **Recommendation: P now, F deferred** (record as an explicit deferred brick).
  Risk if P: the final eq-3.4 assembly must stay component-level throughout; if a
  later consumer genuinely needs the invariant `∇^m A_k` tensor, F gets built then.

**D2 — frame choice: smooth gRef-ON frame (D2a) vs arbitrary smooth frame + Gram
constants (D2b).**
  * D2a: build a smooth Gram–Schmidt local ON frame producer (new infra, ~300
    lines; smoothness of GS coefficients = rational expressions in smooth inner
    products with positive denominators).  Payoff: `compL2 = √normSq0S` on the
    nose (`normSq0S_identity_eq_sum_sq`), constants clean.
  * D2b: any smooth local frame (e.g. Mathlib `Trivialization.localFrame`), plus
    a two-sided comparison `α·compL2² ≤ normSq0S ≤ β·compL2²` with α,β from the
    Gram matrix bounds of the frame on u (uses F4 + finite-dim eigen bounds, the
    same linear algebra as B4).  No new frame infra; constants depend on the frame.
  **Recommendation: D2b** — Claim 1's `C·(1+·)` form absorbs frame constants, and
  the same linear-algebra brick (B4) is needed anyway.  D2a is polish, deferrable.

**D3 — where things live.**  New file
  `HCGCompactness/Claim1Wiring.lean` (imports AkMFold + AllTimesBounds-layer
  pieces); generic lowered-Koszul component lemma goes to the lowest natural
  layer (`Tensor/RSTensor/NablaOnTensors/` if it only needs the connection-
  difference API; HCGCompactness otherwise).  Frame-Gram linear algebra goes
  next to `RicciOperatorNormBound`-style files (`Geometry/Curvature/` or
  `Geometry/Metric/`), NOT in Evolution (lift-generic-out rule).

**D4 — per-point basis vs fixed frame.**  All towers need ONE smooth frame fixed
  on `u`; all pointwise identities (hkoszul, hinv) are stated per `y ∈ u` IN that
  frame.  Do NOT reuse the g_k-ON pointwise basis of `connDiffCompEq` (it varies
  with y; "frame-stuck", cannot be differentiated).

## 4. Bricks

**B1 — `hkoszul` (the lowered-Koszul field identity).  THE main brick.
STATUS 2026-06-10: **B1 COMPLETE sorry-free** (`koszulComp_at`, Claim1Wiring.lean,
general frame).  The intrinsic content came from the NEW
`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean` (parallel session; compiles
clean): `difference_symm_at` + `nabla_metric_two_term` + `koszul_difference`.
`koszulComp_at` takes its frame components: LHS lowers via
`christoffelSymbolDifferenceInFrame`(+`_expansion`,+`_eq_sub`, Chart/Christoffel)
+ `coeff_sum_eq` linearity; RHS realizes via `iterCov_realizes` (a=0) +
`iterCovComp_eq_iterCov` + explicit `Fin.cons = frameTuple` slot identifications;
permutations `(Equiv.refl, Equiv.swap 0 1, (finRotate 3).symm)`, coefficients
`(½, ½, −½)`.  GOTCHAS: (i) TWO distinct `christoffelSymbolInFrame` constants
(`Tensor.Coordinates` vs `Coordinates`, identical bodies — bridged by rfl-lemma
`chr_eq_chartChr`; FLAG for dedup); (ii) avoid `set` for the connections (breaks
rw matching against library lemmas); (iii) `2+0`/`iterCov … 0` defeq-not-syntactic
— bridge with an exact-cast `have`; (iv) concrete Fin-equiv applications
(`swap`, `finRotate.symm`) close by `congr 1` alone (definitional evaluation).**
  Math: `Ǎ(a,b,e) := Σ_d A^d_{ab}·g[e,d] = ½(∇g(a,b,e) + ∇g(b,a,e) − ∇g(e,a,b))`,
  ∇ = gRef-LC, valid in ANY frame (tensor identity).  Derivation: two-term
  expansion `∇g(a,b,e) = Ǎ(a,b,e) + Ǎ(a,e,b)` (from `∇_k g_k = 0` + the §1b
  convention `A = ∇_k − ∇_ref`, signs POSITIVE)
  + cyclic combination using A's lower-slot symmetry (both connections torsion-free)
  + g-symmetry.  Lean route R1: extract the inner-product-level identities from
  `covOneCompDiff`'s proof body (F1) into a frame-general lemma; then the array
  algebra (3-term cyclic sum) is pure `Finset`/`ring`.  Sub-bricks:
  - B1.1 two-term expansion, frame-general, lowered (inner-product) form;
  - B1.2 A's lower-slot symmetry as a component fact (locate in
    ConnectionDifference/AllTimesBounds; else prove from torsion-freeness);
  - B1.3 `contrTail A_comp g_comp = Ǎ` (lowering = last-slot contraction against
    the metric array; componentRS + basis expansion);
  - B1.4 the cyclic assembly + cast to `iterCovComp … g 1` via F5.
  Fallback R2 (if extracting from covOneCompDiff is too entangled): re-derive
  B1.1 from the ConnectionDifference API + `IsLeviCivita` compatibility directly.
  Effort: 1–1.5 sessions.  Risk: moderate (R1 extraction quality unknown).

**B2 — smoothness wiring (`hA`, `hg`, `hchr`, `hframe`).
STATUS 2026-06-10: **B2 COMPLETE sorry-free** in `Claim1Wiring.lean`
(`lcChrist_e_mdiffOn`, `frame_e_mdiffOn`, `akCompField` + `akCompField_mdiffOn`,
`gCompField_mdiffOn`).  `hg` gotcha: `Tensor0SModel` instance synthesis needs
`set_option backward.isDefEq.respectTransparency false in` (the known
tensor-model-alias lesson); engine = `TensorMultilinear.contMDiffAt_section_apply_gen`
+ `(metricTensorField g).contMDiff` + `frame_e_mdiffOn`, conclusion defeq to
`frameComp0S` (no simp needed).  IMPORTANT: do NOT import
`ApproximateIsometry.lean` — it is another session's in-flight edit and currently
BROKEN (unknown `lcDiffCompInFrame`/`lc_christoffel_contMDiffAt` references, 100+
errors); B2 instead uses the STABLE upstream `lc_christoffel_contMDiffAt`
(`LeviCivita/Smooth/MetricFlatBasis.lean`) + an `IsLocalFrameOn.coeff ↔
localFrame_coeff` eventuallyEq bridge (same simp set as the old ApproximateIsometry
proof: `IsLocalFrameOn.toBasisAt/coeff`, `Trivialization.localFrame/basisAt/
localFrame_coeff`).**
  `hchr` from F3; `hg` = smoothness of metric components in a smooth frame
  (exists in coordinate/AllTimesBounds machinery); `hA` = componentRS of
  connectionDifferenceTensorAt smooth = difference of two smooth Christoffel
  arrays (F3 twice).  Effort: 0.5 session.  Risk: low.
  ENTRY POINTS (all verified in-repo 2026-06-10; B2 = adapt these to the
  `ContMDiffOn … u` shapes `claim1` consumes; canonical setting: a tangent
  trivialization `e₀` + `basisE`, `frame := e₀.localFrame basisE`,
  `u := e₀.baseSet`, `hframe∞ := e₀.isLocalFrameOn_localFrame_baseSet I ∞ basisE`):
  - `hchr`: **`lcChrist_e_contMDiffAt`** (`ApproximateIsometry.lean` ~:1490) —
    `ContMDiffAt 𝓘(ℝ,ℝ) ∞` of `christoffelSymbolInFrame (LC g) frame hframe1 · i j k`
    at every `x ∈ e₀.baseSet` (general `e₀`, exactly the per-point form; wrap with
    `.contMDiffWithinAt` to get `ContMDiffOn … e₀.baseSet`).  `IsLocalFrameOn` is a
    Prop, so any `hframe1` proof matches up to proof irrelevance.
    (Variant pinned at `trivializationAt … x`: `lcChrist_triv_contMDiffAt` ~:3729.)
  - `hframe` (tower input `∀ d, ContMDiffOn … (fun y => TotalSpace.mk' E y (frame d y)) u`):
    from `hframe∞.contMDiffOn d`.
  - `hg`/`hA` (component-field smoothness): **`tensorRS_eval_contMDiffAt`**
    (`Tensor/RSTensor/LocalFrameRegularity.lean:150`) — smooth section `T`, smooth
    `β`, smooth slots `V` ⇒ `fun p => T p (β p) (fun a => V a p)` is `ContMDiffAt ∞`.
    For `hg`: the `(0,2)` specialization on `frame`-slots applied to
    `frameComp0S (metricTensorField g_k) frame` (`frameComp0S` def:
    `Evolution/RmRealizationBridge.lean:81`, `= fun x m => A x (frameTuple frame x m)`).
    For `hA`: same on the `(1,2)` `connectionDifferenceTensorAt` SECTION — REMAINING
    sub-gap: smoothness of `y ↦ connectionDifferenceTensorAt (LC g_k) (LC gRef) y` as
    a section (= difference of two smooth-Christoffel objects; check
    `ConnectionDifference.lean` for an existing `contMDiff` producer, else derive from
    `lcChrist_e_contMDiffAt` twice through the component basis), plus the
    upper-slot input `β` built from the frame's DUAL basis (check `hframe.toBasisAt`
    / coordinate-dual plumbing in `Tensor/RSTensor/Coordinates/`).

**B3 — `hinv` + the `Ginv` field.
STATUS 2026-06-10: **B3 COMPLETE sorry-free** in `Claim1Wiring.lean`: `gramE`
(frame Gram matrix), `gramE_herm`, `gramE_dotVec` (quadratic-form expansion),
`gramE_posDef` (via `Matrix.PosDef.of_dotProduct_mulVec_pos` + frame linear
independence + `g.pos` — mirrored from `BoundaryGramMatrix.lean`'s template;
gotcha: the PosDef hypothesis carries `star c`, bridge with `star_trivial`),
`ginvCompField` (= `(gramE)⁻¹` entries, junk off `baseSet`), **`ginv_hinv`**
(the exact `claim1` `hinv` shape, via `Matrix.nonsing_inv_mul` + entry
extraction).  No smoothness of `Ginv` anywhere, as designed.**

**B4 — `hGinv` : `compL2 (Ginv x) ≤ C0` + (D2b) the frame-Gram comparison.
STATUS 2026-06-10: **B4 COMPLETE sorry-free** (`ginv_compL2_le`, Claim1Wiring.lean):
`c·‖v‖² ≤ vᵀ(gramE)v  ⟹  compL2(ginvCompField) ≤ √(card Idx)/c`.  Elementary
column bound (`w = G⁻¹eₗ`: `c‖w‖² ≤ wᵀGw = wₗ ≤ ‖w‖`), NO spectral theory;
posdef/invertibility derived from `hquad` itself.  The geometric `hquad` comes
from the eq-3.3 equivalence composed with the frame's gRef-Gram lower bound via
`gramE_dotVec` (consumer-side one-liner).  GOTCHAS: `dotProduct_self_nonneg/_eq_zero`
do NOT exist — inline `Finset.sum_pos'`/`sum_nonneg` + `Function.ne_iff`; nlinarith
needs the explicit `mul_self_le_mul_self` product chain + `le_div_iff₀` split.**
  From the two-sided equivalence `c·gRef ≤ g_k ≤ C·gRef` (eq 3.3 output) and the
  frame's gRef-Gram bounds: matrix eigen/Rayleigh bounds ⇒ entries of the inverse
  Gram are bounded ⇒ `compL2(Ginv) ≤ C0(c,n,frame)`.  Reuse the Rayleigh
  machinery (`RicciOperatorNormBound`, `QuadraticFormBound`); may need a small
  `Matrix`/bilinear inverse-bound lemma (finite-dim, ~80–150 lines).
  Effort: 0.5–1 session.  Risk: moderate-low (pure linear algebra, tools partly
  present).

**B5 — `hK` and the conclusion bridge (g-side norms).
STATUS 2026-06-10: **B5 COMPLETE sorry-free** (`compL2_tower_eq`, Claim1Wiring.lean):
at any point where the frame is gRef-ON (the pointwise
`MetricInverseInBasis … identityInvMetric` condition, the established
AllTimesBounds pattern), `compL2 (iterCovComp … (frameComp0S T) j y) =
√(normSq0S gRef y (r+j) (iterCov gRef r T j y))` — an EQUALITY, both directions
usable (convert `hK` inputs and the conclusion).  Proof:
`normSq0S_identity_eq_sum_sq` + `iterCovComp_eq_iterCov` + `component0S_apply` +
`toBasisAt_coe`.  The full non-ON Gram-comparison (two-sided constants) is NOT
built — deferred to the eq-3.4 endpoint phase if a consumer needs the whole-window
norm conversion in a single non-ON frame (Route-P discipline: Step 4 consumes
`compL2` directly).**

**B6 — assembly `claim1_geom`.
STATUS 2026-06-10: **FIRST ASSEMBLY COMPLETE sorry-free** (`claim1_geom`,
Claim1Wiring.lean): the geometric Claim 1 on a trivialization domain —
`|∇_U^m (Γ(g_K)−Γ(g_ref))| ≤ C·(1+|∇^{m+1}g_K|)` in `compL2` — with ALL structural
hypotheses discharged (B1 `koszulComp_at`, B3 `ginv_hinv`, B2 smoothness ×4) and
only the numeric window bounds (`hGinv : |Ginv|≤C0`, `hK : |∇^j g_K|≤K`) as inputs.
Instantiation: `c=(½,½,−½)`, `P=(refl, swap 0 1, (finRotate 3).symm)`.
REMAINING REFINEMENTS: B4 (produce `hGinv` from the eq-3.3 two-sided metric
equivalence — finite-dim linear algebra on `gramE⁻¹`) and B5 (restate the
conclusion through `√normSq0S` via `iterCovComp_eq_iterCov` + the ON/Gram
comparison — D2b constants).**

**B7 (DEFERRED, Route F) — (1,2) upper realization.**
  `frameCompRS` + `(r,s)` realization predicate + `covDerivStepCompU_frameCompRS_eq`
  + induction (mirror `iterCovComp_eq_iterCov`) + `normSqRS` bridge (G1 isometry
  `RSLoweringNorm` reusable here).  Effort: 2–3 sessions.  Only if an invariant-
  tensor consumer appears.

## 5. Order, milestones, stop conditions

Order: B2 → B3 → B1 (the heart) → B4 → B5 → B6.  (B2/B3 first: cheap, and they
fix the frame/array conventions B1 must match.)

Milestones: M1 = B1.1 two-term expansion compiles (the only mathematically deep
step); M2 = hkoszul complete; M3 = claim1_geom sorry-free.

Stop-and-consult conditions: (i) B1 extraction reveals the inner-product layer
is inseparable from the ON basis after ~1 session → switch R2; if R2 also blocks
on missing ConnectionDifference API → report exact missing lemma. (ii) B4 needs
spectral theory beyond Rayleigh → simplify to entrywise bounds (compL2 is an
entrywise-friendly norm; `|Ginv_{ij}| ≤ ‖·‖` route). (iii) any brick exceeds 2×
its estimate.

Out of scope here (later phases of ric_bound): Claim 2 (mixed derivatives),
Step 4 telescoping + (A_N)/(B_N) double induction, Step 5 time derivatives,
discharge into `MetricCovOrderEvolutionInput`.

## 6. GPT Pro review prompt (ready to send; Case 2 — push branch first)

```text
I am working in a large Lean 4/mathlib project. Do not write code first. Review a
formalization PLAN for mathematical feasibility and route quality.

Context: MSM135 Ch3 Lemma 3.11, eq (3.4) bookkeeping "Claim 1":
|∇^m A_k| ≤ C_m(1+|∇^{m+1} g_k|), where A_k = connectionDifferenceTensorAt
(LC g_k) (LC gRef) = ∇_k − ∇_ref is the connection-difference (1,2) tensor
(this orientation gives lowered-Koszul coefficients +½,+½,−½), ∇ = Levi-Civita
of the reference gRef, g_k the flow metric.

Already PROVEN sorry-free at the component-array level (file
DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/AkMFold.lean):
the full estimate `claim1` from hypotheses (hkoszul: lowered-Koszul field
identity contrTail(A)(g) = ½(∇g∘P₁)+½(∇g∘P₂)−½(∇g∘P₃); hinv: pointwise inverse
array; |Ginv| ≤ C0; |∇^j g| ≤ K, 1 ≤ j ≤ m), via an isolate-and-invert engine
(binomial P(m), residual ISO(m), inverse cancellation, strong induction) that
never differentiates g⁻¹.

The PLAN under review (file …/HCGCompactness/Claim1Wiring.md on the branch)
instantiates these hypotheses on the actual geometry. Please:
1. Check the mathematical claims: (a) the lowered-Koszul identity in an
   ARBITRARY (non-coordinate, non-ON) smooth local frame, as a pure component
   identity with the THREE permutations and coefficients (½,½,−½) — is the
   stated derivation (two-term expansion from ∇_k g_k = 0 + lower-slot symmetry
   of A + cyclic combination) complete and frame-correct (no structure-
   coefficient corrections)? (b) the claim that Ginv needs NO smoothness and NO
   derivative bounds anywhere. (c) the D2b plan to use an arbitrary smooth frame
   with Gram-equivalence constants instead of constructing a smooth orthonormal
   frame — any hidden obstruction for the m-th order towers?
2. Assess Route P (keep the A-side at component level; defer the (1,2) tensor
   realization) — is anything in MSM135's Step 4 (telescoping, mixed-derivative
   bounds) that genuinely needs the INVARIANT ∇^m A_k rather than its frame
   components?
3. Identify the riskiest brick and any missing lemma the plan overlooks.
4. Suggest the smallest reordering/merging of bricks B1–B6 if any.
Constraints: prefer small helper lemmas; no broad refactors; do not propose
abandoning the proven component engine.
```

## 7. Honest accounting

Claim 1 estimate (component form): **proven**.  Geometric instantiation: 0%
(this plan).  After B1–B6: Claim 1 fully geometric ⇒ ric_bound's Claim-1
input done; ric_bound itself still needs Claim 2 + Steps 4–5 (larger).  Whole
HCG project ~15–20% (theorem-weighted), unchanged until those land.

## 2026-06-14 — component-eval transparency sweep (item 4): 4 → 3 blocks

Removed the `set_option backward.isDefEq.respectTransparency false` from **B5 `compL2_tower_eq`** — it was
**STALE**.  The proof is pure component-eval (`rw [compL2]; congr 1; normSq0S_identity_eq_sum_sq; simp only
[compL2Sq]; Finset.sum_congr; iterCovComp_eq_iterCov; component0S_apply; IsLocalFrameOn.toBasisAt_coe; rfl`) —
no bundle topology / `ContMDiffAt` / section ext — so the option was unnecessary.  Same shape as the already-
removed `RicBoundGoodFrame.{compL2_tower_le, sqrt_tower_le_compL2}`.  Focused-check green (54.2s),
statement-preserving (no consumer of B5 is affected).

**Kept (still need the option, correctly):** `gCompField_mdiffOn` (B2, `ContMDiffOn` — and note the B2 `hg`
`Tensor0SModel` instance-synthesis gotcha recorded above is genuine bundle/model-topology), `koszulComp_at`
(B1, builds smooth sections via `ContMDiffSection.exists_eq_at_gen`), `claim1_geom` (B6 assembly wiring
`ContMDiffOn` bricks).  These belong to the bundle/model-topology workstream, not component-eval.  See
`Tensor/RSTensor/ComponentEvalApiPlan.md` (6th pass).

## 2026-07-09: generic tensor component smoothness

Added and verified `tensorComp_mdiffOn`: components of any smooth covariant
tensor field in a trivialization frame are smooth on the base set.  F4 uses it
for its arbitrary tensor `T`; it replaces a repeated metric/Ricci-specific proof
pattern without unfolding tensor representations.
