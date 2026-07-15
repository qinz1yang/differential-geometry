# `TimeRecursion` -- Brick 4 Phase P3 downstream plan

## 2026-07-14 uniform recursive residual cost

Added `gammaStarCost` and `resStarCost`, and strengthened `gammaStarU` and
`resStarLFU` to carry exact `StarSum2Cost` certificates. The recurrence fixes
one residual constant for each derivative order `k`, independent of the later
choice of time, point, or local frame. Focused verification and the module
refresh passed.

## 2026-06-13 Planner plan

This is the new downstream home for Brick 4 P3.  It should import:

```lean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SpatialMember
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
```

Do not try to prove P3 in `StarSum2.lean`: `StarSum2` is upstream of `StarRouting` and
`SpatialMember`, while P3 needs both the `slotdiffStarA` routing family and the accepted
`spatialCommStarSum` theorem.

Status:

- P2 is closed: `spatialCommStarSum` is available from `SpatialMember`.
- P3 theorem is 0% proved.
- `gammaStepStar` is 0% proved.
- The old generic `residualStarSum S hS k t` stub in `StarSum2.lean` is too strong and in the
  wrong layer.  The refrozen all-`k` endpoint must live here and carry the honest `Fin 3`,
  `hdim`, base-evolution, and time-step inputs needed by `residualStarSum_zero` and
  `iteratedRmComp_hasDerivWithinAt`.

## First producer: Ricci trace of `nablaRm`

Before attempting `gammaStepStar`, build the missing bridge:

```lean
ricciCovDeriv_trace_nablaRm
  : ricciCovDerivCompInFrame S frame t x d a b
      = sum e, nablaKRm04Field S t 1 x
          (vec5 (frame d x) (frame e x) (frame a x) (frame e x) (frame b x))
```

Expected route:

1. Use `canBianchiCore` with `g := S.base.metric t`, the supplied orthonormal basis, and
   `identityInvMetric`.  This avoids the coordinate-frame limitation of `canBianchiAt`.
2. Rewrite its `NablaRicTraceAt` conclusion with `nablaRicTrace_apply` / direct application at
   `A := frame d x`, `B := frame a x`, `C := frame b x`.
3. Identify the `nablaRm04` side with `nablaKRm04Field S t 1 x`.  Use the definitional
   `nablaKRm04Field_succ` / `nablaRm04Field` route and `nablaKRm04Field_realizes` as needed.
4. Identify the `nablaRic` side with `ricciCovDerivCompInFrame`.  The coordinate prototype is
   `coordNablaReal` / `coordNablaRealOn`; for the P3 endpoint this needs an arbitrary-frame
   version, probably proved by the same `TotalNabla0SRealizes.eval_C1_slots` pattern with a
   local-frame or cov-zero-at-point frame realization.
5. Collapse the orthonormal inverse metric to a single diagonal sum.

Stop condition: if step 4 cannot be proved without a real local-frame hypothesis, stop and report
the exact hypothesis needed.  Do not introduce a polished assumption like `hgamma`.

## Then `gammaStepStar`

After the bridge is available, normalize:

- `iteratedRmCompDt_succ`;
- `covDerivStepDt`;
- `christoffelRHS_id` at the orthonormal inverse metric;
- the Ricci-trace bridge above.

The normalized summands should be `base (k+1) 1 k 0` terms.  Reuse `slotdiffStarA` whenever the
slot shape matches; add only the missing Christoffel-route permutations.

## Executor prompt

```text
Create `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.lean` and
claim it via `scripts/lake-locked.ps1`.  Import `SpatialMember` and `IteratedRmTowerHeatEq`.
Read `TimeRecursion.md` and `StarSum2.md` section `2026-06-13 P3 EXECUTOR FINDINGS`.

Do not work in `StarSum2.lean` except for removing or relocating the old misplaced
`residualStarSum` stub after the new endpoint exists.  First build only the smallest producer:
the arbitrary-frame bridge
`ricciCovDeriv_trace_nablaRm`, using `canBianchiCore` plus the `coordNablaReal` proof pattern.

Do not attempt `gammaStepStar` until that bridge is green.  Stop if the arbitrary-frame
`totalNabla0SFun ... S.ricci` to `ricciCovDerivCompInFrame` realization requires a local-frame
hypothesis not present in the refrozen endpoint; report the exact statement shape.
```

## 2026-06-13 EXECUTOR FINDINGS — bridge GREEN, stop-condition reached

Both producers are GREEN and sorry-free in `TimeRecursion.lean`:

1. `nablaRicReal_frame` (Gap B realization) — `coordNablaReal` generalized to an arbitrary smooth
   frame.  Proves
   `nablaRicComp S frame t x d a b = ricciCovDerivCompInFrame S frame t x d a b`
   for any `IsLocalFrameOn I E 1 frame u`, `hu : IsOpen u`, `hx : x ∈ u`.  It needs ONLY frame
   smoothness — no frozen/cov-zero frame — because `ricciCovDerivCompInFrame` already carries the
   two Christoffel corrections (so the `eval_C1_slots` route closes with any `C¹` extension `X`).
   The proof is a direct port of `coordNablaReal` with `coordinateFrameAt x₀ → frame`,
   `coordinateFrameSet x₀ → u`, `(…).contMDiffAt → hframe.contMDiffAt hu hx`.

2. `ricciCovDeriv_trace_nablaRm` (the requested bridge) — GREEN.  Route exactly as planned:
   `canBianchiCore (S.family.metric t) basis identityInvMetric hinv` (`hinv` from
   `metricInverseInBasis_identity_of_orthonormal … horth`), `.2.2` is `NablaRicTraceAt`, applied at
   `(frame d x, frame a x, frame b x)`.  The reconciliation of `canBianchiCore`'s
   `ricciSection`/`rm04Section` to the solution's `S.ricci`/`S.base.rm04` is **definitional**
   (`metricRicci g := ricciSection (metricCov g) _`, `metricRm04 g := rm04Section g (metricCov g) _`,
   `metricCov g := leviCivitaConnectionOfMetric g`, all `def`/proof-irrelevant), so the closing
   `heq.trans (hcollapse …)` bridges by defeq with NO explicit reconciliation simp.  Gap A is
   `nablaKRm04Field_succ`+`totalNabla0S_apply`+`nablaKRm04Field_zero`; the δ-collapse is
   `Finset.sum_eq_single` + `identityInvMetric_apply_self`/`diagonalInvMetric_eq_zero_of_ne`.

### Slot-order note (native vs schematic)

`canBianchiCore`'s `NablaRicTraceAt` traces Riemann slots **1 & 4**:
`nablaRic(A,B,C) = ∑ᵢⱼ gInv·nablaRm04(A, eᵢ, B, C, eⱼ)`.  So the proved bridge has the **native**
diagonal order `vec5 (frame d x)(frame e x)(frame a x)(frame b x)(frame e x)` = `(d,e,a,b,e)`, i.e.
`∇_d Ric_{ab} = ∑_e ∇_d Rm04(e,a,b,e)`.  The schematic target in this plan wrote `(d,e,a,e,b)`;
the two differ by the `NablaRmSymm` slot-`3↔4` antisymmetry (`canBianchiCore.2.1` supplies
`NablaRmSymmAt`).  `gammaStepStar` should normalize slots downstream — it should consume the native
`(d,e,a,b,e)` order, or apply `NablaRmSymm` once if it needs `(d,e,a,e,b)`.

### STOP CONDITION REACHED — refrozen endpoint must carry a smooth local frame

The realization (hence the bridge) requires the frame to be a **smooth `IsLocalFrameOn I E 1 frame u`
local frame** (`+ hu : IsOpen u`, `hx : x ∈ u`), with its pointwise values `frame i x` forming the
`g`-orthonormal `basis` (`hbasis : ∀ i, frame i x = basis i`, `horth`).  The current
`residualStarSum_zero` endpoint instead carries only a **pointwise `Module.Basis`** (orthonormal at
`x`) with NO smoothness — which is insufficient for `eval_C1_slots`.

Exact statement shape the refrozen P3 endpoint must supply (so `gammaStepStar` can use this bridge):

```text
-- in addition to the pointwise orthonormal `basis`, the endpoint must expose
(frame  : Idx → (y : M) → TangentSpace I y)
(hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
(hu     : IsOpen u)
(hx     : x ∈ u)
(hbasis : ∀ i, frame i x = basis i)
(horth  : ∀ i j, (S.family.metric t).inner x (basis i) (basis j) = if i = j then 1 else 0)
```

i.e. the refrozen endpoint's frame should be a smooth orthonormal local frame, with `basis` recovered
as its value at `x` (or directly as `hframe.toBasisAt hx`).  This is satisfiable — the time-step
(`iteratedRmComp`) already works against a frame *field* — but it is a real change from a bare
pointwise `Module.Basis`, so the planner should confirm the endpoint refreeze carries it before
`gammaStepStar` is attempted.

NOT YET DONE: `gammaStepStar`, the refrozen all-`k` endpoint, and relocating the old
`residualStarSum` stub from `StarSum2.lean` (the stub move is gated on the new endpoint existing).

## 2026-06-13 Planner review -- bridge accepted, endpoint decision

Live review accepted the executor result:

- `TimeRecursion.lean` imports the correct downstream modules: `SpatialMember` and
  `IteratedRmTowerHeatEq`.
- `rg "sorry|admit" TimeRecursion.lean` is clean.
- `nablaRicReal_frame` is the arbitrary smooth-local-frame realization of `nablaRicComp =
  ricciCovDerivCompInFrame`.
- `ricciCovDeriv_trace_nablaRm` is the requested bridge, with the native trace order
  `(d,e,a,b,e)` from `NablaRicTraceAt`.

Planner decision: the refrozen P3 endpoint must be local-frame based.  A bare pointwise
`Module.Basis` endpoint is the wrong interface for P3 because the time-recursion and gamma producer
need smooth frame fields.  The all-`k` endpoint should live in this file, not in `StarSum2.lean`.

Next step is statement freeze, not `gammaStepStar`:

1. Add a theorem-shaped local-frame endpoint, suggested name `residualStarSumLF`, carrying:
   `frame : Fin 3 -> (y : M) -> TangentSpace I y`, `hframe : IsLocalFrameOn I E 1 frame u`,
   `hu`, `hx`, a pointwise `basis : Module.Basis (Fin 3) Real (TangentSpace I x)`,
   `hbasis : forall i, frame i x = basis i`, and `horth`.
2. Carry the honest time-side inputs: the k=0 `hbase` from `residualStarSum_zero`, and for the
   all-k induction the explicit `hrm`/`hchr`/`hswap` inputs consumed by
   `iteratedRmComp_hasDerivWithinAt`, or a small named input package with exactly those fields.
3. Prove the k=0 local-frame adapter from `residualStarSum_zero`; this should be routine because
   the old k=0 theorem is stronger than a local-frame-only conclusion.
4. Leave the all-k induction as the single visible `sorry` in the new endpoint if needed.  Do not
   move or delete the old `StarSum2.lean` stub until the new endpoint elaborates and the downstream
   imports are clear.

Stop condition: if the local-frame endpoint cannot be stated without adding a vague assumption like
`hstep`, stop and report the exact missing time-side field.  Do not attempt `gammaStepStar` yet.

## Next executor prompt

```text
Work in `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.lean`;
claim it with `scripts/lake-locked.ps1`. Read `TimeRecursion.md` sections
`2026-06-13 EXECUTOR FINDINGS` and `2026-06-13 Planner review -- bridge accepted, endpoint decision`.

Do not start `gammaStepStar` yet. First refreeze the P3 endpoint in this downstream file as a
local-frame theorem, suggested name `residualStarSumLF`. The endpoint must quantify a smooth
`Fin 3` local frame:

  frame : Fin 3 -> (y : M) -> TangentSpace I y
  hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u
  hu : IsOpen u
  hx : x ∈ u
  basis : Module.Basis (Fin 3) Real (TangentSpace I x)
  hbasis : forall i, frame i x = basis i
  horth : forall i j, (S.base.metric (t : Real)).inner x (basis i) (basis j) =
    if i = j then 1 else 0

Carry the honest time-side inputs explicitly: the k=0 `hbase` used by `residualStarSum_zero`,
and for all-k recursion the `hrm`/`hchr`/`hswap` fields consumed by
`iteratedRmComp_hasDerivWithinAt`, or a small named input package with exactly those fields.

Deliverables:
1. A compiling theorem-shaped `residualStarSumLF` in `TimeRecursion.lean`, with at most one
   honest `sorry` for the all-k induction body.
2. A proved k=0 local-frame adapter from `residualStarSum_zero` if it is short; otherwise stop
   with the exact elaboration mismatch.
3. Update `TimeRecursion.md` with the final endpoint signature and verification result.

Stop if the endpoint cannot be stated without a vague wrapper assumption like `hstep`, or if the
time-side fields needed by `iteratedRmComp_hasDerivWithinAt` do not fit the local-frame endpoint.
Do not move/delete the old `StarSum2.lean` `residualStarSum` stub until the new endpoint elaborates.
```

## 2026-06-13 EXECUTOR FINDINGS — `residualStarSumLF` frozen (k=0 GREEN, all-k single `sorry`)

Verification: focused check PASSES with **exactly one `sorry`** (the `succ` / all-`k` body).  No
stop condition: the time-side fields fit the local frame with NO vague `hstep` wrapper.

Key elaboration facts found:

- `christoffelSymbolInFrame (cov) frame (hframe : IsLocalFrameOn I E 1 frame u) x i j k` and
  `frameComp0S (A) frame` are **frame-general** (only `realizedChr`/`realizedRmBase` specialize them
  to `coordinateFrameAt`).  So the tower's component data is given concretely for the LF frame by two
  private defs in `TimeRecursion.lean`:
  - `lfBase S frame := fun s => frameComp0S (S.base.rm04 s) frame`
  - `lfChr S frame hframe := fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y`
  (`christoffelSymbolInFrame` resolves unqualified via the `DifferentialGeometry.Tensor.Coordinates`
  open, exactly as in `RmRealizationBridge`.)
- `IsLocalFrameOn` is a **data structure** (carries `coeff`), so `lfChr` legitimately depends on the
  specific `hframe`; this is not proof-irrelevant and is correct.
- `residualStarSum_zero`'s conclusion **hard-codes the witness `e0Field`** in the derivative target
  (not the bound existential `T`).  So the k=0 adapter supplies `e0Field`/`e0Field_mem` explicitly and
  uses `residualStarSum_zero` only for the per-component `hcomp`:
  `refine ⟨e0Field S t, e0Field_mem S t, fun I0 => ?_⟩; obtain ⟨_,_,hcomp⟩ := residualStarSum_zero …; exact hcomp x basis horth I0`.

### Final endpoint signature (frozen)

```text
residualStarSumLF
  (S : SolutionOn D) (hS : IsSolutionOn S) (k : ℕ) (t : RegularTime D)
  {x : M} {u : Set M}
  (frame : Fin 3 → (y : M) → TangentSpace I y)
  (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) (hx : x ∈ u)
  (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
  (hbasis : ∀ i, frame i x = basis i)
  (horth : ∀ i j, (S.base.metric t).inner x (basis i) (basis j) = if i = j then 1 else 0)
  (hdim : ∀ y, Module.finrank Real (TangentSpace I y) = 3)
  (hbase : <residualStarSum_zero's hbase, ∀ y bas _horth I0, ∂ₜRm04 = trace + reaction>)   -- k = 0
  (baseDt : Real → M → (Fin 4 → Fin 3) → Real)                                              -- ∂ₜRm array
  (chrDt  : Real → M → Fin 3 → Fin 3 → Fin 3 → Real)                                        -- ∂ₜΓ  array
  (hrm  : ∀ m, HasDerivWithinAt (fun s => lfBase S frame s x m) (baseDt t x m) D.carrier t)
  (hchr : ∀ i a p, HasDerivWithinAt (fun s => lfChr S frame hframe s x i a p) (chrDt t x i a p) D.carrier t)
  (hswap: ∀ k' d m, HasDerivWithinAt
            (fun s => extDerivFun (fun y => iteratedRmComp   frame (lfChr S frame hframe) (lfBase S frame) k' s y m) x (frame d x))
            (        extDerivFun (fun y => iteratedRmCompDt frame (lfChr S frame hframe) chrDt (lfBase S frame) baseDt k' t y m) x (frame d x))
            D.carrier t) :
  ∃ T : Tensor0SField (4 + k), StarSum2 S t k T ∧
    ∀ (I0 : Fin (4 + k) → Fin 3),
      HasDerivWithinAt
        (fun r => tensor0SComponent (nablaKRm04Field S r k x) (fun i => basis i) I0)
        (tensor0SComponent
          (metricTrace0S2TensorInBasis basis identityInvMetric (nablaKRm04Field S t (k + 2) x) + T x)
          (fun i => basis i) I0)
        D.carrier t
```

`hrm`/`hchr`/`hswap` are exactly `iteratedRmComp_hasDerivWithinAt`'s inputs instantiated at
`Idx := Fin 3`, `frame := frame`, `chr := lfChr`, `base := lfBase`.  They are carried for the all-`k`
body but unused in the proved k=0 case.

### Remaining `sorry` (the all-`k` body) — what it must do

`succ k` branch.  The intended proof:
1. realize `iteratedRmComp frame (lfChr) (lfBase) k s y = ` the frame components of `nablaKRm04Field S s k`
   (all-`k` `RmRealizationBridgeAllK` analogue of `iteratedRmComp_one_eq_nablaRm04Field`);
2. differentiate in time via `iteratedRmComp_hasDerivWithinAt` (fed by `hrm`/`hchr`/`hswap`) to get
   `∂ₜ∇ᵏRm = iteratedRmCompDt …`;
3. normalize `iteratedRmCompDt` via `iteratedRmCompDt_succ` + `christoffelRHS_id` + the bridge
   `ricciCovDeriv_trace_nablaRm` into `metricTrace0S2TensorInBasis (…) (∇^{k+2}Rm) + (star sum)` — this
   is `gammaStepStar`, the NEXT producer.

This is a clean single mathematical frontier (`gammaStepStar`), not a routine local proof.

NOT TOUCHED (correctly): `StarSum2.lean` (the old stub move is still gated on downstream import
clean-up after `gammaStepStar`), and `gammaStepStar` itself.

## 2026-06-13 Planner review -- LF endpoint accepted, gamma input audit next

Accepted the executor deliverables as a statement-freeze/base-case pass:

- `residualStarSumLF` elaborates in `TimeRecursion.lean` with one visible `sorry`, in the `succ`
  branch only.
- The `k = 0` branch is genuinely proved from `residualStarSum_zero`, with the explicit
  `e0Field`/`e0Field_mem` witness.
- The concrete local-frame tower data `lfBase`/`lfChr` is the right shape for
  `iteratedRmComp_hasDerivWithinAt`.

Planner caveat for the next session: the all-`k` branch cannot normalize the gamma correction from
`hchr` alone.  The branch needs a value equation for the chosen derivative array:

```text
chrDt (t : Real) x i j p =
  - ricciCovDerivCompInFrame S frame (t : Real) x i j p
  - ricciCovDerivCompInFrame S frame (t : Real) x j i p
  + ricciCovDerivCompInFrame S frame (t : Real) x p i j
```

This cannot be recovered from `hchr` alone: `hchr` only says `chrDt` is *a* derivative array for
`lfChr`.  It may be derivable from `hchr` plus `christoffelEvolution_of_solution` (or
`evol_christoffel_inFrame`) and uniqueness of the time derivative within `D.carrier`; however those
producers carry inverse-metric and metric-frame regularity inputs not currently quantified in
`residualStarSumLF`.  The next executor must audit this first, but should not spend a session trying
to manufacture those inputs locally.  If they are not already available in the endpoint, adjust the
endpoint by carrying this exact pointwise value equation (`hchrId`, or an equally short name).  That
is an honest gamma-value input, not a vague `hstep` wrapper.

The other confirmed next dependency is a local-frame version of the all-`k` realization bridge.
The existing `iteratedRmComp_eq_nablaKRm04Field` in `RmRealizationBridgeAllK.lean` is
coordinate-frame specific; P3 needs the same induction for an arbitrary smooth local frame:

```text
iteratedRmComp frame
  (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
  (fun s => frameComp0S (S.base.rm04 s) frame)
  k t x n
= nablaKRm04Field S t k x (frameTuple frame x n)
```

with `{x : M}`, `hx : x in u`, `hframe : IsLocalFrameOn I E 1 frame u`, and `hu : IsOpen u`.
Suggested theorem name: `iterRmLF_eq_nabla` (short enough).  Prefer placing it in
`RmRealizationBridgeAllK.lean`; the same-name note `RmRealizationBridgeAllK.md` now records the
route.  If it is kept private in `TimeRecursion.lean`, record why.

## Next executor prompt

```text
Work in `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.lean`;
claim it with `scripts/lake-locked.ps1`.  If you edit `RmRealizationBridgeAllK.lean`, claim that
file too and update `RmRealizationBridgeAllK.md` as well.  Read `TimeRecursion.md` sections
`2026-06-13 EXECUTOR FINDINGS -- residualStarSumLF frozen` and
`2026-06-13 Planner review -- LF endpoint accepted, gamma input audit next`.

Goal: start `gammaStepStar`, but do the two mandatory audits/producers first.

1. Audit the Christoffel-time value input, briefly.
   In the `succ` branch, gamma normalization needs the pointwise identity

     chrDt (t : Real) x i j p =
       - ricciCovDerivCompInFrame S frame (t : Real) x i j p
       - ricciCovDerivCompInFrame S frame (t : Real) x j i p
       + ricciCovDerivCompInFrame S frame (t : Real) x p i j

   `hchr` alone is not enough.  Try only the direct derivation from the current endpoint plus
   `christoffelEvolution_of_solution` or `evol_christoffel_inFrame` and time-derivative uniqueness
   on `D.carrier`.  If the endpoint lacks the required inverse-metric / metric-frame regularity
   inputs, do not invent a vague wrapper and do not spend a long proof-search pass.  Add this exact
   pointwise hypothesis to `residualStarSumLF` under a short name such as `hchrId`, keep the k=0
   branch unchanged, and record the endpoint change in `TimeRecursion.md`.

2. Build or reuse the local-frame all-k realization bridge.
   First grep for an arbitrary-frame version.  If none exists, prove the local-frame analogue of
   `iteratedRmComp_eq_nablaKRm04Field`, suggested name `iterRmLF_eq_nabla`:

     iteratedRmComp frame
       (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
       (fun s => frameComp0S (S.base.rm04 s) frame)
       k t x n
     =
     nablaKRm04Field S t k x (frameTuple frame x n)

   This should follow the existing coordinate-frame proof in `RmRealizationBridgeAllK.lean`,
   replacing `coordinateFrameSet_open` with `hu` and
   `coordinateFrameAt_isLocalFrame_one` with `hframe`.  The key banked step is
   `covDerivStepComp_frameComp_eq`.  See `RmRealizationBridgeAllK.md` for the local route.

3. Then state and attempt the raw gamma correction membership lemma, preferably private first:

     gammaStepStar :
       exists Tgamma,
         StarSum2 S (t : Real) (k + 1) Tgamma /\
         forall I0,
           covDerivStepDt (chrDt (t : Real) x)
             (fun m => nablaKRm04Field S (t : Real) k x
               (fun q => basis (m q))) I0
           =
           tensor0SComponent (Tgamma x) (fun i => basis i) I0

   Use `hchrId`, `christoffelRHS_id`, the green `ricciCovDeriv_trace_nablaRm`, and the routing bank
   in `StarRouting.lean` (`slotdiffStarA` first; add only the missing private route helpers).
   Be careful with the native trace order from `ricciCovDeriv_trace_nablaRm`: `(d,e,a,b,e)`.
   Insert only the necessary `NablaRmSymm` slot normalization when a route demands it.

Deliverables:
- If steps 1 and 2 close but `gammaStepStar` does not, return with the exact normalized component
  equality that remains, the route helper needed, and no extra public wrapper.
- If `gammaStepStar` closes, use it to replace the single `sorry` in `residualStarSumLF` only if
  the IH/stNabla bridge is local and clear.  Otherwise stop with `gammaStepStar` green and the exact
  IH bridge goal.
- Update `TimeRecursion.md` with findings and verification status.

Stop conditions:
- The current endpoint cannot supply or honestly carry `hchrId`.
- The local-frame all-k realization bridge fails for a real API reason after the coordinate-frame
  proof pattern is tried.
- The normalized gamma term is not a `base (k+1) 1 k 0` route after applying the Ricci-trace bridge
  and known `NablaRm` symmetries.
```

## 2026-06-13 EXECUTOR FINDINGS — gamma input audit done, `gammaStepStar` stated (route confirmed)

No stop condition triggered.  Focused check PASSES; the file now has TWO `sorry`s, both the same
underlying frontier: `gammaStepStar` (the routing) and `residualStarSumLF`'s `succ` branch (which
will consume `gammaStepStar`).

**Step 1 (chrDt audit → carry `hchrId`).**  `christoffelEvolution_of_solution`
(`Evolution/Connection/MetricCovDerivProducer.lean`) does produce the `∂ₜΓ = -∇Ric - ∇Ric + ∇Ric`
value (with `ricciCovDerivCompInFrame` as `∇Ric`), but only from inputs the endpoint does NOT carry:
`gInv`, `gInvDt`, `hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal`, plus `hSmooth`/`hFdiff`/
`hFtdiff` (C²/MDifferentiable metric-frame and `ricciCompInFrame` regularity).  Per the planner's
"do not manufacture those locally", I added the honest pointwise value equation `hchrId` to
`residualStarSumLF` (right after `hchr`).  The k=0 branch is unchanged and still GREEN.

**Step 2 (local-frame all-k bridge).**  GREEN — `iterRmLF_eq_nabla` added to
`RmRealizationBridgeAllK.lean` (not local), targeted-built.  See `RmRealizationBridgeAllK.md`.

**Step 3 (`gammaStepStar`).**  STATED as a private theorem in `TimeRecursion.lean`, type-correct, with
`horth` on `S.family.metric` (matching both `ricciCovDeriv_trace_nablaRm` and `slotdiffStarA`).  The
route is confirmed viable — it IS a `base (k+1) 1 k 0` route:

- `covDerivStepDt (chrDt t x) A I0 = ∑ s:Fin (4+k), ∑ p:Fin 3, (chrDt t x)(I0 0)(tail I0 s) p · A(update (tail I0) s p)`;
- `hchrId` rewrites `chrDt` into three `ricciCovDerivCompInFrame` terms;
- `ricciCovDeriv_trace_nablaRm` rewrites each into `∑_e ∇¹Rm(d,e,a,b,e)` (native trace slots 1 & 4);
- the resulting `∑ (∇¹Rm trace)·(∇ᵏRm)` products have exactly the product shape of `slotdiffStarA`'s
  RHS `starBaseField S t (k+1) 1 k 0 (sigmaDiffA k q)` = `∑_e ∑_i ∇¹Rm(i,i,m0,m_{q+1},e)·∇ᵏRm(update … q e)`.

**Precise remaining frontier (the `gammaStepStar` `sorry`):** the *witness construction* + routing
equality.  The native bridge trace order `(d,e,a,b,e)` (trace on Rm slots 1 & 4) does NOT coincide
slot-for-slot with `sigmaDiffA`'s `(i,i,m0,m_{q+1},e)` (trace on slots 0 & 1).  So assembling
`Tgamma` from `sigmaDiffA`-routed `starBaseField` terms needs the missing Christoffel-route
permutations added to `StarRouting.lean` — specifically a `NablaRmSymm` slot-`3↔4` normalization of
the bridge output before it matches a `slotdiffStarA`-style route, plus the per-`(s,p)` index routing
`(I0 0, tail I0 s, p) ↦ (m 0, m q.succ, q)`.  This is a genuine `StarRouting`-bank extension, not a
local proof.

Endpoint change recorded: `residualStarSumLF` now carries `hchrId : ∀ i j p, chrDt t x i j p =
-∇Ric_{ijp} - ∇Ric_{jip} + ∇Ric_{pij}` (with `∇Ric = ricciCovDerivCompInFrame`).  Honest value input,
not a vague `hstep`.

## 2026-06-13 EXECUTOR — `gammaStepStar` LHS normalized (verified), witness frontier pinned

The `gammaStepStar` proof now contains a VERIFIED reduction `hLHS` (no longer a bare `sorry`); only
the StarSum2 witness construction is the remaining `sorry`.  `hLHS` proves, for every `I0`:

```text
covDerivStepDt (chrDt t x) (fun m => ∇ᵏRm x (basis ∘ m)) I0
  = ∑ s:Fin (4+k), ∑ p:Fin 3,
      ( -(∑ e, ∇¹Rm(I0₀, e, Tₛ, p, e))
        -(∑ e, ∇¹Rm(Tₛ, e, I0₀, p, e))
        +(∑ e, ∇¹Rm(p,  e, I0₀, Tₛ, e)) )      -- I0₀ := I0 0,  Tₛ := Fin.tail I0 s
    * ∇ᵏRm x (basis ∘ update (Fin.tail I0) s p)
```

proved by `simp only [covDerivStepDt]` + `Finset.sum_congr` ×2 + `rw [hchrId, hbridge ×3]` where
`hbridge` is `ricciCovDeriv_trace_nablaRm` specialized to the frame (native trace order
`(d,e,a,b,e)`).  This is the EXACT normalized component equality the witness must match.

### The witness frontier — `(1,4)`-trace routes (must be built in `StarRouting.lean`)

CONFIRMED that `slotdiffStarA` cannot be reused, even up to symmetry:

- `slotdiffStarA`'s `∇¹Rm(i, i, m0, m_{q+1}, e)` self-traces slot `0 ↔ 1` — the **∇-direction
  against the first Riemann index** (a divergence-type trace).
- the gamma term's `∇¹Rm(d, e, a, b, e)` self-traces slots `1 ↔ 4` — **two Riemann indices** (the
  Ric trace), with the ∇-direction `d` FREE.
- `NablaRmSymm` permutes only the four Riemann indices, NOT the ∇-slot, so it cannot turn a
  `(1,4)`-Riemann trace into a `(0,1)` `∇`-Riemann trace.  The routes are genuinely distinct.

So the witness `Tgamma` must be assembled from a NEW `(1,4)`-self-trace route family.  Structure
(parametrized by the cross-slot `q : Fin (4+k)`, which is `sigmaDiffA`'s parameter):

```text
Tgamma = ∑ q : Fin (4+k),
  ( - starBaseField S t (k+1) 1 k 0 (σ₁ q)     -- ∇¹Rm(•, e, •, p, e), cross p ↔ ∇ᵏRm slot q
    - starBaseField S t (k+1) 1 k 0 (σ₂ q)     -- the j↔i-swapped Ric term
    + starBaseField S t (k+1) 1 k 0 (σ₃ q) )   -- the p-in-∇-slot Ric term
```

with three `σᵢ q : Fin (9+k) ≃ Fin (9+k)` routing the product `∇¹Rm ⊗ ∇ᵏRm` so that `mtIter 2`
realizes (a) the `∇¹Rm` slot-`1↔4` self-trace and (b) the cross-trace of the remaining free `∇¹Rm`
slot with `∇ᵏRm` slot `q`.

**The exact routing functions are now derived** (product slots: `0–4 = ∇¹Rm`, `5+j = ∇ᵏRm` slot `j`;
target: positions `0,1` = first traced pair, `2,3` = second traced pair, `4 = m0`, `5+q = m_{q+1}`,
else identity — read off `tfDiffA`).  The OUTPUT routing is IDENTICAL to `tfDiffA`; only the `∇¹Rm`
slot roles change.  For the three `hLHS` terms:

```text
-- term 1  ∇¹Rm(I0₀, e, Tₛ, p, e): self-trace {1,4}=e,e; cross {3}=p; free {0}→m0, {2}→m_{q+1}
tfDiffB1 k q a := if a=1 then 0 | a=4 then 1 | a=3 then 2 | a=5+q then 3 | a=0 then 4
                  | a=2 then 5+q | else a
-- term 2  ∇¹Rm(Tₛ, e, I0₀, p, e): like B1 but free {0}→m_{q+1}, {2}→m0  (i.e. swap a=0,a=2 targets)
tfDiffB2 k q a := if a=1 then 0 | a=4 then 1 | a=3 then 2 | a=5+q then 3 | a=2 then 4
                  | a=0 then 5+q | else a
-- term 3  ∇¹Rm(p, e, I0₀, Tₛ, e): self-trace {1,4}; cross {0}=p; free {2}→m0, {3}→m_{q+1}
tfDiffB3 k q a := if a=1 then 0 | a=4 then 1 | a=0 then 2 | a=5+q then 3 | a=2 then 4
                  | a=3 then 5+q | else a
```

Each is a bijection of `Fin (9+k)` (targets `{0,1,2,3,4,5+q}` ↔ sources `{0,1,2,3,4,5+q}`), so
`Equiv.ofBijective` + the `bijective_iff_injective_and_card` boilerplate applies verbatim.  Each then
needs `_cast_val`/`_nat_val` lemmas and a `slotdiffStarA`-style evaluation (via `starBaseProd_eq`).
Then `gammaStepStar` closes by `hLHS` + `starSum2_sum` over `q` + the three evaluations + the
orthonormal `e`-collapse.  (NB: the `∇¹Rm` self-trace is now slots `1,4`, so `starBaseProd_eq`'s
first-two-traces land on `∇¹Rm`'s `1,4` after `domDomCongr`, matching the `e,e` in `hLHS`.)

This is a well-defined `StarRouting.lean` build (3 route families, σ's given explicitly above); it is
the genuine next frontier.  No stop condition triggered (route IS a `base (k+1) 1 k 0` route; `hchrId`
carried; bridge green; `hLHS` reduction verified).

## 2026-06-13 EXECUTOR — `gammaStepStar` CLOSED (0 sorry); 3 routes GREEN in `StarRouting`

`gammaStepStar` is now **fully proved** (no `sorry`).  The only remaining `sorry` in the file is
`residualStarSumLF`'s `succ` branch.

**Routes built (`StarRouting.lean`, all GREEN, 0 sorry):** `tfRic1/2/3`, `sigmaRic1/2/3`,
`sigmaRic{1,2,3}_cast_val`/`_nat_val`, and the evaluations `slotRic1/2/3` — the `(1,4)`-self-trace
`base (k+1) 1 k 0` variants of `slotdiffStarA`, one per `∂ₜΓ` term.  The `tf` functions are exactly
as predicted in the previous note.  The `∇ᵏRm` factor (and hence `_nat_val` and the `hR` half of
each evaluation) is identical to `slotdiffStarA`; only the `∇¹Rm` `tf`/`_cast_val`/`hL` differ.
Each evaluation is a verbatim adaptation of `slotdiffStarA`'s proof.

**`gammaStepStar` proof (TimeRecursion.lean):**
- `hbridge` = `ricciCovDeriv_trace_nablaRm` specialized to the frame.
- `hLHS` = the verified `covDerivStepDt` + `hchrId` + bridge reduction (LHS → explicit `∇¹Rm·∇ᵏRm`).
- witness `Tgamma = (-1)•TA + (-1)•TB + TC`, `T_i = ∑_q starBaseField (k+1) 1 k 0 (sigmaRic_i k q)`;
  `StarSum2` via `starSum2_sum` + `StarSum2.base/smul/add`.
- component equality: evaluate the witness via `tensor0SComponent_apply` + `ContMDiffSection.coe_add`/
  `coe_smul` + `ContinuousMultilinearMap.add_apply`/`smul_apply` + per-route `hTAp/hTBp/hTCp`
  (Finset.induction), then `Finset.smul_sum` + sum-combine, `Finset.sum_congr` over `q=s`, `slotRic`
  rewrite, `hbasis`/`hDeq` (the `update`-shape reconciliation `fun q'=>basis(update (tail I0) s p q')
  = update (basis∘(I0∘succ)) s (basis p)`), then `Finset.sum_congr` ×2 + `ring`.  The one residual
  defeq `Fin.tail I0 s = I0 s.succ` is bridged by `simp only [show … from rfl]`.
- REQUIRED: `set_option backward.isDefEq.respectTransparency false in` on `gammaStepStar` (the
  documented instance-wall fix for `0`/`+`/`•`/`∑` on `Tensor0SField`).

### Remaining frontier — `residualStarSumLF` `succ` branch (the IH/assembly bridge)

Per the directive ("if `gammaStepStar` closes, replace the `sorry` only if the IH/stNabla bridge is
local and clear; otherwise stop with `gammaStepStar` green and the exact IH bridge goal"), I stop
here: the `succ` assembly is NOT a local bridge.  It must combine, at `k+1`:
1. `iteratedRmComp_hasDerivWithinAt` (fed by `hrm`/`hchr`/`hswap`) — `∂ₜ∇ᵏRm = iteratedRmCompDt`;
2. `iterRmLF_eq_nabla` — `iteratedRmComp = nablaKRm04Field` components (realization);
3. `iteratedRmCompDt_succ` — splits `∂ₜ∇^{k+1}Rm` into `∇(∂ₜ∇ᵏRm)` (the covariant step) minus the
   gamma correction `covDerivStepDt (∂ₜΓ) (∇ᵏRm)`;
4. `gammaStepStar` (now green) — the gamma correction is a `StarSum2 (k+1)` element;
5. `spatialCommStarSum` (P2, green) — the spatial commutator `(∂ₜ−Δ)` reorganization is a `StarSum2`;
and assemble `(∂ₜ − Δ)∇^{k+1}Rm = metricTrace(∇^{k+3}Rm) + (StarSum2 element)`.  This is the heat-
equation assembly that the endpoint's conclusion states — a genuine multi-producer frontier, the
next session's task.

## 2026-06-13 PLANNER REVIEW -- `gammaStepStar` accepted; `succ` assembly next

Live review accepted the executor report.

- `gammaStepStar` is present as a private theorem in `TimeRecursion.lean` and has no internal
  `sorry`.
- `StarRouting.lean` contains the three Ricci-trace routes `tfRic1/2/3`, `sigmaRic1/2/3`,
  their `_cast_val`/`_nat_val` lemmas, and evaluations `slotRic1/2/3`.
- Source inspection of the normalized sign/routing math matches the report: `hchrId` contributes
  `-TA - TB + TC`, and `slotRic1/2/3` match the native trace terms used in `hLHS`.
- `TimeRecursion.lean` still has exactly one visible `sorry`, the intended `residualStarSumLF`
  `succ` branch.

The remaining task is not a new routing lemma. It is the multi-producer `succ` assembly:

1. use the inductive hypothesis for level `k`;
2. differentiate the local-frame tower via `iteratedRmComp_hasDerivWithinAt`;
3. use `iteratedRmCompDt_succ` to split the derivative into the covariant derivative of the
   previous residual plus the gamma correction;
4. convert tower components using `iterRmLF_eq_nabla`;
5. use `gammaStepStar` for the gamma term;
6. use `spatialCommStarSum` for the spatial commutator;
7. combine the resulting `StarSum2` witnesses with `.nabla`, `.add`, and `.smul` until the endpoint
   derivative is `metricTrace0S2TensorInBasis ... (nablaKRm04Field S (t : Real) (k+3) x) + T x`.

Stop condition for the next executor: if the IH cannot be made uniform enough to apply a spatial
derivative / `StarSum2.nabla` step at the center `x`, report the exact current goal and the missing
uniform-in-local-frame statement. Do not hide this behind a new hypothesis named `hstep`.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- gammaStepStar accepted; succ assembly next"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarRouting.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridgeAllK.md

Target:
Close the single remaining sorry in theorem residualStarSumLF in
DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.lean.

Verified inputs:
- gammaStepStar is green and supplies the StarSum2 witness for
  covDerivStepDt (chrDt t x) (nablaKRm04Field S t k x components).
- iterRmLF_eq_nabla is green in RmRealizationBridgeAllK.lean.
- spatialCommStarSum is green in SpatialMember.lean.
- residualStarSumLF already carries hchrId, hrm, hchr, and hswap.

Expected route:
1. In the succ branch, obtain the IH witness for level k from recursive residualStarSumLF.
2. Use StarSum2.nabla or the existing `.nabla` constructor/method on the IH witness for the
   covariant-derivative part of the previous residual.
3. Use iteratedRmComp_hasDerivWithinAt with hrm/hchr/hswap, then rewrite with
   iteratedRmCompDt_succ.
4. Use iterRmLF_eq_nabla to identify local-frame tower components with nablaKRm04Field components.
   Bridge frame slots to endpoint basis slots using hbasis as needed.
5. Apply gammaStepStar to the covDerivStepDt term and spatialCommStarSum to the commutator term.
6. Combine StarSum2 witnesses by add/smul/nabla until the endpoint has a single witness T.

Stop conditions:
- Stop if the IH is not uniform enough to feed StarSum2.nabla or a center/frame derivative step.
- Stop if iteratedRmComp_hasDerivWithinAt and the endpoint derivative use incompatible component
  functions after the hbasis rewrite.
- Stop if the remaining goal is a missing producer lemma; report the smallest theorem statement.

Verification:
Use scripts/lake-locked.ps1. Claim TimeRecursion.lean before editing, focused-check it, and release
the lock. If exported declarations changed upstream, refresh only the direct upstream module needed.
Update TimeRecursion.md with the result and do not paste full logs.
```

## 2026-06-13 EXECUTOR — `succ` STRUCTURAL FRONTIER: the fixed-`x` endpoint is not uniform enough

This is exactly the planner's anticipated stop condition ("if the IH cannot be made uniform enough
to apply a spatial derivative … at the center `x`, report the exact missing uniform-in-local-frame
statement").  Confirmed by source inspection — no new code written this session (`gammaStepStar`
remains GREEN; the single `sorry` is unchanged).

### The wall (precise)

The `succ` recurrence is `∂ₜ∇^{k+1}Rm = ∇(∂ₜ∇ᵏRm) − (∂ₜΓ)∗∇ᵏRm`.  In Lean:

1. `iteratedRmComp_hasDerivWithinAt` (fixed `x`) gives `∂ₜ∇^{k+1}Rm |_x = iteratedRmCompDt (k+1) t x`.
2. `iteratedRmCompDt_succ` rewrites this as
   `covDerivStepComp (frameExtData frame (fun y => iteratedRmCompDt k t y) x) (chr t x)
        (iteratedRmCompDt k t x)  −  covDerivStepDt (chrDt t x) (iteratedRmComp k t x)`.
3. The first term contains `frameExtData frame (fun y => iteratedRmCompDt k t y) x`, i.e. the
   **spatial (frame) derivative `extDerivFun` of the field `y ↦ iteratedRmCompDt k t y` at `x`**.

To identify that covariant-step term with `∇(Δ∇ᵏRm + T_k)` (so it can pair with `spatialCommStarSum`
to give `Δ∇^{k+1}Rm + star`), one needs `iteratedRmCompDt k t y = component(Δ∇ᵏRm + T_k)(y)` **on a
neighborhood of `x`** (eventual equality), not merely at `x` — because `extDerivFun` reads the field
near `x`.  The level-`k` residual that supplies this equality is the IH; but the **fixed-`x`**
`residualStarSumLF` conclusion gives the residual **only at `x`**, and `extDerivFun_eventuallyEq_congr`
needs it `=ᶠ[nhds x]`.  Agreement at a single point does not constrain the derivative.

Equivalent diagnosis: `residualStarSumLF`'s time-side inputs `hrm`/`hchr`/`hswap` are stated at the
single center `x`, so even the time-derivative `∂ₜ∇ᵏRm` is only available at `x`.  The induction step
genuinely consumes the level-`k` residual as a **field on `u`**.

This is NOT an `hstep` wrapper issue and not a missing routing lemma — it is the same `∀x`-uniformity
that the **original `StarSum2.residualStarSum` stub already has** (its conclusion is
`∀ (x : M) (basis …) …`).  The local-frame refreeze dropped that `∀x`.

### The exact missing statement (recommended endpoint restatement)

Make `residualStarSumLF` **uniform over `u`** (a planner-level design decision, since it changes the
endpoint signature):

- Replace the single pointwise `basis`/`horth`/`hx` + fixed-`x` conclusion with a frame that is
  **orthonormal throughout `u`** and a conclusion quantified over `y ∈ u`:
  ```text
  (horthU : ∀ y ∈ u, ∀ i j, (S.base.metric t).inner y (frame i y) (frame j y) = if i = j then 1 else 0)
  …
  ∀ (y : M), y ∈ u → ∀ (I0 : Fin (4+k) → Fin 3),
    HasDerivWithinAt
      (fun r => tensor0SComponent (nablaKRm04Field S r k y) (fun i => frame i y) I0)
      (tensor0SComponent (metricTrace0S2TensorInBasis (hframe.toBasisAt …) identityInvMetric
          (nablaKRm04Field S t (k+2) y) + T y) (fun i => frame i y) I0)
      D.carrier t
  ```
- Make the time-side inputs uniform: `hrm`/`hchr`/`hswap` quantified `∀ y ∈ u` (each `…At y` rather
  than `…At x`).  `iteratedRmComp_hasDerivWithinAt` is then applied per `y`.

### Verified induction route once the endpoint is uniform

- **base `k=0`:** `residualStarSum_zero` is already `∀x`, so it discharges the `∀y` base directly.
- **succ:** for each `y ∈ u`:
  1. `iteratedRmComp_hasDerivWithinAt` (at `y`) + `iterRmLF_eq_nabla` (already `∀y∈u`): the LHS deriv
     is `iteratedRmCompDt (k+1) t y`.
  2. From the IH (`∀y`) + `iteratedRmComp_hasDerivWithinAt` + derivative **uniqueness**
     (`HasDerivWithinAt.unique`, needs `UniqueDiffWithinAt ℝ D.carrier y` — verify for `RegularTime`),
     get the **field** identity `iteratedRmCompDt k t · =ᶠ[nhds y] component(Δ∇ᵏRm + T_k)`.
  3. `iteratedRmCompDt_succ` + `extDerivFun_eventuallyEq_congr` (with step 2) + `covDerivStepComp_frameComp_eq`
     ⇒ the covariant-step term is `∇(Δ∇ᵏRm + T_k) = ∇(Δ∇ᵏRm) + ∇T_k`.
  4. `spatialCommStarSum` (already `∀x`): `Δ∇^{k+1}Rm − ∇(Δ∇ᵏRm) = star_comm`.
  5. `gammaStepStar` (re-instantiated at `y`): the `covDerivStepDt` term is `star_gamma`.
  6. `T := (−1)•star_comm + StarSum2.nabla(T_k) + (−1)•star_gamma`; `StarSum2` via
     `.nabla`/`.add`/`.smul` (all exist: `StarSum2.nabla` confirmed present in `StarSum2.lean`).

Infrastructure confirmed present: `StarSum2.nabla`, `spatialCommStarSum` (`∀x`), `residualStarSum_zero`
(`∀x` base), `iterRmLF_eq_nabla` (`∀y∈u`), `gammaStepStar`, `covDerivStepComp_frameComp_eq`,
`extDerivFun_eventuallyEq_congr`.  Unverified detail to check first: `UniqueDiffWithinAt ℝ D.carrier y`
for the time domain (needed for the derivative-uniqueness step).

STOP per planner stop condition: this is a design decision (uniform-over-`u` endpoint), not a local
proof; reporting rather than unilaterally redesigning the public endpoint signature.

## 2026-06-13 PLANNER REVIEW -- uniform endpoint redesign approved

Accepted the executor's structural diagnosis after source inspection:

- `iteratedRmCompDt_succ` uses
  `frameExtData frame (fun y => iteratedRmCompDt ... k t y) x`, so the succ step genuinely needs a
  neighborhood identity for the level-`k` residual field, not only an equality at the center.
- The current `residualStarSumLF` is fixed at one `x`; its `hrm`/`hchr`/`hswap`, `hchrId`,
  orthonormality, and conclusion are all pointwise at that center.
- The old upstream `StarSum2.residualStarSum` stub had the correct consumer shape in this respect:
  after choosing a witness `T`, it concluded the residual identity for all centers.

Planner decision: restate the active endpoint as a new uniform local-frame theorem rather than
trying to prove the fixed-`x` statement.  Suggested short name: `resStarLFU`.  Keep the old
`residualStarSumLF` only as a compatibility wrapper or mark it superseded after the uniform theorem
exists; do not maintain two active P3 frontiers.

The uniform endpoint should quantify a smooth local frame on `u`, assume orthonormality on `u`, and
conclude the residual identity for every `y in u`.  Time-side inputs must also be uniform on `u`:
`hrm`, `hchr`, `hchrId`, and `hswap` should all be indexed by `y` plus `hy : y in u`.

Correction to the previous executor note: do not add `UniqueDiffWithinAt Real D.carrier y`.
The uniqueness point is the time `(t : Real)`, not the spatial point `y`.  Since
`t : RealTimeInterval.RegularTime D`, first try converting both time-within derivatives to ordinary
derivatives by

```text
(h_within_at_y ...).hasDerivAt (D.regular_mem_nhds t.2)
```

and then use ordinary `HasDerivAt` uniqueness to identify derivative values.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- uniform endpoint redesign approved"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/SpatialMember.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridgeAllK.md

Target:
Restate the active P3 endpoint as a uniform local-frame theorem in TimeRecursion.lean, suggested
short name resStarLFU, and make it elaborate with one honest succ-assembly sorry if needed.

Design:
- Keep S, hS, k, t, frame, hframe, hu, hdim, hbase, baseDt, chrDt.
- Replace fixed x/basis/hbasis/horth with uniform data on u:
  horthU : forall y, y in u -> forall i j,
    (S.base.metric (t : Real)).inner y (frame i y) (frame j y) =
      if i = j then 1 else 0
- Make time-side inputs uniform:
  hrm : forall y, y in u -> forall m, HasDerivWithinAt ...
  hchr : forall y, y in u -> forall i a p, HasDerivWithinAt ...
  hchrId : forall y, y in u -> forall i j p, chrDt (t : Real) y i j p = ...
  hswap : forall y, y in u -> forall k' d m, HasDerivWithinAt ...
- Conclude:
  exists T, StarSum2 S (t : Real) k T /\
    forall y, y in u -> forall I0,
      HasDerivWithinAt
        (fun r => tensor0SComponent (nablaKRm04Field S r k y)
          (fun i => frame i y) I0)
        (tensor0SComponent
          (metricTrace0S2TensorInBasis (hframe.toBasisAt hy) identityInvMetric
            (nablaKRm04Field S (t : Real) (k+2) y) + T y)
          (fun i => frame i y) I0)
        D.carrier (t : Real)

Implementation route:
1. Add resStarLFU below residualStarSumLF or replace residualStarSumLF if the local edit is clean.
2. Prove k=0 from residualStarSum_zero, using hframe.toBasisAt hy and horthU y hy.
3. Leave the succ branch as the single visible sorry unless the assembly is immediately local.
4. Record in TimeRecursion.md whether the uniform statement checks.

Do not add UniqueDiffWithinAt Real D.carrier y. If derivative uniqueness is needed, convert
HasDerivWithinAt facts to HasDerivAt with D.regular_mem_nhds t.2 and use HasDerivAt uniqueness.

Verification:
Claim TimeRecursion.lean with scripts/lake-locked.ps1, focused-check it, release the lock, and update
TimeRecursion.md without full logs.
```

## 2026-06-13 EXECUTOR — `resStarLFU` uniform endpoint frozen (k=0 GREEN, succ single `sorry`)

Done.  Focused check PASSES with **exactly one `sorry`** (the `succ` branch).  `residualStarSumLF`
was **replaced** by `resStarLFU` (no two active frontiers; the old fixed-`x` name was only referenced
in an `iterRmLF_eq_nabla` doc comment, no code dependency).

### What changed

- **Dropped** the fixed-center data `{x}`, `hx`, `basis`, `hbasis`, `horth`.
- **Added** uniform orthonormality `horthU : ∀ y ∈ u, ∀ i j, (S.base.metric t).inner y (frame i y)(frame j y) = if i=j then 1 else 0`.
- **Uniformized** the time-side inputs: `hrm`, `hchr`, `hchrId`, `hswap` are each now `∀ y, y ∈ u → …`
  (the inner `iteratedRmComp` field var renamed `z` to avoid shadowing the quantified `y`).
- **Conclusion** is now `∀ (y : M) (hy : y ∈ u) (I0), HasDerivWithinAt (∇ᵏRm comp in `frame · y`) (…
  metricTrace0S2TensorInBasis (hframe.toBasisAt hy) identityInvMetric (∇^{k+2}Rm) + T y …) D.carrier t`.
- `hbase`, `baseDt`, `chrDt`, `hdim`, `S`, `hS`, `k`, `t`, `frame`, `hframe`, `hu` are kept.

### k = 0 adapter (proved)

`induction k` (so `succ` carries the uniform IH `_ih`).  For `zero`: witness `e0Field`/`e0Field_mem`;
specialize `residualStarSum_zero S t hdim hbase` at `y`, the pointwise basis `hframe.toBasisAt hy`, and
`horthy` (derived from `horthU y hy` via `hframe.toBasisAt_coe hy`); then
`simpa only [hframe.toBasisAt_coe hy] using hb` rewrites `(toBasisAt hy) i → frame i y` to match the
`(fun i => frame i y)` component frame.  (`metricTrace0S2TensorInBasis (toBasisAt hy)` already matches
on both sides — `toBasisAt_coe` does not fire on the un-applied basis argument.)

### Remaining `sorry` — the `succ` Shi assembly (unchanged frontier, now actually provable)

The uniform IH `_ih` now gives the level-`k` residual `∀ y ∈ u`, so the spatial-derivative step is
unblocked.  Route (for the next session):
1. `iteratedRmComp_hasDerivWithinAt` at each `y` (fed by the uniform `hrm`/`hchr`/`hswap y hy`) +
   `iterRmLF_eq_nabla` (∀y∈u): LHS deriv `= iteratedRmCompDt (k+1) t y`.
2. From `_ih y hy` + `iteratedRmComp_hasDerivWithinAt` + derivative uniqueness: convert both
   within-derivatives to `HasDerivAt` via `(·).hasDerivAt (D.regular_mem_nhds t.2)` (NB: the
   uniqueness point is the time `t : RegularTime D`, NOT a spatial `UniqueDiffWithinAt`), giving the
   **field** identity `iteratedRmCompDt k t · =ᶠ[nhds y] component(Δ∇ᵏRm + T_k)` on `u`.
3. `iteratedRmCompDt_succ` + `extDerivFun_eventuallyEq_congr` + `covDerivStepComp_frameComp_eq`:
   covariant-step term `= ∇(Δ∇ᵏRm + T_k)`.
4. `spatialCommStarSum` (∀x) for `Δ∇^{k+1}Rm − ∇(Δ∇ᵏRm)`; `gammaStepStar` (re-instantiate at `y`) for
   the `covDerivStepDt` term.
5. `T := (−1)•star_comm + StarSum2.nabla T_k + (−1)•star_gamma`; combine via `.nabla`/`.add`/`.smul`.

Stop condition for next session: if `covDerivStepComp_frameComp_eq` needs a `TotalNabla0SRealizes`
certificate for the field `Δ∇ᵏRm + T_k` (not just `nablaKRm04Field`), report that as the missing
realizer producer.

## 2026-06-13 PLANNER REVIEW -- `resStarLFU` accepted; succ assembly is active

Live source review accepts the report.

- `resStarLFU` is now the active P3 endpoint in `TimeRecursion.lean`.
- The fixed-center data have been removed from the endpoint; orthonormality and the time-side inputs
  are uniform over `u`.
- The `k = 0` branch is proved from `residualStarSum_zero` by specializing to
  `hframe.toBasisAt hy` and rewriting with `hframe.toBasisAt_coe hy`.
- Grep shows exactly one active Lean `sorry` in the checked StarSum P3 files: the `resStarLFU`
  `succ` branch.

The next executor should not revisit endpoint design.  The active frontier is now the actual
Shi-recursion assembly in the `succ` branch.  Expected first ingredients:

- extract the IH witness `Tk`, `hTk : StarSum2 S (t : Real) k Tk`, and the uniform IH component
  identity from `_ih`;
- set `hcov := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)` for
  `StarSum2.nabla`;
- set `hmc := solution_isMetricCompatible (I := I) S (t : Real)` for `spatialCommStarSum`;
- instantiate `spatialCommStarSum` at `Idx := Fin 3`, point `y`, basis `hframe.toBasisAt hy`,
  inverse metric `identityInvMetric`, and the orthonormality from `horthU y hy`;
- instantiate `gammaStepStar` at `y`, `basis := hframe.toBasisAt hy`, with
  `hbasis := fun i => (hframe.toBasisAt_coe hy i).symm` or the orientation Lean wants;
- use `.hasDerivAt (D.regular_mem_nhds t.2)` on the two time-derivative facts before derivative
  uniqueness.

Stop condition remains narrow: if the covariant-step of the IH residual requires a new
`TotalNabla0SRealizes`/field-realizer theorem for
`metricTraceFirstTwoField (nablaKRm04Field S t (k+2)) + Tk`, report that exact theorem as the
missing producer.  Do not replace it by a vague `hstep` hypothesis.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- resStarLFU accepted; succ assembly is active"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/SpatialMember.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarRouting.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridgeAllK.md

Target:
Fill the single remaining sorry in the succ branch of resStarLFU in TimeRecursion.lean, or stop with
the smallest missing producer theorem.

Known green inputs:
- resStarLFU is the active uniform endpoint; k=0 is proved.
- gammaStepStar is green.
- spatialCommStarSum is green.
- iterRmLF_eq_nabla is green.
- StarSum2.nabla is green.

Suggested route:
1. In the succ branch, extract the IH witness Tk and hTk from _ih.
2. Let hcov := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2).
   Use hcov with StarSum2.nabla hTk for the stNabla Tk witness.
3. Let hmc := solution_isMetricCompatible (I := I) S (t : Real).
   Instantiate spatialCommStarSum with hcov, hmc, Idx := Fin 3, basis := hframe.toBasisAt hy,
   gInv := identityInvMetric, and horth from horthU y hy via hframe.toBasisAt_coe hy.
4. Instantiate gammaStepStar at the same y and basis. Use hchrId y hy and rewrite
   hframe.toBasisAt hy back to frame values with hframe.toBasisAt_coe hy.
5. Use iteratedRmComp_hasDerivWithinAt at y with hrm y hy, hchr y hy, hswap y hy, then rewrite with
   iteratedRmCompDt_succ and iterRmLF_eq_nabla.
6. To identify the level-k derivative value from IH, convert the relevant HasDerivWithinAt facts to
   HasDerivAt using .hasDerivAt (D.regular_mem_nhds t.2), then use derivative uniqueness.
7. Apply extDerivFun_eventuallyEq_congr and covDerivStepComp_frameComp_eq to turn the covariant-step
   term into nabla(metricTrace + Tk). Combine with spatialCommStarSum and gammaStepStar.
8. Assemble the final witness with StarSum2.nabla hTk, the spatial witness, and the gamma witness
   using .add/.smul. Keep signs from iteratedRmCompDt_succ, not from prose.

Stop conditions:
- Stop if covDerivStepComp_frameComp_eq needs a TotalNabla0SRealizes certificate for
  metricTraceFirstTwoField (nablaKRm04Field S t (k+2)) + Tk that is not currently available.
- Stop if the IH derivative uniqueness only gives a pointwise equality and cannot be promoted to
  eventual equality on nhds y; report the exact goal.
```

## 2026-06-13 EXECUTOR — `traceOrthoEq` banked GREEN; precise blocker = `gammaStepStar` is fixed-`x`

Focused check PASSES; one `sorry` (resStarLFU `succ`).  No `.lean` regressions.

### Concrete progress: `traceOrthoEq` (GREEN, private, in `TimeRecursion.lean`)

The orthonormal↔intrinsic trace bridge the succ assembly needs is now banked:
```text
traceOrthoEq (g) (basis) (horth : ∀ i j, g.inner x (basis i)(basis j) = if i=j then 1 else 0) (T) (tail) :
  metricTrace0S2TensorInBasis basis identityInvMetric T tail = metricTraceFirstTwo0STensor g T tail
```
Proof: `metricTrace0S2TensorInBasis_apply` + `metricTraceFirstTwo0STensor_apply` +
`metricTrace0S2InBasis_eq_metricTrace` (hinv from `metricInverseInBasis_identity_of_orthonormal`).
This reconciles the endpoint's `metricTrace0S2TensorInBasis (toBasisAt hy)` with `spatialCommStarSum`'s
intrinsic `metricTraceFirstTwo0STensor`.

### Stop-condition resolved: NO missing realizer producer

The planner's stop condition ("`covDerivStepComp_frameComp_eq` needs a missing `TotalNabla0SRealizes`
for `metricTraceFirstTwoField (∇^{k+2}Rm) + Tk`") does NOT trigger: `stNabla_realizes S t A` supplies
`TotalNabla0SRealizes (4+k) (S.family.connection t) A (stNabla S t A)` for **any** field `A`, including
`A := metricTraceFirstTwoField g (∇^{k+2}Rm) + Tk`.  So that piece is producer-complete.

### THE actual blocker: `gammaStepStar` is fixed-`x`, but the uniform endpoint needs `∀y`

`resStarLFU`'s conclusion is `∃ T, StarSum2 ∧ ∀ y ∈ u, …` — a **single global** `T`.  Composing the
producers into one `T` requires each producer's witness to be obtained ONCE (global) with its
component equality holding `∀ y`:
- `spatialCommStarSum` IS `∀x` (its `∃ T` is outside, comp-eq `∀ x basis …`) — composes fine.
- `StarSum2.nabla hTk` gives the global field `stNabla S t Tk` — composes fine.
- **`gammaStepStar` is fixed-`x`** (`{x}`, `hx : x ∈ u`, basis at `x`, comp-eq `∀ I0` at that `x`).
  Instantiating it "at `y`" (planner route step 4) yields a **per-`y`** `∃ Tgamma`; although its proof
  witness `(-1)•TA+(-1)•TB+TC` is a center-independent global field, the `∃` hides that, so the
  per-`y` `Tgamma`s cannot be collapsed into the single endpoint `T`.

**Smallest next producer change:** uniformize `gammaStepStar` to `∀ y ∈ u` (mirroring
`spatialCommStarSum`'s `∀x` shape and the `resStarLFU` redesign): statement
`∃ Tgamma, StarSum2 S t (k+1) Tgamma ∧ ∀ y ∈ u, ∀ I0, covDerivStepDt (chrDt t y) (…∇ᵏRm at y…) I0 =
tensor0SComponent (Tgamma y) (frame · y) I0`, with `hchrId`/orthonormality uniform (`∀ y ∈ u`).
Its witness (the `sigmaRic` route sums) is already global; the proof body is the existing per-component
reduction re-run at a variable `y` (basis `hframe.toBasisAt hy`, `hchrId y hy`, `horthU y hy`) — the
same mechanical uniformization done for the endpoint.  This is well-defined and producer-complete (no
new math).

### Then the succ assembly composes (route, all lemmas confirmed)

Obtain `Tcomm` (spatialComm, once), `Tgamma` (uniform gammaStepStar, once), `hTk`/`Tk` (from `_ih`).
Witness `T := stNabla S t Tk + (-1)•Tcomm + (-1)•Tgamma`; `StarSum2` via
`(StarSum2.nabla hcov hTk).add ((hTcomm.smul (-1)).add (hTgamma.smul (-1)))`.  Per `y ∈ u`, `I0`:
`iteratedRmComp_hasDerivWithinAt` (uniform inputs) + `iterRmLF_eq_nabla` frames the LHS; the derivative
value `iteratedRmCompDt (k+1) t y` is normalized by `iteratedRmCompDt_succ`, the IH field-identity
(via `.hasDerivAt (D.regular_mem_nhds t.2)` uniqueness + `extDerivFun_eventuallyEq_congr` +
`covDerivStepComp_frameComp_eq` + `stNabla_realizes`), `spatialCommStarSum`, `gammaStepStar`, and
`traceOrthoEq` (now banked) into `metricTrace0S2TensorInBasis (toBasisAt hy) identityInvMetric
(∇^{k+3}Rm) + T y`.  Signs: `T = ∇Tk − comm − gamma` (from `∂ₜ∇^{k+1}Rm = ∇(Δ∇ᵏRm+Tk) − gamma` and
`Δ∇^{k+1}Rm = ∇(Δ∇ᵏRm) + comm`).
- Stop after three genuinely different local rewrite/coercion routes fail on the same obligation.

Verification:
Claim TimeRecursion.lean with scripts/lake-locked.ps1, focused-check TimeRecursion.lean, release the
lock, and update TimeRecursion.md without full logs.
```

## 2026-06-13 PLANNER REVIEW -- trace bridge accepted; uniform gamma next

Live source review accepts the executor report.

- `traceOrthoEq` is present in `TimeRecursion.lean` and is exactly the orthonormal-basis trace to
  intrinsic trace bridge needed to reconcile `metricTrace0S2TensorInBasis (hframe.toBasisAt hy)` with
  `spatialCommStarSum`'s intrinsic trace.
- `resStarLFU` is the active uniform endpoint, and the only local P3 frontier in this file remains
  the `succ` branch `sorry`.
- The previous stop condition does not trigger: the derivative-of-field realization is not missing,
  since `stNabla_realizes S t A` is available for arbitrary fields `A`.
- The real blocker is witness scope. `spatialCommStarSum` and `StarSum2.nabla` provide one global
  witness with component equalities for every point, but `gammaStepStar` is still fixed at a single
  `{x}`. Instantiating it pointwise gives per-`y` existential witnesses, which cannot be collapsed
  into the single global witness required by `resStarLFU`.

Planner decision: do not grind the `resStarLFU` `succ` assembly first. The next producer is a
uniform gamma theorem, suggested private name `gammaStarU`, using the same global route-sum witness
already built inside `gammaStepStar`.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- trace bridge accepted; uniform gamma next"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarRouting.md

Target:
Uniformize `gammaStepStar` in `TimeRecursion.lean`. Add a private theorem, suggested short name
`gammaStarU`, with one global witness:

  exists Tgamma, StarSum2 S t (k+1) Tgamma and
    forall y, y in u -> forall I0,
      covDerivStepDt (chrDt t y)
        (fun m => nablaKRm04Field S t k y (fun q => frame (m q) y)) I0
      =
      tensor0SComponent (Tgamma y) (fun i => frame i y) I0

Inputs should mirror the uniform endpoint:
- `frame`, `hframe`, `hu`
- uniform orthonormality `horthU : forall y, y in u -> ...`
- uniform Christoffel value equation `hchrIdU : forall y, y in u -> ...`

Implementation route:
1. Do not recompute the mathematics. Reuse the existing `gammaStepStar` proof body, but move the
   fixed-point choices under `intro y hy`.
2. Define the shared witness once, outside the pointwise proof:
   `TA := sum q, starBaseField S t (k+1) 1 k 0 (sigmaRic1 k q)`;
   `TB := sum q, starBaseField S t (k+1) 1 k 0 (sigmaRic2 k q)`;
   `TC := sum q, starBaseField S t (k+1) 1 k 0 (sigmaRic3 k q)`;
   `Tgamma := (-1) • TA + (-1) • TB + TC`.
3. Prove `StarSum2` membership exactly as in `gammaStepStar`.
4. For the component equality, fix `y hy I0`; specialize the old local proof pattern with
   `basis := hframe.toBasisAt hy`, rewrite basis values using `hframe.toBasisAt_coe hy`, and use
   `hchrIdU y hy` plus `horthU y hy`.
5. If the metric spelling differs between `S.family.metric t` and `S.base.metric t`, first try the
   existing solution metric bridge/simp pattern already used in this file. Stop and report the exact
   goal only if that bridge is not available.
6. Keep the old fixed-point `gammaStepStar` as a wrapper if cheap, or leave it in place; do not delete
   working code unless all references are updated.
7. After `gammaStarU` checks, attempt the `resStarLFU` succ branch only if the remaining assembly is
   plainly local. Otherwise stop with `gammaStarU` green and report the next exact obligation.

Stop conditions:
- Stop if `hframe.toBasisAt hy` / frame-value rewriting blocks the component equality; report the
  exact goal and whether the old `hbasis` orientation is needed.
- Stop if the shared witness unexpectedly depends on `x`; report the exact line where that
  dependency enters.
- Stop after three genuinely different local rewrite/coercion routes fail on the same obligation.

Verification:
Claim `TimeRecursion.lean`, focused-check it with `scripts/lake-locked.ps1`, release the lock, and
update `TimeRecursion.md` without full logs. Do not run a full build.
```

## 2026-06-13 EXECUTOR — `gammaStarU` GREEN (uniform gamma); succ now fully producer-ready

`gammaStarU` compiles GREEN on the **first try**.  Focused check passes; the only `sorry` is the
`resStarLFU` succ branch.  This removes the witness-scope blocker.

### `gammaStarU` (private, GREEN, in `TimeRecursion.lean`)

```text
gammaStarU (S) (t) (k) {u} (frame) (hframe) (hu)
  (horthU  : ∀ y ∈ u, ∀ i j, (S.base.metric t).inner y (frame i y)(frame j y) = if i=j then 1 else 0)
  (chrDt) (hchrIdU : ∀ y ∈ u, ∀ i j p, chrDt t y i j p = -∇Ric_{ijp} - ∇Ric_{jip} + ∇Ric_{pij}) :
  ∃ Tgamma, StarSum2 S t (k+1) Tgamma ∧
    ∀ y ∈ u, ∀ I0, covDerivStepDt (chrDt t y)
        (fun m => nablaKRm04Field S t k y (fun q => frame (m q) y)) I0
      = tensor0SComponent (Tgamma y) (fun i => frame i y) I0
```

Same global witness `(-1)•TA + (-1)•TB + TC` (route sums, no `x`) and same proof body as
`gammaStepStar`; the only changes (all the planner's predicted route):
- witness + `StarSum2` proved ONCE (outside `∀y`); component proof under `intro y hy I0`.
- `hbasis_y i := (hframe.toBasisAt_coe hy i).symm` (orientation `frame i y = (toBasisAt hy) i`, same as
  the old `hbasis`).
- `horth_y` from `horthU y hy` via `rw [← hbasis_y i, ← hbasis_y j, SolutionOn.family_metric]` — the
  `S.family.metric ↔ S.base.metric` bridge is exactly the `@[simp] SolutionOn.family_metric` already
  used in this layer (no new producer).
- `simp only [hbasis_y]` converts the goal's `frame · y` to `(toBasisAt hy)` so the rest of the proof
  (`hbridge_y`, `hLHS_y`, `hDeq`, `hTAp/hTBp/hTCp`, `slotRic1/2/3 … (toBasisAt hy) horth_y`, the
  `sum_congr`+`ring` match) is the `gammaStepStar` body verbatim at the variable `y`.

No stop condition triggered: frame-value rewriting did NOT block (the `hbasis_y` orientation is the
same as the old `hbasis`), and the witness is `x`-free (route sums).

### Status of the succ assembly: producer-complete, NOT yet local

Per the directive I did NOT grind the succ assembly (it is the full Shi recurrence, ~150 lines, not
"plainly local").  But every producer it needs is now green and uniform:
- `gammaStarU` (∀y, single global witness) — NEW, green.
- `spatialCommStarSum` (∀x) — green.
- `traceOrthoEq` (orthonormal↔intrinsic trace) — green.
- `StarSum2.nabla` (`hcov := connSmoothOfSol S hS t (D.regular_subset t.2)`), `stNabla_realizes`,
  `iterRmLF_eq_nabla`, `iteratedRmComp_hasDerivWithinAt`, `iteratedRmCompDt_succ`,
  `covDerivStepComp_frameComp_eq`, `extDerivFun_eventuallyEq_congr` — all green/confirmed.

**Next exact obligation (succ branch of `resStarLFU`):** obtain `Tk`/`hTk` from `_ih`, `Tcomm` from
`spatialCommStarSum` (∀x), `Tgamma` from `gammaStarU` (∀y) — each ONCE.  Set
`T := stNabla S t Tk + (-1)•Tcomm + (-1)•Tgamma`; `StarSum2` via
`(StarSum2.nabla hcov hTk).add ((hTcomm.smul (-1)).add (hTgamma.smul (-1)))`.  Per `y ∈ u`, `I0`:
`iteratedRmComp_hasDerivWithinAt` (uniform inputs) + `iterRmLF_eq_nabla` frames the LHS; normalize the
derivative value `iteratedRmCompDt (k+1) t y` via `iteratedRmCompDt_succ`, the IH field-identity (from
`_ih y hy` + `iteratedRmComp_hasDerivWithinAt` + `.hasDerivAt (D.regular_mem_nhds t.2)` uniqueness +
`extDerivFun_eventuallyEq_congr` + `covDerivStepComp_frameComp_eq` + `stNabla_realizes`),
`spatialCommStarSum`, `gammaStarU`, and `traceOrthoEq`, into
`metricTrace0S2TensorInBasis (toBasisAt hy) identityInvMetric (∇^{k+3}Rm) + T y`.  Signs:
`T = ∇Tk − comm − gamma` (from `∂ₜ∇^{k+1}Rm = ∇(Δ∇ᵏRm+Tk) − gamma`, `Δ∇^{k+1}Rm = ∇(Δ∇ᵏRm) + comm`).

### Cleanup note
`gammaStepStar` (the old fixed-`x` form) is now **subsumed by `gammaStarU`** and is unused (private,
the succ branch does not yet call it).  Left in place per the directive; it is safe to delete once the
succ assembly is wired to `gammaStarU` (≈165 lines of duplicate proof).

## 2026-06-13 PLANNER REVIEW -- gammaStarU accepted; close resStarLFU succ

Live source review accepts the executor report.

- `gammaStarU` is present in `TimeRecursion.lean` as the uniform gamma producer: one global
  `Tgamma` witness, with the component equality under `forall y, y in u`.
- The old fixed-center `gammaStepStar` is private and now only appears as its own declaration plus
  comments. It can be deleted after the succ branch is wired to `gammaStarU`.
- `resStarLFU` remains the single active P3 endpoint frontier in this file. The only local proof
  hole is the succ branch.
- The producers needed by the succ branch were checked by name in the live tree:
  `StarSum2.nabla`, `stNabla_realizes`, `spatialCommStarSum`, `traceOrthoEq`,
  `iterRmLF_eq_nabla`, `iteratedRmComp_hasDerivWithinAt`, `iteratedRmCompDt_succ`,
  `covDerivStepComp_frameComp_eq`, and `extDerivFun_eventuallyEq_congr`.

Planner decision: the next executor should attempt the succ branch of `resStarLFU`. This is no longer
a producer-design task; it is the full Shi recurrence assembly. If it closes, delete the obsolete
private `gammaStepStar` and update comments/docstrings that still name it.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- gammaStarU accepted; close resStarLFU succ"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/SpatialMember.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarRouting.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridgeAllK.md

Target:
Fill the single remaining `sorry` in the `succ` branch of `resStarLFU` in `TimeRecursion.lean`.
After the branch is green, delete the now-obsolete private fixed-center `gammaStepStar` and update
local comments that still name it. Do not change the public statement of `resStarLFU`.

Known green producers:
- `gammaStarU`: one global gamma witness with component equality for every `y in u`.
- `spatialCommStarSum`: one global commutator witness with component equality for every point/basis.
- `traceOrthoEq`: converts the endpoint's orthonormal-basis trace to intrinsic trace.
- `StarSum2.nabla` and `stNabla_realizes`.
- `iterRmLF_eq_nabla`.
- `iteratedRmComp_hasDerivWithinAt` and `iteratedRmCompDt_succ`.
- `covDerivStepComp_frameComp_eq` and `extDerivFun_eventuallyEq_congr`.

Assembly route:
1. In the `succ k _ih` branch, obtain the IH witness:
   `obtain <Tk, hTk, hIH> := _ih`.
2. Define the solution-side inputs once:
   `hcov := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)`;
   `hmc := solution_isMetricCompatible (I := I) S (t : Real)`.
3. Obtain `Tcomm` once from `spatialCommStarSum S hS t k hcov hmc` using `Idx := Fin 3`.
4. Obtain `Tgamma` once from `gammaStarU S (t : Real) k frame hframe hu horthU chrDt hchrId`.
5. Use witness:
   `T := stNabla S (t : Real) Tk + (-1 : Real) • Tcomm + (-1 : Real) • Tgamma`.
   Prove `StarSum2` by
   `(StarSum2.nabla hcov hTk).add ((hTcomm.smul (-1)).add (hTgamma.smul (-1)))`,
   adjusting parentheses if Lean's goal associates `+` differently.
6. For each `y hy I0`, use `iteratedRmComp_hasDerivWithinAt` with `hrm y hy`, `hchr y hy`,
   and `hswap y hy`, then rewrite the source side with `iterRmLF_eq_nabla`.
7. Normalize the derivative value by rewriting `iteratedRmCompDt_succ`.
8. For the covariant-step term:
   - use the uniform IH `hIH y hy` and derivative uniqueness after converting to `HasDerivAt` via
     `.hasDerivAt (D.regular_mem_nhds t.2)`;
   - promote the resulting level-k field identity to the spatial derivative using
     `extDerivFun_eventuallyEq_congr`;
   - apply `covDerivStepComp_frameComp_eq` with
     `A := metricTraceFirstTwoField (S.base.metric (t : Real))
       (nablaKRm04Field S (t : Real) (k+2)) + Tk`
     and `nablaA := stNabla S (t : Real) A`;
   - discharge the realizer with `stNabla_realizes S (t : Real) A`.
9. Use `spatialCommStarSum` to replace
   `metricTraceFirstTwo0STensor (nablaKRm04Field ... (k+3)) -
    totalNabla0SFun ... (metricTraceFirstTwoField ... (k+2))`
   by `Tcomm`.
10. Use `gammaStarU` for the `covDerivStepDt` term.
11. Use `traceOrthoEq` plus `horthU y hy` and `hframe.toBasisAt_coe hy` to return the trace to the
    endpoint form `metricTrace0S2TensorInBasis (hframe.toBasisAt hy) identityInvMetric`.
12. Keep signs from the definitions:
    `iteratedRmCompDt_succ` gives `covariant_step - gamma`;
    `spatialCommStarSum` gives `trace(k+3) - nabla(trace(k+2)) = comm`;
    hence the endpoint witness is `nabla(Tk) - comm - gamma`.

Stop conditions:
- Stop if derivative uniqueness gives only a pointwise identity and you cannot obtain the eventual
  equality needed by `extDerivFun_eventuallyEq_congr`; report the exact goal.
- Stop if `covDerivStepComp_frameComp_eq` does not accept
  `A := metricTraceFirstTwoField ... + Tk` with `stNabla_realizes`; report the exact type mismatch.
- Stop if the signs cannot be reconciled after expanding `iteratedRmCompDt_succ` and
  `spatialCommStarSum`; report the normalized algebraic goal before trying broad automation.
- Stop after three genuinely different local rewrite/coercion routes fail on the same obligation.

Verification:
Claim `TimeRecursion.lean`, focused-check it with `scripts/lake-locked.ps1`, release the lock, and
update `TimeRecursion.md` without full logs. If `TimeRecursion.lean` exports the closed theorem and a
downstream consumer is checked, refresh only the narrow targeted module needed; do not run a full
build.
```

## 2026-06-13 EXECUTOR — succ assembly: witness + StarSum2 + HasDerivWithinAt framing GREEN; reduced to one static identity `hval`

Major verified progress.  Focused check passes; the single remaining `sorry` is `hval` (a STATIC
algebraic identity), down from the full `succ` assembly.  Everything else in `succ` is GREEN:

- **Witness + `StarSum2` (GREEN):** `obtain ⟨Tk, hTk, hIH⟩ := _ih`;
  `hcov := connSmoothOfSol S hS (t:Real) (D.regular_subset t.2)`;
  `hmc := solution_isMetricCompatible S (t:Real)`;
  `Tcomm` from `spatialCommStarSum S hS t k hcov hmc`; `Tgamma` from
  `gammaStarU S (t:Real) k frame hframe hu horthU chrDt hchrId`.
  Witness `T := stNabla S t Tk + (-1)•Tcomm + (-1)•Tgamma`; membership
  `((StarSum2.nabla hcov hTk).add (hTcomm.smul (-1))).add (hTgamma.smul (-1))`.
  (Needed `set_option backward.isDefEq.respectTransparency false in` on `resStarLFU` for the
  `+`/`•`/`∑` instance wall.)
- **HasDerivWithinAt framing (GREEN):** `hLHSfun` rewrites the endpoint LHS function to the level-`(k+1)`
  tower component via `iterRmLF_eq_nabla` (the `lfChr`/`lfBase` defeq is handled by
  `rw [show iteratedRmComp … = nablaKRm04Field … from iterRmLF_eq_nabla …]; rfl`).  `hderiv` is
  `iteratedRmComp_hasDerivWithinAt` at `y`.  `rw [hLHSfun]` + the value rewrite reduce the goal to:

```text
hval : tensor0SComponent (metricTrace0S2TensorInBasis (toBasisAt hy) identityInvMetric (∇^{k+3}Rm y)
          + (stNabla S t Tk + (-1)•Tcomm + (-1)•Tgamma) y) (frame · y) I0
     = iteratedRmCompDt frame (lfChr S frame hframe) chrDt (lfBase S frame) baseDt (k+1) t y I0
```

### Complete route for `hval` (the remaining static identity — all producers ready)

1. **Field identity** `hfield : ∀ z ∈ u, iteratedRmCompDt … k t z = frameComp0S A frame z`,
   `A := metricTraceFirstTwoField (S.base.metric t) (nablaKRm04Field S t (k+2)) + Tk`.
   Per `z, n`: `hfun` (LHS-fn = tower-fn, as in `hLHSfun`); `hd1 := iteratedRmComp_hasDerivWithinAt … k n`;
   `rw [hfun] at hd1`; `huniq := (hd1.hasDerivAt hmem).unique ((hIH z hz n).hasDerivAt hmem)` with
   `hmem := D.regular_mem_nhds t.2`; then reconcile `tensor0SComponent (metricTrace0S2TensorInBasis
   (toBasisAt hz) id (∇^{k+2}Rm z) + Tk z) (frame·z) n = frameComp0S A frame z n` via `traceOrthoEq`
   (with `horth_z` from `horthU z hz` + `toBasisAt_coe`), `metricTraceFirstTwoField_apply`,
   `frameComp0S`/`frameTuple`/`tensor0SComponent` defs, and `ContinuousMultilinearMap.add_apply`.
2. `rw [iteratedRmCompDt_succ]` + `Pi.sub_apply`: RHS = covariant-step `−` gamma (at `I0`).
3. **Gamma term:** rewrite `iteratedRmComp … k t y` to `fun m => nablaKRm04Field S t k y (fun q =>
   frame (m q) y)` (funext + `iterRmLF_eq_nabla` + `frameTuple`), then `hgamma y hy I0`
   = `tensor0SComponent (Tgamma y) (frame·y) I0`.
4. **Covariant-step term** (the fiddliest): use `hfield` to rewrite the `frameExtData`/value inputs of
   `covDerivStepComp` to `frameComp0S A frame` (eventual-eq near `y` via `extDerivFun_eventuallyEq_congr`,
   value at `y` via `hfield y hy`), `lfChr t y = christoffelSymbolInFrame …` (defeq); apply
   `covDerivStepComp_frameComp_eq A (stNabla S t A) (stNabla_realizes S t A) frame hframe hu hy I0`
   ⇒ `(stNabla S t A) y (frameTuple frame y I0) = tensor0SComponent (stNabla S t A y) (frame·y) I0`.
5. **Match:** `stNabla_add` splits `stNabla A = stNabla(metricTraceFirstTwoField g (∇^{k+2}Rm)) + stNabla Tk`;
   `hcomm` (spatialComm at `y`, `toBasisAt hy`, `identityInvMetric`, `hinv`, `horth_y`, `I0`):
   `metricTraceFirstTwo0STensor g (∇^{k+3}Rm y)(·) − totalNabla0SFun (4+k) conn (metricTraceFirstTwoField
   g (∇^{k+2}Rm)) y (·) = comp(Tcomm y)`; `traceOrthoEq` bridges the endpoint's
   `metricTrace0S2TensorInBasis (toBasisAt hy)` ↔ `metricTraceFirstTwo0STensor g`; then
   `tensor0SComponent` linearity (`add`/`smul_apply`) + `ring`.  Signs: `T = ∇Tk − comm − gamma`.

The riskiest remaining sub-step is (4): matching the `covDerivStepComp` inputs (`frameExtData` of the
field) to `covDerivStepComp_frameComp_eq` via the `hfield` eventual equality.  No missing producer.

NOTE: `gammaStepStar` (old fixed-`x`) NOT yet deleted — per directive, delete only after `succ` is green.

## 2026-06-13 PLANNER REVIEW -- hval reduction accepted; prove static identity next

Live source review accepts the executor report.

- `resStarLFU` now has the succ witness, `StarSum2` membership, and `HasDerivWithinAt` framing
  checked in Lean. The remaining hole is the local static identity named `hval`.
- The remaining `hval` statement is exactly the equality between the endpoint trace-plus-witness
  component and `iteratedRmCompDt ... (k+1) ...`.
- The old fixed-center `gammaStepStar` is still present and should stay until `hval` and the whole
  succ branch are closed.
- The riskiest sub-step is not a missing producer; it is the `frameExtData` germ-congruence needed
  to feed `covDerivStepComp_frameComp_eq`. A private pattern exists in
  `HCGCompactness/AkMFold.lean` as `frameExtData_congr_nhds`, but it is private and not imported as
  API. For this file, a short private helper `frameExtGerm` is appropriate if direct rewriting is
  noisy.

Planner decision: next executor should prove `hval` only. Start by proving the field identity and
the `frameExtData` matching; after `hval` closes, remove the obsolete private `gammaStepStar`.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md, especially
  "2026-06-13 PLANNER REVIEW -- hval reduction accepted; prove static identity next"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridge.lean
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/RmRealizationBridgeAllK.lean
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/IteratedRmTowerHeatEq.lean

Target:
Fill the single remaining `sorry`, the local `hval` proof in the `succ` branch of `resStarLFU` in
`TimeRecursion.lean`. Do not change the public statement. After the succ branch is fully green,
delete the obsolete private fixed-center `gammaStepStar` and update comments that still mention it.

Current checked state:
- Witness is already fixed:
  `T := stNabla S (t : Real) Tk + (-1 : Real) • Tcomm + (-1 : Real) • Tgamma`.
- `StarSum2` membership is green.
- `hLHSfun` and `hderiv` are green.
- The only remaining obligation is `hval`.

Recommended proof shape:
1. If direct rewriting of `frameExtData` is noisy, add a private helper above `resStarLFU`:

   `frameExtGerm`:
   if `F1 =ᶠ[nhds y] F2`, then
   `frameExtData frame F1 y = frameExtData frame F2 y`.

   Prove it by `funext m d`, then `extDerivFun_eventuallyEq_congr (frame d y)` and specialize the
   eventual equality at `m`. This is the same pattern as the private `frameExtData_congr_nhds` in
   `HCGCompactness/AkMFold.lean`; keep it private/local unless a lower-layer public API becomes
   clearly necessary.

2. Inside `hval`, define
   `A := metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
       (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk`.

3. Prove a uniform field identity on `u`:
   `hfieldU : forall z, z in u ->
      (fun m => iteratedRmCompDt frame (lfChr S frame hframe) chrDt (lfBase S frame) baseDt
          k (t : Real) z m)
        = frameComp0S A frame z`.

   For each `z hz m`:
   - rewrite the level-k tower source function by `iterRmLF_eq_nabla`, as in `hLHSfun`;
   - get `hd1` from `iteratedRmComp_hasDerivWithinAt ... k m`;
   - convert `hd1` and `hIH z hz m` to `HasDerivAt` with `.hasDerivAt (D.regular_mem_nhds t.2)`;
   - use derivative uniqueness;
   - reconcile the derivative value in `hIH` with `frameComp0S A frame z m` using `traceOrthoEq`,
     `horthU z hz`, `hframe.toBasisAt_coe hz`, `metricTraceFirstTwoField_apply`,
     `frameComp0S_apply`, `frameTuple`, `tensor0SComponent_apply`, and add-apply simp lemmas.

4. Rewrite the RHS of `hval` with `iteratedRmCompDt_succ`. It should become:
   covariant-step term minus gamma term.

5. Gamma term:
   rewrite `iteratedRmComp ... k (t : Real) y` to the `nablaKRm04Field` frame component using
   `iterRmLF_eq_nabla`; then use `hgamma y hy I0`.

6. Covariant-step term:
   - turn `hfieldU` into an eventual equality near `y` using `hu.mem_nhds hy`;
   - use `frameExtGerm` (or the direct `extDerivFun_eventuallyEq_congr` proof) to rewrite
     `frameExtData` from the `iteratedRmCompDt` field to `frameComp0S A frame`;
   - rewrite the value input at `y` using `hfieldU y hy`;
   - unfold/defeq `lfChr (I := I) S frame hframe (t : Real) y` to
     `christoffelSymbolInFrame (S.family.connection (t : Real)) frame hframe y`;
   - apply `covDerivStepComp_frameComp_eq` with
     `A := A`, `nablaA := stNabla (I := I) S (t : Real) A`,
     and `stNabla_realizes (I := I) S (t : Real) A`.

7. Split `stNabla S (t : Real) A` using `stNabla_add` so the covariant-step output is
   derivative-of-trace plus `stNabla Tk`.

8. Use `hcomm` at `y`, basis `hframe.toBasisAt hy`, `identityInvMetric`, inverse metric from
   `metricInverseInBasis_identity_of_orthonormal`, and orthonormality from `horthU y hy` plus
   `hframe.toBasisAt_coe hy`. This replaces
   `metricTraceFirstTwo0STensor (nablaKRm04Field ... (k+3)) - derivative-of-trace`
   by `Tcomm`.

9. Use `traceOrthoEq` to convert the endpoint trace
   `metricTrace0S2TensorInBasis (hframe.toBasisAt hy) identityInvMetric ...`
   to the intrinsic `metricTraceFirstTwo0STensor` form needed for `hcomm`.

10. Finish by tensor component linearity and scalar algebra:
    `tensor0SComponent_apply`, section add/smul apply lemmas, `Pi.add_apply`, `Pi.smul_apply`,
    then `ring` if the goal is scalar. Signs must match
    `T = stNabla Tk - Tcomm - Tgamma`.

Stop conditions:
- Stop if the derivative uniqueness step cannot produce `hfieldU`; report the exact `HasDerivAt`
  uniqueness goal and both derivative values.
- Stop if `frameExtGerm`/eventual equality does not rewrite `frameExtData`; report the exact
  `frameExtData` goal.
- Stop if `covDerivStepComp_frameComp_eq` rejects `A` or `stNabla_realizes`; report the exact type
  mismatch.
- Stop if the final sign algebra does not reconcile after expanding `iteratedRmCompDt_succ`,
  `hcomm`, and `hgamma`; report the normalized scalar goal.

Verification:
Claim `TimeRecursion.lean`, focused-check it with `scripts/lake-locked.ps1`, release the lock, and
update `TimeRecursion.md` without full logs. Do not run a full build.
```

## 2026-06-13 EXECUTOR -- resStarLFU succ GREEN, sorry-free; P3 all-k endpoint COMPLETE

Focused check PASSES, sorry-free. gammaStepStar deleted; comments in TimeRecursion.lean (gammaStarU
doc, the nablaRicReal_frame doc) and StarRouting.lean updated to cite gammaStarU.

### What closed

The hval static identity and the whole succ branch of resStarLFU are now proved. Route as planned:
Shi single-step dt-nabla^{k+1}Rm = nabla(dt-nabla^k Rm) - (dt-Gamma)*nabla^k Rm, with
dt-nabla^k Rm = Lap nabla^k Rm + Tk (IH) and Lap nabla^{k+1}Rm = nabla(Lap nabla^k Rm) + comm
(spatialCommStarSum); witness T = nabla-Tk - Tcomm - Tgamma. Pieces: hfieldU (IH field identity via
derivative uniqueness) + frameExtGerm + covDerivStepComp_frameComp_eq + stNabla_add + hcomm (=hc') +
gammaStarU + traceOrthoEq.

### Lessons (the assembly was almost entirely a TERM-SHAPE fight, not a math fight)

- linarith/ring atoms are SYNTACTIC, not defeq. The final combine kept failing because the same
  scalar appeared in several defeq-but-not-syntactic spellings: (fun p => frame (I0 p) y) from hcomm
  vs (fun a => frame (I0 a) y) from tensor0SComponent_apply vs frameTuple frame y I0 from
  covDerivStepComp_frameComp_eq, plus rank k+1+2 (endpoint) vs k+3 (spatialCommStarSum). linarith
  treats each as a distinct atom.
- Fix that worked: keep EVERY producer in the single closed atom
  tensor0SComponent X (fun i => frame i y) I0 and derive each equality (hcs, hsplit, hMfeval, hc',
  htrace, hLHS) by exact/simpa/rfl, which match up to DEFEQ -- bridging the alpha / frameTuple /
  k+1+2-vs-k+3 differences before linarith sees them. Then all atoms are syntactically identical and
  linarith [hc'] closes.
- Instance-diamond wall (documented): simp [tensor0SSpace_add_apply] (and the CMM variant) fired on
  the statement-native + but NOT on a simp-produced field-eval sum (stNabla Tk + ...) y. Full simp
  distributes it but over-unfolds (metricTrace0S2TensorInBasis -> metricTrace0S2InBasis); used full
  simp only inside the isolated hLHS (over-unfold harmless there because hLHS's STATED RHS keeps clean
  heads), closed with ring.
- rw [show A = B from rfl] for a defeq A/B is a no-op trap ("did not find pattern"); use show on the
  goal or an exact/rfl-have instead.
- standalone rfl (default transparency) closes a defeq-but-not-syntactic X = X where ring (syntactic
  atomiser) cannot -- needed to finish hfieldU.
- simp only [frameTuple] does NOT reliably unfold the frameTuple def; cleaner to never expose the
  tuple (stay in tensor0SComponent form).

### Project placement (honest)

resStarLFU is the all-k P3 residual-heat endpoint (dt - Lap) nabla^k Rm = StarSum2. It is gating
SCAFFOLDING for two still-unwired consumers: extends_of_rmBounded (the BBS/Shi derivative-bound
pillar, MaximalTime.lean sorry) and HCG Lemma 3.11's hShi input. So P3 endpoint = 100% (done,
sorry-free); the BBS pillar and HCG 3.11 that consume it remain open -- this endpoint is one
important brick, not those theorems. Next: wire resStarLFU into the norm-bound / BBS track.


## 2026-06-13 EXECUTOR -- comment cleanup + lfBase/lfChr made public (P4 prep)

- Fixed stale doc comments: the `resStarLFU` section header no longer says `residualStarSumLF` /
  "fixes one centre x" (it is uniform over `u`); both "single sorry" doc sentences updated to
  "fully proved (sorry-free)" in the prior session.
- **lfBase / lfChr: removed `private`.** A new downstream consumer
  (`TowerHeat.resStarBoundLF`) must state the `resStarLFU` time-side hypotheses `hrm`/`hchr`/`hswap`,
  which are written in terms of `lfBase`/`lfChr`; a private def cannot be named from another file.
  No theorem statement changed. Targeted rebuild of this module GREEN (3768 jobs).

## 2026-06-14 hcov/hmc cleanup

Synced callers after `StarSum2.nabla` and `spatialCommStarSum` stopped taking
solution local-smoothness/metric-compatibility witnesses.  The remaining local
regularity data in this file belongs to separate time-side hypotheses.

Verification passed for the edited file after upstream module refresh.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
time-recursion context.  The remaining regularity hypotheses are the genuine
time-side inputs, not this equivalent smoothness spelling.

Verification passed for the edited file.

## 2026-07-12 short-time-existence branch alignment

The merge made point evaluation through the old
`ContinuousMultilinearMap` representation opaque.  The finite-sum component
expansions and the induction-step trace comparison now use the public
`Tensor0SSpace.add_apply` and `Tensor0SSpace.smul_apply` theorems.  Five
representation-level rewrites in the same proof block were replaced together;
the definitions, witnesses, and mathematical statements are unchanged.

Focused verification and the targeted module refresh passed.  The all-order `resStarLFU` endpoint remains
complete and sorry-free (100%), and this compatibility repair is complete
(100%).  The short-time-existence theorem itself remains proved (100%);
branch-alignment verification is about 99% pending the downstream Hamilton
replay, and the merge commit remains 0% until final verification and diff
review.  This repair does not change the completion percentage of the Hamilton
positive-Ricci endpoint or wider HCG compactness theorem.

