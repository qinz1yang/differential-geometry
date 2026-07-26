# DLaTopSeparated.lean — the DLa head atom (`covGrad (connDiffSection)` top-separated)

## Role in the tree

Sub-brick 1 (the head atom) of the 3-part DLa top-separation (DLa → DLb → `DLa+DLb` triangle),
which is the first of the two genuinely-missing `C₀` constituents (`deTurckLieCoeffField`,
`lieCorr0Field`) of the data-weighted threeArm precursor — ruling item 2 of the R1τ frontier of the
black box `(N) = ricci_flow_unif_existence`.  `(N)` remains **0%**: these are analytic producers far
below the target theorem; a head-atom producer is machinery, not the theorem.

## What this file delivers

For the **top factor of DLa**, `covGrad (connDiffSection g₁ g₀)` (a `(1,3)` section, one covariant
derivative above the connection-difference field), three GREEN theorems in namespace
`DifferentialGeometry.Integral.Connection`:

1. `covGradConnDiffSection_perOrder_l2_topSeparated_generic` — generic in `(g₁, P, htie)`:
   ```
   ‖∇^i (covGrad (connDiffSection g₁ g₀))‖² ≤ Ktop·‖∇^{i+2}P‖² + Kc i·(1 + ∑_{j<i+2} ‖∇^jP‖²)
   ```
   `Ktop = 2·Kt0` with `Kt0` the engine head `10·S 0` → **R-independent**; `Kc i = 2·Kc0(i+1)·(i+1)·KI i`
   (house R-pattern via the ball-uniform tame-window converter `KI`).
2. `covGradConnDiffSection_realizedFam_jetL2_perOrder_topSeparated` — the `realizedFam g₀ T T' hδ hδ' s`
   wrapper (top point `i+2`, low window `i+2`, `(T,T')`-weighted).
3. `covGradConnDiffSection_realizedFam_jetL2_summed_topSeparated` — summed over `i≤a`; top window lands
   at **`a+3`** (= `∑_{j≤a+2}`, order `a+2`), low window `a+2`.  This is the deTurckLie top window
   `a+2` (one order above connDiff/Lie's `a+1`), matching arm0Base.

## Route (the recon snapshot's two-liner — held up exactly)

- The commutation identity `rfns_iteratedCovGrad_covGrad_comm_rs` (`OperatorFieldFibreNormJet.lean:514`,
  in `DifferentialGeometry.Integral.Connection`, so directly in scope) gives the **equality**
  `rfns(∇^i(covGrad Φ)) = rfns(∇^{i+1}Φ)` at `r=1,s=2,m=i,Φ=connDiffSection g₁ g₀`.  Unlike the connDiff
  field's `slotExtend` field↔section transfer (which loses a `finrank²` factor), the head atom is pure
  section — **no `finrank²`**, so `Ktop = 2·Kt0` (not `2·finrank²·Kt0`).
- The committed engine `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
  (`CurvatureCoefficientDifferenceJetTower.lean:1823`, committed-clean) applied at order **`j = i+1`**
  splits the section jet into head `10·S 0·rfns(∇^{i+2}P)` (`.1`) + data-weighted grid remainder
  (`.2`).  The engine head at `j=i+1` is `∇^{(i+1)+1}P = ∇^{i+2}P`; re-ascribed to the clean `i+2`
  index form (defeq `(i+1)+1 = i+2`).
- The remainder is reshaped by the copied private `tsResSum_le_boundedWindow` at `(i+1)` → window
  `(i+1)((i+1)+2)` which is **defeq to the converter window `(i+1)(i+3)`** — so, unlike ConnDiff at
  order `i` (which needed a `boundedFactorGridWindow_mono` widen from `(i)(i+2)` to `(i+1)(i+3)`), the
  head atom at `j=i+1` needs **no widening**.  Integrated by
  `boundedFactorGridWindow_integral_ballUniform_tameWindow` (converter at index `i`, window `(i+1)(i+3)`
  → `1 + ∑_{j<i+2}`).

## Imports / scoping win

Imports only committed-clean `RemainderCoeffL2JetMoser` + `RicciConnDiffOrder1TameEnvelope` (the same
cone as `ConnDiffJetL2Summed.lean`).  Does NOT import any `deTurckLie*` / dirty
`DeTurckLieKernelL2JetBound.lean` / dirty `CurvatureCoefficientDifferenceJetTower.lean` — the head atom
is pure `connDiffSection`, so elaboration never enters any dirty tracked file.

Private helpers copied verbatim with provenance from `ConnDiffJetL2Summed.lean` (themselves copies of
`CurvatureCoefficientDifferenceJetTower.lean` privates): `tsResSum_le_boundedWindow`, `sum_shift_le`,
`jetL2_sum_lowShift`, `iteratedCovGrad_smul_real`.  The summed form uses `jetL2_sum_lowShift a 2 2`
(top offset `p=2`, low offset `q=2` — the head atom's top point is `i+2`, unlike connDiff's `p=1`).

## Verification

Direct `lean` typecheck vs the redirected olean tree `C:/dgbuild/e87b/lib/lean` (recipe in
`RemainderCoeffTopSeparated.md`; imports only committed-clean modules whose oleans are already
co-located, so no untracked-olean co-location needed).  Header carries `autoImplicit false`,
`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`.  `#print axioms` on all three public theorems
must be exactly `[propext, Classical.choice, Quot.sound]`.

STATUS: <pending first typecheck — Codex lane held the Lean lock at dispatch; quiet-window waiter armed>

## Next (Step 2, separate/next brick)

The DLa 8-summand triangle: `deTurckLieDLaCoeffField` (2,2) is the `dLaBiContrFib` bicontraction of
`dLaLoweredCovec`; its raised `(1,3)` representative `dLaKernelRaisedCc`
(`DeTurckLieKernelL2JetBound.lean:1589`) splits as
```
A1 = covGrad(connDiffSection g₁ g₀)          -- THE TOP = this file's head atom
A2 = -covGrad(connDiffSection g_bg g₀)        -- g_bg, T-independent ⇒ Kc
+ 6 dLaQuadCc terms (± / rsDomDomCongr swap0 2 / finRotate 3)  -- product-order i+2, factors ≤ ∇^{i+1}T ⇒ Kc
```
Step 2 assembles `‖∇^i(deTurckLieDLaCoeffField)‖² ≤ Ktop·(∇^{i+2}-head) + Kc·(1+low)` from this file's
A1 producer plus the 6 quad + 1 g_bg summands' existing committed ball-uniform/grid bounds (all → Kc:
they never reach the protected top window).  The bicontraction-Leibniz relating `∇^i(deTurckLieDLa)`
(2,2) to jets of `dLaKernelRaisedCc` (1,3) is the intricate ~300-line part.  Discipline: `Ktop` may
carry `(g₀,hδ₀,g_bg)`-level constants but NEVER `R`; the 6 quad + g_bg constants go wholly to `Kc`
(R allowed there).
