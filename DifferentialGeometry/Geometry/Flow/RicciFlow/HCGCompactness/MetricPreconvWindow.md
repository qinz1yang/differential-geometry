# MetricPreconvWindow.lean — P3 window endpoint, flow-data inputs (C-II-final, in progress)

Threads the P2 flow machinery into the hypotheses of `windowPreconv_of_perTime`
(MetricPreconvBridge.lean:247), the genuine P3 window endpoint — the ABSTRACT
window convergence on `M` (NOT the P4 `SourceMetricCPConvOnWindow` pullback
object; see P3_PLAN.md "PLANNER CORRECTION").

## Landed + verified (axiom-clean, 2026-06-13)

- `evolNorm_bound_of_ricBound` — the `hbound` input of
  `timeLipschitz_of_hasDerivAt` at order `N`: `√normSq0S gRef (-2·nablaRicReal N)
  ≤ 2·(Cpp·CN + Cppp)` on `K × [β,ψ]`, from `ric_bound_field` (P2) + the `(Bₙ)`
  window cap `hboundN` + the existing `sqrt_normSq0S_smul` (`|-2| = 2`).
- `hgLip_orderN_of_solutions` — the order-`N` time-Lipschitz core:
  `metricDerivNorm N (gSeq i s) (gSeq i t) gRef x ≤ L·|s-t|`, uniform in `i`.
  = `timeLipschitz_of_hasDerivAt ∘ hevComp_of_solutions (hev) ∘
  evolNorm_bound_of_ricBound (hbound)`.  The endpoint's full `hgLip` maxes these
  over `a ≤ p`.

Note: `normSq0S_smul`/`sqrt_normSq0S_smul` already existed in AllTimesBounds.lean
(3914/3928) — consumed, not duplicated.

Gotcha: RicBound's olean was STALE (nablaRicReal/ric_bound_field read as unknown
identifiers); a targeted build of RicBound refreshed it.

## Remaining for the endpoint — the dedicated brick (NOT started)

`windowPreconv_of_perTime` needs four hypotheses; status:
1. `hgLip` (time-Lipschitz, all `a ≤ p`): order-`N` core DONE here; remaining =
   the uniform-over-`a ≤ p` max assembly (finitely many orders; each order `a`
   via `hgLip_orderN_of_solutions` at `N := a`, plus the order-0 base
   `∂ₜg = -2Ric` directly).  Bounded, mechanical.
2. `hInfLip` (limit metric time-Lipschitz): minor, sits on top of `gInf`.
3. `hstep` (per-time spatial extraction): from `metricPreconvInf` relative to a
   `gInf : ℝ → SmoothRiemannianMetric` family.
4. the dense rational time net `e`/`hdense`.

**THE dominant frontier = the `gInf : ℝ → metric` family** (a
`metricPreconvInf`-scale construction): a master diagonal (`exists_diag_subseq`)
over a dense rational time net using `metricPreconvInf` at net times; all-`t`
φ-convergence by a Cauchy-in-`Cᵖ` argument from `hgLip` + net density (note:
`metricPreconv_gInf`'s limit is along ITS OWN subsequence, not the master `φ`,
so it can't be reused pointwise at non-net `t`); per-`t` smoothness via
`smoothMetric_of_localCoeff`.  This is its own focused session.

**`hShi` dependency:** `hgLip` threads (via `ric_bound_field`/`hevComp_of_solutions`)
the moving-Shi tower bound `hShi` and the swap `hswap` as honest hypotheses — the
same undischarged BBS frontier P2 takes.  So the window endpoint, like P2, will
carry `hShi` as an input until the BBS realization lands.

## Endpoint statement shape (target)

Over a flow-solution sequence `(D, S, hS, hmet, hreg)` + the P2 input package
(`hequiv`, `hBprev`, `hShi`, `hswap`, the `(B_a)` caps, the lower bound) →
`∃ φ, StrictMono φ ∧ ∃ gInf : ℝ → SmoothRiemannianMetric, ∀ε>0 ∃k0 ∀k≥k0 ∀t∈Icc,
metricDerivNormSupOn K p (gSeq (φ k) t) (gInf t) gRef < ε`
(= `windowPreconv_of_perTime`'s conclusion).
