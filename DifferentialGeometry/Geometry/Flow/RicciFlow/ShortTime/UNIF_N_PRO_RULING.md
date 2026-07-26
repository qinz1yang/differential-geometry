# GPT Pro ruling — black box (N) uniformization route (received 2026-07-22)

Consult prompt: `UNIF_N_PRO_PROMPT.md` (submitted user-side; Chrome plugin was
unavailable).  Ruling recorded verbatim below.  Planner digest:

- **Classification: design issue** — the identity-region guard between the
  Sobolev nonlinearity and the genuine Ricci–DeTurck operator lives in the
  wrong topology (pointwise `H^{a+2}` ball), which is what forces the
  qualitative interval shrinks (`d`, `d₂`, `d₂F`).
- **Route: R1τ** (hybrid; R1′ not literally, R1″ rejected, R2 parked): keep
  the per-datum engine; add a sibling second-order TAME/full-horizon lane
  with `H^{a+1}`-controlled admissibility; only then a NARROW class-uniform
  packet at orders `a, a+1, a+2` (no global cross-metric equivalence; do not
  transfer `Csym1/Csym2` — expose the norm-contraction bound instead).
- **First brick (decisive route test):** the second-order tame smooth-core
  difference estimate (`smoothRemainderDiff_tame_Ha2_Ha1_of_symm`-shaped),
  WITHOUT endpoint `H^{a+2}`-ball hypotheses.  Explicit stop signal if a
  pointwise `H^{a+2}` radius or an `‖U‖_{H^{a+2}}·‖U−V‖_{H^{a+2}}` product is
  unavoidable — that failure rules out R1τ at `A(n) = a+2`.
- Lemma frontier in dependency order: (1) generic `timeH1` √t-modulus;
  (2) the tame estimate (route test — IMPLEMENT ONLY THIS NEXT);
  (3) `H^{a+1}`-controlled scalar cutoff acting on `H^{a+2}`;
  (4) time-level tame Nemytskii forcing estimate in `timeL2 (tensorHs … a)`;
  (5) fixed-horizon representative sibling returning the input `T` exactly;
  (6) narrow class-uniform geometric packet; then instantiate `τ₀`.
- Hamilton–DeTurck pullback hides no extra shrink (its proof returns `T_DT`).

---

[Verbatim ruling follows.]

# Ruling
**Classification: design issue.** More precisely, the existing lane uses the wrong topology at the boundary where the globally defined Sobolev nonlinearity is identified with the genuine Ricci–DeTurck operator.
This is not a local proof-search failure, coercion problem, or typeclass problem. It is also not primarily a missing cross-metric lemma. The target statement remains mathematically reasonable after the approved upgrade from orders `≤ 3` to orders `≤ A(n)`.
**Route ruling: choose neither R1′ nor R1″ literally. Use a non-destructive hybrid, call it R1τ:**
> Keep the existing (g₀)-intrinsic maximal-regularity engine, but add a sibling **second-order tame/full-horizon lane** whose admissibility cutoff is controlled in (H^{a+1}), not by a pointwise (H^{a+2})-ball. Once that analytic lane returns the fixed-point horizon unchanged, add only the finite-order class-uniform comparison estimates needed to bound its constants from (gBase,\Lambda).

| Route | Ruling | Reason |
| --- | --- | --- |
| R1′ as stated | Do not proceed literally | Quantifying the old (d,d₂,d₂F) preserves the bad (H^{a+2})-identity guard and is likely to demand more uniform initial regularity than (A(n)=a+2). |
| R1″ | Reject | Fixing the Sobolev scale does not by itself remove the later (H^{a+2})-faithfulness shrink; it also duplicates the sorry-free engine. |
| R2 | Park | Valid long-term lane, but not the route for closing the last `sorryAx` on this branch. |
| R1τ | Choose | Reuses the fixed-point and maximal-regularity infrastructure, removes the qualitative post-processing horizons, and leaves the existing per-datum API intact. |

# Exact obstruction
The contraction theorem itself is already in an acceptable quantitative form. Once (C₁,C₂,D) are provided, `nemytskii_sol_const` returns an explicit positive horizon depending only on those constants and produces the forcing-space fixed point with a quantitative force-ball bound.
The loss occurs afterward because the current total nonlinearity is constructed using a radial retraction in the **top spatial scale (H^{a+2}_{g₀})**. Its theorem identifying the extended map with the genuine smooth Ricci–DeTurck remainder requires ‖T‖_{H^{a+2}_{g₀}} ≤ R₀.  That is an identity-region condition, not merely an estimate used by the contraction.
Consequently, the representative construction has to shrink the interval until the solution is known to be in that (H^{a+2})-ball. The first shrink uses qualitative (H^a)-continuity at zero; the final result then takes a minimum with further bootstrap horizons.
The later time-regularity horizon is not an unrelated technicality. `deTurckForcing_solCoeff_continuous_smallTimeBase` returns its `d` together with exactly the (H^{a+2})-realizability-ball condition, and the finite-order bootstrap subsequently inherits that same `d`.
Central diagnosis: the fixed point is quantitative, but faithfulness to the geometric PDE is guarded in a topology for which the available uniform initial class does not provide a usable pointwise-in-time modulus.  A uniform (H^{a+2}) modulus at (t=0) is especially suspect: at the natural input order the class controls the initial forcing in (H^a), while uniform continuity of the solution in (H^{a+2}) would generally see additional high-frequency information.  Quantifying the existing (d₂) can therefore force extra derivatives rather than merely more careful constant bookkeeping.

# Is cross-metric (H^s) comparison the right first brick?
No.  Necessary later, not first.  A full `H^s_{g₀} ≃ H^s_{gBase}` theorem would feed bounds into an engine that still returns `T₁ = min(T₀, d/2, d₂, d₂F)` — it does not resolve the decisive lifetime loss.  The first brick should test whether the second-order nonlinearity admits the correct tame estimate WITHOUT a pointwise (H^{a+2})-radius assumption.  If that fails, R1τ is dead and a large cross-metric layer would have been built for the wrong analytic API.  After the route test succeeds, the cross-metric layer is NARROW: integer-order, smooth-core, one-sided estimates at orders (a, a+1, a+2) only; a class-uniform (H^{a+1} → C⁰)/fibre-operator bound; a uniform tame constant; a uniform ‖N(0)‖_{H^a_{g₀}} bound.  Do not transfer `Csym1`/`Csym2` (symmetrization is already used through a norm contraction; expose that exact bound).

# Quantitative replacement for the qualitative (t=0) δ
Small generic lemma (`timeH1`): ‖u(t) − u(0)‖_{H^a} ≤ √t · ‖∂ₜu‖_{L²([0,T];H^a)} — an explicit ½-Hölder modulus replacing the naked `ContinuousWithinAt`.  Useful, but patching only this `d` is NOT the route.
Architectural replacement: use the cross-scale (H^{a+1}) representative (the branch already has the Lions–Magenes machinery: continuous (H^{a+1}) representative, every-time norm bounds from the (L²H^{a+2}) field and the (H¹H^a) carrier) to establish admissibility on the ENTIRE fixed-point interval, so the truncated and genuine equations agree without a later qualitative shrink.  The existing locally-Lipschitz theorem shows the lifetime pattern but its nonlinearity is first-order type (H^{a+1} → H^a); Ricci–DeTurck is genuinely (H^{a+2} → H^a) — use the cross-scale trace and stay-in-ball technology, not the headline theorem.  Best: change the decomposition so the representative accepts full-interval admissibility and returns the input horizon `T` exactly.

# The correct second-order replacement
For smooth symmetric (U,V) inside a fixed fibre-small or (H^{a+1})-admissible region:
‖N(U) − N(V)‖_{H^a} ≤ K·( (1 + max(‖U‖_{H^{a+1}}, ‖V‖_{H^{a+1}}))·‖U−V‖_{H^{a+2}} + max(‖U‖_{H^{a+2}}, ‖V‖_{H^{a+2}})·‖U−V‖_{H^{a+1}} ).
Sums instead of maxima fine.  An (H^{a+1})-ball or fibre-smallness assumption is allowed; endpoint (H^{a+2}) norms may appear LINEARLY as tame factors; it must NOT assume ‖U‖_{H^{a+2}}, ‖V‖_{H^{a+2}} ≤ R₂.  The time-integrated estimate closes in L^∞_t H^{a+1} ∩ L²_t H^{a+2} via ‖A·B‖_{L²_t} ≤ ‖A‖_{L^∞_t}‖B‖_{L²_t} in one orientation and reversed in the other; the cross-scale representative supplies L^∞H^{a+1}, maximal regularity supplies L²H^{a+2}.

# Small lemma frontier (dependency order)
1. Generic quantitative trace modulus (`timeH1`): ‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖ on `Icc 0 T` (time-restricted L² norms).
2. Second-order tame smooth-core estimate — DECISIVE ROUTE TEST: sibling of the ball-Lipschitz theorem, provisionally `smoothRemainderDiff_tame_Ha2_Ha1_of_symm`, for `deTurckSmoothRemainder`/`deTurckSmoothN`, with fibre-smallness and symmetry but WITHOUT endpoint (H^{a+2})-ball hypotheses.  FIRST substantial implementation step.
3. Lower-topology cutoff lifted to (H^{a+2}): U ↦ χ(‖ιU‖_{H^{a+1}})·U — maps into the prescribed (H^{a+1})-ball, identity on it, (H^{a+1})-Lipschitz, mixed (H^{a+2}/H^{a+1}) difference estimate.
4. Time-level tame Nemytskii estimate parallel to `nemytskiiMixedForcingMap_dist_le`, consuming L^∞H^{a+1} + L²H^{a+2} (+ difference) bounds, producing the contraction directly in `timeL2 (tensorHs … a)`.  No fake pointwise `LipschitzWith` for (H^{a+1} → H^a); the operator is second order.
5. Fixed-horizon representative: `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` — hypotheses contain full-interval admissibility; conclusion uses EXACTLY the supplied `T`.  Bootstrap restated against the lower-topology identity region.
6. Class-uniform geometric packet (only after 2–5 work per datum): smooth-core norm comparison at (a,a+1,a+2); uniform lower-topology admissibility radius; uniform tame constant; uniform ‖N(0)‖_{H^a} bound.  Then instantiate the explicit fixed-point formula; its time is `τ₀`.

# Lean proof strategy (as given)
(1) Do not modify the per-datum theorem; siblings only.  (2) In `SobolevNonlinearityExistence.lean`, at the point where `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm` collapses endpoint high-order terms into the ball constant `R`, keep them in the conclusion.  (3) Lift to spectral (H^a,H^{a+1},H^{a+2}) norms as the existing theorem does; per-datum `Classical.choose` constants acceptable at this stage.  (4) Define the (H^{a+1})-controlled scalar cutoff on (H^{a+2}); identity on the admissible ball ⟹ evaluates to the genuine remainder.  (5) Sibling forcing map reusing L²H^{a+2} maximal regularity + (H^{a+1}) representative + force-ball fixed point; replace only the pointwise globally-Lipschitz estimate by the time-integrated tame estimate.  (6) Forcing radius first (Duhamel fields in the (H^{a+1}) region), then `T` from the self-map estimate with √T·‖N(0)‖; fixed point genuine on the full interval.  (7) Bootstrap assumes full-interval admissibility; drop the small-time (H^{a+2})-ball recovery.  (8) Then the narrow uniform packet bounds all inputs by (gBase, Λ, A(n)).  (9) The Hamilton–DeTurck pullback returns `T_DT` itself — no hidden shrink.

# What to implement next
ONLY the second-order tame smooth-core difference estimate (item 2).  Do not yet: edit `ricci_flow_unif_existence`; build the cross-metric layer; modify the fixed-point theorem; alter the representative theorem; add jets beyond `A(n)`.

# Stop signal
Stop immediately if the estimate cannot close without a pointwise endpoint bound ‖U‖_{H^{a+2}}, ‖V‖_{H^{a+2}} ≤ R₂ — specifically if an unavoidable term has the form C(R₂)·‖U−V‖_{H^{a+2}} (with R₂ a pointwise H^{a+2} supremum) or ‖U‖_{H^{a+2}}·‖U−V‖_{H^{a+2}}.  Acceptable: ‖U‖_{H^{a+2}}·‖U−V‖_{H^{a+1}}.  Do not hide a failed tame estimate by adding jets, reintroducing `d₂`, starting the cross-metric layer, or a new `Classical.choose`.  Failure at that point rules out R1τ at `A(n)=a+2` and means the formulation must be reconsidered.
