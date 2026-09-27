# Poincaré endgame skeleton: first external statement review and lead due diligence

Date: 2026-09-25. Source: the owner's external-review answer to the lead's audit prompt (the
statements of `Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean` and
`Surgery/Topology/CanonicalNeighborhoodInduction.lean` as archived at mirror commit
`dd37b1d5a`), together with the reports of the five Opus worker lanes dispatched the same
afternoon (point picking, backward curvature control, uniform-κ threshold, standard-cap inputs,
noncollapsing transport).

**Result: `CanonicalNeighborhoodsThroughSurgery` and `CanonicalNeighborhoodContinuation` were FALSE
as stated; `NoncollapsingThroughSurgery` and `CanonicalNeighborhoodContinuation` used a
noncollapsing hypothesis too weak for the crossing case; `PinchingThroughSurgery` is a corollary of
the tree. The two real modules were restated (age-restricted witness clause, cap window and order
bounds, history-wide parabolic noncollapsing); the assembly was reproved and re-audited.**

## 1. Verdicts

| Item | Claim | Lead check |
|---|---|---|
| 1 pinching sign | the prompt read `Rm ≥ Phi(R)` | Prompt error only: `curvatureOperatorLowerBoundAt … (Phi R)` is `0 ≤ Rm(v) + Phi(R)·…`, and `AdmissiblePinchingFunction.pos` gives `Phi > 0`; the Lean definition is the usual `Rm ≥ −Phi(R)`. |
| 2 C1 is a corollary | of `exists_admissiblePinchingFunction_for_identified_incomingSlabs` | Verified by compilation: `Surgery/Topology/PinchingThroughSurgery.lean`, `pinchingThroughSurgery`, bounds `1`, `phi` independent of `B`. |
| 3 C2 binder order | κ before `qcan` is Perelman II 5.2 / KL 79.12 | Accepted; the proof must supply an initial good interval from the fixed initial metric. Recorded in `HANDOFF_C.md`. |
| 6 debit per cut | zero-cut events pay nothing | `GeometricCutoffRecord.no_cuts_discard` (`GeometricCutoff.lean:242`) excludes identity events; the finiteness argument is inside the proved horizon-invariants theorem, not an open obligation. |
| 8 record schedule | event-time bounds are not Perelman's schedule | Accepted as a bridging obligation for S; the collaborator's factory already closes the class under event-local bounds. |
| 9 cap admissibility | `modelAccuracy` alone is too little | Accepted and repaired: C outputs `Dcap`, `mcap`; the class requires `Dcap ≤ p₀.modelRadius`, `mcap ≤ p₀.modelOrder`; S receives them. |
| 11, 12 two-stage picking | use nested windows; make `Q(t − T) → 0` | Accepted. Lane P's `exists_noncanonical_point_with_canonical_above_double` yields both: the second bad point lies in the first window, so `Q₂ < 2Q₁`. |
| 13 large backward boxes | not from derivative bounds alone | Confirmed by Lane B: only the fixed-scale box (`R ≤ 8Q` on radius `c(C2)/√(2Q)`, time `c(C2)/(2Q)`) follows; the large-`A` control is inside the tree's blow-up machinery (Lane U). |
| 14 in-slab noncollapsing does not cross events | flat collapsing torus cut into short slabs | Counterexample verified against the old `NoncollapsedBefore` (windows inside the slab). Repaired: `RetainedCoreHistory.NoncollapsedBefore` is stated with `ObservedHistory.isParabolicallyRmControlledBall` (traces through the retained cores), and the terminal slab is attached by `extendHorizon` with `IncomingSlab.closedPrefix`. |
| 17 scathed case | needs quantitative capture and a non-circular cap stability | Accepted; two separate bricks in `HANDOFF_C.md`. |
| 18 exact constants | need strict margins | Accepted; Lane U produces the witness with the same `C` as `exists_uniform_canonical_constants_with_cap_neck_charts`, which is what the induction needs. |
| 19, 20 S reorder | more than `q0`; no automatic uncoupling | Accepted; S stays open. |

## 2. The FALSE statement found by Lane D

`CanonicalWitness` (`Perelman/CanonicalNeighborhood/FiniteHornGeometry.lean:272`) puts a
`StrongNeck` under both the neck and the cap alternatives (`LocalCap` builds its tube from strong
necks), and `StrongNeck.sub_inv_scalar_mem_carrier` (`Surgery/Topology/StandardCapCanonicalTransport.lean`)
shows that a strong neck at `(y, t)` needs `t − R(t, y)⁻¹` inside the flow's time domain. For a
slab `closedOpen a s` a point of a freshly inserted cap (`R ≈ h⁻²`, `t − a ≪ h²`) therefore has no
witness unless its component is compact positive or round
(`PartialStandardSolution.isEmpty_canonicalWitness_of_time_mul_scalar_lt`,
`CanonicalWitness.exists_backward_window_or_isCompact_connectedComponent`). The old clause "every
point of the singular slab with `qcan < R` has a witness" was therefore false for every class
history with a cut event, and so was C3 at `t₀ = a`. Kleiner–Lott's ε-cap needs only a spatial
ε-neck; the tree's cap is stronger.

Repair adopted: the witness clause is required only where `τmin ≤ R(t, x) · (t − a)`, with `τmin`
a further output of C (after `ε`), and S receives `τmin`. The derivative clause `|∂ₜ⁻R| ≤ Ctime R²`
stays unrestricted above `qcan` (in the fresh layer it comes from the standard-solution comparison,
which consumes exactly this clause). The collaborator's factory hypothesis has the old unrestricted
shape and must be weakened the same way when the S chain is ported.

## 3. What the five lanes established (all compiled read-only; audited: 21 declarations, one
unused instance removed)

* Lane P: scalar and `|Rm|` bounded on `Icc a b` of a slab; 2Q point picking with the canonical
  clause on `[T, t']`; `|Rm| ≤ C(Phi) · max R 1` from pinching.
* Lane B: fixed-scale backward control from `gradient` and `time_derivative`, window inside the
  slab (`a < t' − 2c/Q`), scalar and `|Rm|` versions.
* Lane U: `abstract_model_theorem` (`HighCurvatureModelBounds.lean:246`) is already uniform in
  `(ε, κ, σ, Phi)`; point picking and bounded curvature at bounded distance are internal.
  `exists_uniform_canonical_threshold_of_spatially_noncollapsed` gives the witness with the
  `ε`-only constant `C` from `Q₀(ε, κ, ρ, Phi) ≤ R`, a backward window `θ/R` inside the slab,
  pinching there, and SPATIAL κ-noncollapsing at all times of the window. The bridge from the
  parabolic (history) noncollapsing to the spatial one is the open glue.
* Lane D: the standard solution has no witness at small normalized age (see §2); late-time
  witnesses follow from `HighCurvatureModels.lean:117` once its olean exists; witness transport
  under the collaborator's closeness (spatial `Cᵖ`, no time jets) is absent.
* Lane N: forward volume transfer under `|Rm| ≤ ρ⁻²` (`ForwardTransfer.lean`, radius `L·ρ`,
  `L ≥ exp(n²θ)`); the retained-core transfer at scales inside the previous slab is superseded by
  the history-wide predicate and was not wired.

## 4. Open after this round

The crossing case of C3 (backward neighbourhood through the retained core into earlier slabs)
needs a blow-up on the common flow of a history parabolic ball, which the compact-manifold
machinery does not cover; the scathed case needs quantitative capture, standard-solution
witnesses at positive age, and witness transport with time jets. The parabolic-to-spatial bridge
under the derivative estimate is the next brick.
