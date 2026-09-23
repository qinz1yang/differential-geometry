# C1 branch tube: review of the `realisation` clause (digest of the BI answer)

Owner supplied the review on 2026-09-23 (request BI). Corrections to the request: C1's original
review digest is `consult/I-caseone-skeleton-review-digest.md`, not `AN`; the mirror commit named
in BI predates the `# Batch 6` log entry (it is in `2ded05734` and later). Marks: **[V]** checked
against the Lean source by the lead; **[P]** the reviewer's or worker's paper computation;
**[OPEN]** outstanding proof.

## Verdicts

| Object | Review | Lead disposition |
|---|---|---|
| `exists_isSourceTrackedBranchTube` | FIX (weaken the interface), not FALSE | Fix (a) applied 2026-09-23 (lead edit on lease d: zero diagnostics, axiom audit; the C1 and A2 skeletons recheck with no error). |
| `cyclic` | OK | Unchanged. |

## What the review established

**[P] The increments.** In the model where the collar's vertical projection `w` is affine on each
triangle (`A = (0,0)`, `B = (1,0)`, `C = (x,1)`, `G` the centroid, `m_AC`, `m_BC` the edge midpoints),
the standard derived-neighbourhood boundary of the branch contains the two steps
`U = (A + m_AC + G)/3 → V = (A + G)/2` and `V' = (B + G)/2 → U' = (B + m_BC + G)/3` with
`w(V) - w(U) = (1 - 2x)/18` and `w(U') - w(V') = (2x - 1)/18`, so the boundary path folds or has a
flat step for every `x`, including `x = 1/2`; reparametrisation cannot repair the non-injective
projection. This confirms the worker's computation and withdraws the original review's "choose a
common subdivision" argument.

**[P] Not a universal impossibility.** `derived` requires neither `Lc ≤ R` nor `Lc.space` equal to
the branch, so `Lc` may include an isolated vertex `G`; for `x = 1/2` the new boundary ordinates in
that triangle are `1/8, 1/4, 3/8, 5/12, 1/2, 7/12, 5/8, 3/4, 7/8`, strictly increasing. This shows
the local obstruction can be circumvented but is not a global producer for arbitrary `L`, `ρ`; no
counterexample satisfying every hypothesis was given. The statement is therefore not refuted.

## Fix (a), recommended and adopted

Keep `derived` and `cyclic`, the continuous lift, `hbase` along the whole interval, the nonzero
same-side values and the initial alternating labels; restrict only the geometric identity to the
endpoints. New field text (replacing the fifth conjunct of `realisation` in
`LoopTheorem/ClosedBranchCaseOneTransport.lean`):

```lean
      (∀ (i : Fin 4) (t : unitInterval), t = 0 ∨ t = 1 →
        φ (r i, (t : ℝ)) = ι (⇑D (ρ (a i t, s i t)))) ∧
```

**[V] Consumers** (verified 2026-09-23 while applying the edit: the module and both skeletons recheck clean). The reviewer states that the transport proof only needs its two uses
changed to `hreal i 0 (Or.inl rfl)` and `hreal j 1 (Or.inr rfl)`, that `SourceRayTransport`, the
square-fixing and page-swap proofs are untouched, and that `ClosedBranchCaseOne`'s orientability
assembly, `ClosedBranchCaseOneTubeCarrier`, `ClosedBranchOrientability` and A2's
`not_branchPreimage_eq_of_isOrientable` keep their signatures. The lead will verify this while
applying the change (a real-module edit that rebuilds its cone; the C1 and A2 skeletons are
rechecked afterwards). Fix (b) (dropping `derived`) is rejected: at least `N.space ⊆ L.space` must
survive for the ambient orientation; the reviewer's alternative `ambientSubdivision` certificate is
recorded but not adopted.

## Obligations and warnings

- **[OPEN]** Fix (a) still requires producing the derived tube's marked closure and the endpoint
  matching; the change removes the mid-ray identity, it does not prove the leaf.
- Joint fixture: the capped Möbius model in `ℝP² × S¹` with end map `(01)(23)`, with the real
  `derived` witness and the new endpoint field, still UNTESTED.
- The endpoint version no longer guarantees that the middle of each ray lies in the surface image;
  no future surgery consumer may read it as a full trace.
