# NormalLiveConv

## 2026-07-18 framed dependency validation

No local source migration was needed: this module contains no raw fixed-base
chart or old exponential-radius occurrence.  After refreshing the framed Cage
and the `expRadiusGp`-based `NormalMetricConv` producer, both focused
verification and the exact module refresh are green.  Thus
`exists_live_diag`, `exists_slot_diag`, and `exists_diag_full` preserve the
same minimizing branches on the canonical framed metric-limit chain.

`MetricCompactBase.exists_b1_raw` has a complete source proof body but still
awaits the remaining Support/stage/metric framed validation.  The separately
named textbook B1 theorem and unconditional endpoints remain theorem-level
0%; rounded machinery estimates remain B1 95%, C4 87%, whole HCG 60%.

## 2026-07-16 prescribed live-slot diagonal branches

`MetricCompactnessInputs.exists_slot_diag` combines the finite slotwise metric
subsequence with `NormalRadiusProfile.exists_diagPair_at`. For each live slot
the stage radius is the supplied `q alpha` and the limit radius is exactly
`q alpha / 2`; the same common subsequence carries every `HasDiagPairConv`.

Focused verification passed. This producer introduces no new radius field.
Before it is attached to the support capstone, its independently selected
stage branch must be identified with or replaced by the minimizing branch used
by the readout. `StepB1RawInput` and textbook B1 remain theorem-level 0%.

## 2026-07-16 minimizing-branch alignment

`exists_slot_diag` now retains the canonical `NormalDiagFence` at every stage
alongside each `HasDiagPairConv`.  The higher producer `exists_diag_full`
accepts an eventual family of `HasLiveBrFull` witnesses plus an arbitrary
eventual payload `Q`, passes to one common shifted subsequence, and preserves:

- `Q` at every refined index;
- the normal-metric limit data;
- `HasLiveBrFull` at every refined index; and
- forward and exact-inverse convergence for the branch selected inside that
  same full minimizing witness.

The last item uses `HasDiagPairConv.congr_stage`; no branch selector, extra
radius field, or whole-cage containment was added.  Focused verification and
the targeted module refresh passed.

This closes the selected-branch/subsequence coherence seam, not the frozen
stage quantifier defect: `exists_diag_full` does not by itself replace a
stage-dependent pair threshold by one all-pairs threshold.  `StepB1RawInput`
and textbook B1 remain theorem-level **0%**; dedicated Step-B/B1 machinery is
about **95%**, Chapter 4 about **87%**, and whole-HCG compactness machinery
about **57%**.
