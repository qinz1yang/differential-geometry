# Time-dependent local Nemytskii layer

## State — 2026-07-19

`TimeLocalNemytskii.lean` adds the measure-theoretic input needed by a
genuinely time-dependent nonlinear forcing term.

The central predicate is `TimeNemyMeas`.  It requires strong measurability of
the actual composite

```text
t ↦ N(t, aeSetLift f t)
```

for every almost-everywhere state-valued `L²` field on every slab below a
fixed horizon.  Separate measurability of `t ↦ N(t,u)` for each fixed `u` is
not used: without an additional Carathéodory theorem it would not justify this
composition.  `timeNemy_of_cont` proves that joint continuity in `(t,u)` is a
clean sufficient producer for `TimeNemyMeas`.

The remaining public API is:

- `memLp_time_tame`: compositional measurability, an a.e. uniform zero bound,
  and an a.e. uniform three-arm estimate imply `L²` integrability;
- `timeNemyTame`: the corresponding time-`L²` field;
- `timeNemyTame_ae`: its pointwise representative identity.

The growth proof uses only the lower-state bound and the three-arm estimate.
No extension of `N` outside its genuine state set is introduced.

## Verification and honest accounting

This lane was required to be source-only while another named Lean build was
active.  The file has therefore received static source review but no focused
Lean check in this lane.  Verified theorem completion is 0% until that check
passes; source implementation of this isolated measure-theoretic layer is
complete pending elaboration.

**2026-07-25 REAL BUILD VERDICT: GREEN.** Authoritative
`lake build +…TimeLocalNemytskii` passed (olean produced); the public API
(`TimeNemyMeas`, `timeNemy_of_cont`, `memLp_time_tame`, `timeNemyTame`,
`timeNemyTame_ae`) is now verified and consumable.

No `sorry`, `admit`, axiom, opaque replacement, foundational instance, or new
notation is introduced.
