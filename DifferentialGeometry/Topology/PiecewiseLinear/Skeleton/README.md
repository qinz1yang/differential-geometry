# Skeleton — sorry-first feasibility files (owner-authorised transient frontier, 2026-09-20)

**Purpose.** Validate that a whole chain fits together *before* anyone proves its hard leaves.
A skeleton file states every open leaf as `theorem leaf … := by sorry` and **proves the assembly
for real** from those leaves, down to the named endpoint (`DescentStepOrientableStatement`,
`GeneralPositionInDoubleBufferedStatement`, `Moise352Open 3`, …). If the assembly does not
compile, the interfaces do not fit — found in an hour, not after a week of proving.

**Why this is allowed.** `AGENTS.md` forbids `sorry` "unless the owner … explicitly authorizes a
transient proof frontier". The owner authorised exactly this on 2026-09-20. The authorisation is
confined to this directory.

**Rules.**
1. Skeleton files live only in `Skeleton/`. They are **never** imported by the root aggregate or
   by any file outside `Skeleton/`. One file per chain (leaves and assembly together), because the
   focused checker keeps no object for a module with diagnostics.
2. A skeleton "passes" when the focused check reports **no diagnostic other than**
   `declaration uses 'sorry'`. Each `sorry` is a leaf; nothing else may be sorried — in
   particular no `sorry` inside an assembly proof.
3. **Mathematical review happens on the leaf statements, before any leaf is proved**: truth,
   joint satisfiability on one non-degenerate tuple, extreme values of every set/tolerance
   parameter, end points and junctions of every injectivity hypothesis, and the producer of every
   hypothesis. Leaves may be sent to external consultation as a list.
4. A leaf statement is **frozen** once reviewed. Whoever proves it proves *that* statement, in a
   real file outside `Skeleton/`, with the usual focused check, audit and lint; then the skeleton
   replaces the `sorry` by the real theorem. If a leaf turns out false or too weak, the skeleton
   is changed first and the assembly re-checked, then the proof continues.
5. `FREE_INPUTS.md` stays the ledger; for a chain with a skeleton its open leaves are exactly the
   `sorry`s of that file (`grep -c "sorry" Skeleton/<Chain>.lean`).
6. No declaration docstrings or comments, as everywhere; the module docstring lists the leaves
   with one line each (what it says, which lane owns it, reviewed or not).

7. **A skeleton cannot be imported by anything, not even by another skeleton** (found 2026-09-21):
   the focused checker only offers a module to importers when its receipt has zero diagnostics,
   and every skeleton has `sorry` warnings. Vocabulary shared by two skeletons (predicates,
   index types, proved exporters) therefore lives in a *real* module with no `sorry`
   (e.g. `Section34Frame.lean`, `LoopTheorem/ClosedBranchCaseOneTransport.lean`), imported by
   both. When one skeleton's endpoint is another skeleton's leaf, the two statements are kept
   textually identical and compared by diff, not by import.

8. **External verdicts are evidence, not rulings** (owner, 2026-09-21). Before a leaf is restated
   on a FALSE verdict, the counterexample is checked clause by clause against the actual Lean
   hypotheses, and the digest records "counterexample verified by <who>" or "not verified". A
   proposed repair is tested against the shared fixture and against the earlier counterexamples
   before it is adopted; a repair that adds a universal quantifier is suspect (one such repair was
   withdrawn by the reviewer a round later). An OK verdict freezes the *statement*: whoever proves
   the leaf first tries to refute it and stops if it looks false. Claims about the book or the
   tree are checked against the source before they change `FREE_INPUTS.md`.
