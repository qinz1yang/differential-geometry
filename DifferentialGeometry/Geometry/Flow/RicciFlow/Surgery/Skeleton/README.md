# Skeleton: sorry-first feasibility files (owner-authorised transient frontier, 2026-09-25)

**Purpose.** Validate that a whole chain fits together before anyone proves its hard leaves. A
skeleton file states every open leaf as `theorem leaf … := by sorry` and proves the assembly for
real from those leaves, down to the named endpoint (`smoothPoincareConjecture`). If the assembly does
not compile, the interfaces do not fit.

**Why this is allowed.** `AGENTS.md` forbids `sorry` unless the owner explicitly authorizes a
transient proof frontier. The owner authorised exactly this on 2026-09-25 for this directory.

**Rules.**
1. Skeleton files live only in `Skeleton/`. They are never imported by the root aggregate or by any
   file outside `Skeleton/`. One file per chain.
2. A skeleton passes when `lake build` of the module reports no diagnostic other than
   `declaration uses 'sorry'`. Each `sorry` is a leaf; nothing else may be sorried, in particular no
   `sorry` inside an assembly proof.
3. The leaves of this chain are `def … : Prop` in the two real modules
   `Topology/CanonicalNeighborhoodsThroughSurgery.lean` and
   `Topology/CanonicalNeighborhoodInduction.lean`; the skeleton only asserts them. Mathematical
   review happens on those definitions before any leaf is proved: truth, joint satisfiability on one
   non-degenerate history with a cut event and a singular slab, extremes of every constant and time
   parameter, and the producer of every hypothesis. Reviews and their due diligence are recorded in
   `../consult/`.
4. A leaf statement is frozen once reviewed. Whoever proves it proves that statement, in a real
   module next to the induction module, with the module build, the axiom closure and the thirteen
   standard linters; then the skeleton replaces the `sorry` by the real theorem and the root
   aggregate registers the module. If a leaf turns out false or too weak, the two real modules are
   changed first and the assembly re-checked, then the proof continues.
5. `../FREE_INPUTS.md` stays the ledger; the open leaves of this chain are exactly the `sorry`s of
   `PoincareEndgame.lean`.
6. No comments, docstrings or file headers in Lean source (this checkout's `AGENTS.md`); the leaf
   descriptions live in `../FREE_INPUTS.md` and the `HANDOFF_*.md` files here.
7. A skeleton cannot be imported by anything, not even by another skeleton. Shared vocabulary lives in
   the real modules.
8. External verdicts are evidence, not rulings. Before a leaf is restated on a FALSE verdict, the
   counterexample is checked clause by clause against the actual Lean hypotheses and the digest
   records what was verified. Worker lanes that find a target false report the counterexample and
   stop; that counts as success.
