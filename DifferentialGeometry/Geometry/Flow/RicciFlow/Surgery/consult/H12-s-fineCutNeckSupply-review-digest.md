# Review H12 (single statement: T4 `FineCutNeckSupply`, the S leaf's new supply), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-l` @ 8383afb2c (`DESIGN_B13.md` §0, §2 T4, §4), not compiled.
Overall: **T4 itself is undetermined; the proposed proof route is FIX, not FALSE.** F6's quantifier obstacle
is real; "old caps are uncovered" is not a counterexample.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (1) T4 vs old caps | unproved, not refuted | For one history the final slab length `Δ = s − a > 0` and B12 already gives fine necks once `Qc·Δ ≥ 2θ`; a single old cap producing a horn does not contradict arbitrary-accuracy eventual self-improvement. A counterexample needs a FAMILY of histories uniformly meeting the cap requirements with `R_L(x)/max(Λ/r², qcan, 1) → ∞` never being an `εc`-neck. Cap age in `(Θ, 1]` marks a proof gap only. In the actual signature `Kfine` precedes `p₀`: a per-`p₀` version is not enough. |
| (2) F* constant order | F6 correct; no automatic fix | `∀εc ∃Rrad(εc)` cannot be assembled: one needs `D ≥ Rrad(εcut)` AND the factory's requirement on `εcut` simultaneously; e.g. `R(ε) = ε⁻²` with `ε ≤ D⁻¹` has no solution on `(0, 1/2)`; "enlarge `D`, then shrink the accuracy" is not a proof; the dependence of the accuracy on order/accuracy parameters must be handled too, not only `Dbig`. |
| (3) fixed-`p₀` X-core | not supplied by B3e | B3e outputs `Rrad, ζ₀` after the input `A`, with no uniform control over all `A`; the radii growing with `n` come from negating that lemma's own existential and cannot be transplanted into a fixed-`p₀` diagonal process. This refutes the current call route, not T4's truth. |
| (4) Perelman II §4.3 | usable only as a STRENGTHENED route | §4.1 requires neck alternatives with a full backward parabolic window (surgeries allowed far away); §4.2's cone exclusion and §4.3's repeated backward extension use it. Our purely spatial witnesses plus scalar derivative bounds do not give this cross-event window, so §4.3 cannot bypass the old-cap problem. |
| §0 `hlong` | reduction correct; "false" argument fails | Nonempty case: `Qc = Qθ` does give a uniform positive time lower bound, but "the model dies after ≈ h²" and "the class bounds only the scale from above" do not produce actual histories from the same `g₀` with `Δₙ → 0`; a failure at one scale still needs `Qc ≥ Qθ` checked. Verdict: `hlong` is NOT AVAILABLE as a supplied input, not refuted; `uniformDebitSurgeryStepStrong_of_long_slabs` stays a correct conditional reduction. |
| gap | missing hypothesis | The birth-scale lemma (F4) needs `p₀.recenterConstant * δbound ≤ 1/2`; T4 as written lacks it and `recenterConstant` is not uniformly bounded above (cannot be obtained from `δ₀` alone). Lead's note: `InCutoffClass` (`CanonicalNeighborhoodInduction.lean:165`) already carries this conjunct; T4 must quantify over the class, or add it explicitly. |

Two-layer repair (reviewer): (a) immediate weakening from B12: `Qc ≥ K_{εc}·max{Λ/r², qcan, 1, (s − a)⁻¹} ⇒ P.FineCutNecks εc Qc`
(cutting scale depends on the slab length: does NOT restore S's uniform debit); (b) keeping F*: strengthen the CLASS
condition — neck alternatives with a uniform, cross-event backward parabolic window, supplied independently for
late-age caps (not only witnesses gated by the slab age).

Decision (lead): S's supply is a genuine design fork (interface strengthening (b) vs. a fixed-parameter X-core vs.
reordering F* with a solvable `Dbig/εcut` dependence). A dedicated design lane (DESIGN_S_SUPPLY) will lay out the
exact statements and costs of each option for C3/C4 before any T3/T4 proof work; T5 (assembly from the
`FineCutNeckSupply` interface) and T1 (obstruction) proceed as interface-level bricks.
