# Review H17 (single statement: `StrongNecksOfCutoffClass`, the A-lite leaf), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-q` @ 149de65b1 (`DESIGN_STRONG_INTERFACE.md` §4), not compiled.
Overall: **FIX, not FALSE; the reviewer leans to TRUE and keeps A-lite.** §4.4's "the X-core applies as is" and
"S2e is covered by the curvature bounds" are NOT acceptable as written.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| no extra Crossing floors | OK | The source's positivity / ≥1 conditions remain; only extra quantitative floors are absent. Enlarge `C1, C2, Ctime, Cgrad` to the needed floors, enlarge `τmin` (only weakens the age-gated `CanonicalBefore` hypothesis), take `qh ≥ max qcan q₀`; all before `p₀`, allowed by the quantifiers. |
| full-slab class instead of the "before t₀" induction | inputs OK; copying the proof FIX | The full-slab class restricts to any `Before t₀`, so no "first bad time" is needed for the inputs. BUT "no strong witness" does not give "no spatial witness": SX's spatial conclusion cannot be reused; one must call the genuine X-core that outputs a SPACETIME witness on the common flow. B5 explicitly needs curvature bounds along the existing traces of the WHOLE ball, not automatic from the class. |
| caps of standard age `σ ∈ (θcap, 1)` | not a direct counterexample | Never conflate the two ages. Choose `θcap` with a strict margin so that after transport `R(t − T) > 1` still holds, so the whole window does not cross its own birth time; `R(t − T) ≳ 1` is not enough. Other events still need tracing. The full/truncated dichotomy of the standard solution has a genuine basis. |
| arbitrarily short slab chains | not a direct counterexample | `IncomingBackwardNeck.crossing` already allows crossing many events; no uniform slab length needed. But use the SAME common flow after exact identification and estimate the error ONCE; do not splice approximate strong necks slab by slab with accumulated loss. The record's certified depth is still only the nominal `r²`. |
| far-cylinder points right after gluing | H17 not refuted; supply must be fixed | A lone standard solution's short-age spatial neck may lack a full backward window. In the history the incoming neck completes it; if the chosen whole tube touches newly glued material it cannot be traced, and one must prove a cap witness can be chosen instead. `∃ W` with late `C1h, C2h` permits this choice but does not prove it. |
| A-lite loses the previous slab's strong clause? | not at the interface | A-lite can run the event induction INSIDE the leaf: produce the previous slabs' strong clause first, then the current slab, then the terminal slab. Dropping the strong conjunct from the CN interface does not forbid internal induction; what is saved is the interface edit, not the production proofs. |

**The real acceptance gap is S2e.** From the record's coverage of `[T − r², T]` and a gap `≤ Cδr²`, bounded
curvature + time-Lipschitz do NOT give existence of the earlier history segment. First prove that the WHOLE
tube survives on the completing interval (or switch to the cap-witness branch), then the higher-order comparison
the strong neck needs. Also the `O(δ)` constant must be uniform over the LATER-quantified `p₀`: the class only
gives `p₀.recenterConstant·δbound ≤ 1/2`, which is not a small error tending to zero.

**Definite auxiliary error:** S1′ as documented allows `t = 0` yet demands a truncated depth in `(0, 1]`; at `t = 0`
the depth `tR = 0`, and far cylinder regions cannot be covered by a fixed-constant cap witness. Change to `t > 0`
or allow zero depth. (Does not refute H17: its conclusion quantifies only over open-slab times.)

Decision (lead): keep A-lite. Leaf-closure gates: (1) whole-tube survival on the completing interval + higher-order
control (S2e rewritten: survival-or-cap-witness dichotomy, `O(δ)` uniform in `p₀`); (2) the X-core's SPACETIME
witness on the common flow carried back (never SX's spatial form; B5's whole-ball trace curvature bounds supplied);
(3) `θcap` with strict margin `R(t − T) > 1`; (4) single common flow + one error estimate across events;
(5) S1′ with `t > 0` (or zero depth allowed). SP1/SP2 told; the leaf statement itself stands.
