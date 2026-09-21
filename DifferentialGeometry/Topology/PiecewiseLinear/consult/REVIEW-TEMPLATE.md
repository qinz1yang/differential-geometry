# Standing instructions for an external statement review

*You are asked to review the **leaf statements** of one Lean 4 skeleton file. Answer in English or
Chinese. You cannot compile; nobody asks you to.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**. Paths are
relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. The file to review is named in the
message that sent you here (a file under `Skeleton/`). Read also `Skeleton/README.md` (what a
skeleton is), `FREE_INPUTS.md` (where the chain sits) and whatever the skeleton's module
docstring points to. Mathematical background: Moise, *Geometric Topology in Dimensions 2 and 3*;
earlier answers are digested in `consult/*-answer-digest.md`.

**What a skeleton is.** Every open obligation of a chain is stated as `theorem leaf … := by sorry`;
the assembly down to the named endpoint is *proved* from the leaves and compiles. So the
interfaces already fit. What is **not** known is whether each leaf is true, non-vacuous and
provable by the lane that owns it. That is your job.

**For every leaf (`sorry`), in the order of the file:**
1. **Restate it in ordinary mathematics** (two or three lines), naming the objects.
2. **True or false?** Try to refute it first. Take every set parameter to its extremes (empty, the
   image itself, the whole space, a lower-dimensional set); every tolerance very large and very
   small, and adjacent stages of any sequence; every injectivity hypothesis at the end points and
   at each junction of a concatenation (a `Path x x` is never injective); every local finiteness
   statement against an increasing family and against the wrong ambient space; every `frontier`
   of a ball of dimension below the ambient one (it is the whole ball — the intrinsic boundary is
   `r '' stdSimplexBoundary d`). If false, give the counterexample and the repaired statement.
3. **Jointly satisfiable?** Exhibit ONE non-degenerate object on which all hypotheses hold at once
   (not the empty set, not `n = 0`, not the identity specialisation of the hypotheses). If none
   exists the leaf is vacuous — say so.
4. **Dischargeable?** For each hypothesis name who supplies it in the intended use (a proved
   theorem of the tree, another leaf, or the consumer). A hypothesis nobody can supply in the
   intended use is a defect even if the leaf is true.
5. **Right size?** Say if the leaf is really several theorems, or if it hides the whole difficulty
   of the endpoint behind a restatement, or if a hypothesis is redundant (derivable).
6. **How would you prove it**, in five lines, and which step is the expensive one.

**Then, for the file as a whole:** is any obligation *missing* — something the assembly should
need but does not, because a leaf is accidentally too strong? Are two leaves secretly the same
theorem? What is the single most likely place for a surprise?

**Output format.** A table `leaf | verdict (OK / FIX / FALSE / VACUOUS / UNDISCHARGEABLE) | one-line
reason`, then the details only for the leaves that are not OK, each with the repaired Lean-facing
statement. If a claim of *ours* in the module docstring is wrong, say so first and plainly.
