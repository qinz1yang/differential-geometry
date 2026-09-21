# Digest — eighth external review of `Skeleton/ControlledGraphNeighborhood.lean` (snapshot `165f8750`)

Marks: **[V]** checked by the lead against the Lean text. Only the two unfrozen leaves were
reviewed. Neither is FALSE; no complete counterexample was found. Both verdicts are about the
**supply interface**: data that the intended proof needs and that the leaf did not receive.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34VertexPreparation` | **FIX** → repaired | the thickened overlap clause is producible, also for a triangle of the graph; but the leaf must output one PL chart containing `h '' C''_v` and received no chart |
| `exists_section34PiercingPackage` | **FIX** → repaired | the closed-overlap field is closed; the other containments, sides and components need scales that the given `ε` does not certify |

## 1. Preparation
* **A triangle of the graph is no obstruction; the cut frame already separates the splitting
  disks.** With `D_ab = C_a ∩ C_b` and "`C_w` meets `D_e` ⇒ `w ⊆ e`": a point of `D_e ∩ D_d` puts both ends of
  `d` in `e`, so `d = e`. Different splitting disks are pairwise disjoint, including `ab, bc, ca`. No
  "the graph has no triangle" hypothesis is needed.
* The producer must localise the **whole lens**, not only the intersection circle:
  `C'_a ∩ C'_b ⊆ O_e` with the `O_e` pairwise disjoint (compactness of the disks + local finiteness),
  pierce inside; then `A, B` compact, `A ∩ B ⊆ O` open ⇒ `∃ r > 0, N_r(A) ∩ N_r(B) ⊆ O`; every vertex
  has finitely many incident edges, so take the finite minimum vertex by vertex and shrink with
  the other margins and the core stability scale. Order: whole-lens localisation → scale →
  approximation; no uniform positive scale over the graph. This yields exactly the
  `section34CellThickening` clause.
* **Missing input [V].** The leaf's only `Q`-hypothesis was `hQint`; its conclusion asks for a chart
  of the maximal atlas containing `h '' Cc w` with `C_v ⊆ C''_v`. A compact set lies in finitely many
  charts, not in one, and a single chart around a (possibly wild) ball is not available for free.
  The assembly had the chart — last field of `Section34CarrierControl` with `hQH` — and dropped it
  (`obtain ⟨-, hHsub, hHlf, -, hHcell, -⟩`). **Repair applied:** new hypothesis
  `hCchart : ∀ w, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, h '' src (.vertexBall w) ⊆ c.source`,
  supplied in the assembly from `hQint`, `hQH`, `hcarF` and the chart field. The whole `Q w` need not
  lie in the chart.

## 2. Package
* For the output family, `G'_w(C'_w) ⊆ section34CellThickening h C' ε w` from `Cp w ⊆ Cc w` and the
  output closeness; `section34OverlapConditions` then gives the closed-overlap field. Keeping it a
  field is right (the removal steps carry no closeness). No closed-ball thickening needed.
* **What was not closed [V]:** e.g. `G'_b(B_e) ⊆ Int G'_a(S_e)`, `G'_a(A_{e0}) ⊆ Int G'_b(C'_b)` and the
  component certificates of (7). The certified scale of the preparation protects only `Kcore`,
  which avoids the tubes (there is a strict margin between `Sn e` and every core); the margin
  clauses give `G_b x ∉ G_a(Cc a \ Int Sn)` but not `G_b x ∈ G_a(Cc a)`; none of the three exporters
  proves these conclusions. "A smaller sufficient scale exists for this source configuration" is
  not "the given `ε` is that scale".
* **Repair applied (the reviewer's cheaper option):** the leaf receives `h341 : Moise341` and no
  longer a given family (`hG`, `hGdist` deleted). Its proof chooses auxiliary scales `δ_w ≤ ε_w`,
  approximates chart-locally within them, perturbs into general position. Public `ε`, `hprep` and
  the conclusion (incl. closeness within `ε`) unchanged. The proved
  `Moise341.exists_section34VertexApproximation` stays as a lemma; the assembly no longer calls it.
  Alternative not taken: add the stability certificates for the tube sets to the preparation and
  prove their exporters.

**Closed by this round:** whole overlaps, cores, local finiteness in the target subspace; the five
frozen leaves were not reopened. **Fixture suggested:** periodic tetrahedral triangulation of `ℝ³`,
`𝒦' = 𝒦`, a non-identity affine shear, standard cut, the three edges of a triangle pierced in
pairwise disjoint disk neighbourhoods. **Reviewer's "biggest surprise":** reading "the producer
can choose the scale small" as "any given preparation's scale supports the rest".

**State after the repair (lead re-check, lease a):** 7 diagnostics, all `declaration uses 'sorry'`;
the five frozen leaves and the endpoint byte-identical; the two repaired leaves are frozen on the
strength of the review's own prescription plus the lead's verification — all seven leaves of the
controlled 35.1 skeleton are now frozen.
