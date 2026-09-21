# Digest — sixth external review of `Skeleton/ControlledGraphNeighborhood.lean` (snapshot `be5c8adb`)

Marks: **[V]** checked by the lead; **[–]** not independently verified.
Docstring corrections: "what is missing is exactly degree" is wrong — **the quantitative leaf is
false as stated; restated as the existence of a small enough scale it is provable from
connectedness and invariance of domain.** And the "no PL filling disk" clause of
`Section34OuterTorus` is a *consequence* of spine + buffer, not an independent smallness criterion;
when `h '' rim` is not PL it may even be vacuous.

| Leaf | Verdict | Reason |
|---|---|---|
| `image_subset_of_dist_lt_of_isPLCellOn` | **FALSE [V]** | under an arbitrary compatible metric, small distance does not put points in the same locally connected region |
| `exists_section34CutFrame` | **OK** | take a regular torus of the source rim, carry it by `h` and the carrier chart, then refine and shrink `Q` jointly; the no-filling-disk clause is derivable |
| `exists_section34VertexPreparation` | **FIX** | protects the vertices only; no interior cover of the *whole graph* with its stability scale |
| `exists_section34PiercingPackage` | **FALSE [–]** | a legal preparation may pierce along a detour and miss a segment of the original graph |
| `exists_section34ProtectedCircleRemovalStep` | **OK — freeze** | relative PL ball/annulus replacement inside the fixed tube; embedding of all of `Cc` is in the output; markers and outer boundaries kept off the support |
| `exists_section34DeletedBalls` | **FALSE [–]** | once closeness is forgotten the per-ball membership is lost; non-adjacent balls may intersect |
| `exists_section34EdgeMatching` | **FIX** | should *receive* `hDnbhd` from the deletion leaf instead of re-producing rim containment on fixed images |

## 1. Interior stability
**Counterexample [V]:** `M₁ = ℝ³`, `S = [−1,1]³`, `Kc = {0}`, `M₂ = ℝ³ × {0,1}` with
`d((x,i),(y,j)) = ‖x−y‖ + ¼|i−j|`, `F x = (x,0)`, `G x = (x,1)`, `δ = ½`: both embeddings, `hclose`
(`¼ < ½`), `hfar` (`½ ≤ 1`), yet `F 0 ∉ G '' S`. The leaf has no connectedness or chart-scale
hypothesis (nor the `IsCompact Kc` its docstring mentions). **Restate as an existence of scale:**
`theorem exists_dist_lt_image_interior_stable_of_isPLCellOn (hS : IsPLCellOn 3 S B) (hFc : ContinuousOn F S) (hFi : InjOn F S) (hK : IsCompact Kc) (hKS : Kc ⊆ S \ B) : ∃ δ > 0, ∀ G, IsPLHomeomorphInto 3 G S → (∀ z ∈ S, dist (F z) (G z) < δ) → F '' Kc ⊆ interior (G '' S)`.
Proof: finitely many *connected* open `V_i ⋐ F(Int S)` covering `F(Kc)` with centres `F xᵢ`; choose `δ`
with `G xᵢ ∈ V_i` and `G(B) ∩ V_i = ∅`; by the boundary API
`M₂ \ G(B) = Int G(S) ⊔ (M₂ \ G(S))`, and the connected `V_i` contains the interior point `G xᵢ`. **No
degree, no connected metric balls.** The same local proof works for compact interior subsets of a
solid torus (needs only a local ball cover / restriction lemma).

## 2. Preparation → package: the whole graph
The preparation has `simplexBody 𝒦' w.1 ⊆ interior (Cp w)` only, not `Γ ⊆ ⋃_w Int C'_w`.
Counterexample [–]: reroute one connecting corridor around an interior point `q` of an original
edge (each `Cp w` = a small vertex ball + finitely many thin arms piercing the original splitting
disks in the standard way but joined along a detour): all circles, annuli, tubes, markers and
strict separations hold, yet `dist (q, ⋃ C'_w) > r > 0`; with a non-identity affine shear `h`, `G = h`
and all `ε` below half the image-side gaps, every `ε`-close output misses `h q`, violating the
package's neighbourhood clause. **Repair:** the preparation outputs
`∃ Kcore, (∀ w, IsCompact (Kcore w) ∧ Kcore w ⊆ interior (Cp w)) ∧ graphSkeletonSpace 𝒦 ⊆ ⋃ w, Kcore w`,
and `ε w` is below the scale the stability theorem gives for `Kcore w`. Source geometry first,
stability scale second, approximation last (digest T's timeline; p. 249 uses a neighbourhood of
the whole graph).

## 3. Deleted balls: the leaf is false, the deletion formula is not
* **Per-ball marker [–]:** periodic standard piercing configuration, `h = L` a non-identity affine
  shear, `G_w x = L (x + a)` with `a` a large period, `Q` large balls containing both: all `hpack`
  clauses hold with `cnt = 1`, but the literal deletion gives translated `D_w` not containing `h w`.
  The assembly *drops* the package's closeness before asking the deletion leaf for the per-ball
  marker, so `section34Marker_of_dist_lt` cannot be invoked there.
* **Extra intersections [–]:** give two non-adjacent `Cp` thin fingers meeting outside all tubes;
  `Disjoint (Cp w) (Cp w') → …` says nothing about this already-intersecting pair; `hDadj` fails.
* **Keep the literal formula, isolate a single-cap lemma:** for PL 3-balls `P, Q` whose boundaries
  meet in exactly one normal intersection circle, `∂Q ∩ P` is a proper PL disk and cutting `P` along
  it gives two balls (PL Schoenflies; no need to redo §35). Global sufficient contract, with
  `P_w = G_w(C'_w)`, `L_e = P_u ∩ P_v`: non-adjacent `P_w` pairwise disjoint; closed overlaps `L_e` of
  different edges pairwise disjoint; each adjacent boundary intersection one normal PL circle;
  `h w ∈ Int P_w` and `h w` in no `P_u` to be deleted from `P_w`. Then each ball loses finitely many
  disjoint boundary caps; the literal formula gives 3-balls, intersection disks and
  `⋃ D_w = ⋃ P_w`. These come from **whole-overlap control** in the controlled piercing construction
  ("tubes avoid outer ball boundaries" is not enough). The per-ball marker is carried separately
  and preserved through the frozen circle-removal leaf's off-support output — no renewed closeness
  to `h` needed.

## 4. Matching
Pass what the supplier already gives: `hDvQ : ∀ w, Dv w ⊆ Q w`,
`hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)`; with `hQsep`, `hQlf` first *prove* rim
containment, then the inner torus certificate; the three-stage relative parametrisation must not
change the fixed `Dv`.

**Missing obligations:** source interior cover of the whole graph; correctly chosen stability
scale; per-ball membership retention; isolation of whole overlaps, not only of circle tubes.
**Fixture:** periodic tetrahedral triangulation, non-identity affine shear, fine carriers, standard
piercing; one removable extra circle in one tube. **Biggest surprise:** after closeness is
forgotten, `h(K)` covered by the union does not mean each `h w` is still in the ball labelled `w`.

## Worker's due-diligence results (2026-09-21, before the sixth repair)
* **Detour: verified.** Nothing bounds `Cp` from below on the graph (only the single vertex point);
  `Disjoint (Sn e) graph` plus the tube/graph margin even force the piercing circle off the graph.
* **Deleted balls: both verified.** With every `G w := L (· + a)` all 21 package clauses are
  homeomorphic transports of source clauses (nothing tied `G w` to `h` per ball); the only source
  disjointness was conditional, so already-intersecting non-adjacent fingers were legal.
* **No-filling-disk clause: agreed to be derivable, clause kept.** The derivation needs two private
  declarations (`fundamentalGroupSolidTorusEquivInt`, `euclideanCircleHomeomorph`) in files the worker
  may not edit; the clause has no consumer; dropping it would break the frozen leaf's byte-identity.
  Owed cleanup, not an obligation of the chain.
* **Stability theorem PROVED** (`PLCellOnStability.lean`): `F` stays a continuous injection;
  invariance of domain, local connectedness of a charted space, components of small balls, a finite
  subcover, `δ` the minimum of the scales. No degree, no leaf remainder.
* Not done for budget, not because false: the single-cap lemma as its own leaf; rim containment
  proved out of the matching leaf (route: rim ⊆ graph, then `hDnbhd`, then remove the finitely many
  non-incident closed `Dv w`; needs downward closure of the faces and an index bijection).
