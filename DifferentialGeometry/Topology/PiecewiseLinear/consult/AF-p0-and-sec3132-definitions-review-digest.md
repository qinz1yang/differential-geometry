# Digest — external reviews of the P0 skeleton (v2, `5c3b76db`) and of the §31–§32 definitional layer (`f6a3a00e`), 2026-09-21

Marks: **[V]** checked by the lead against the Lean text or the book; **[–]** not independently
verified; **[D]** the lead disagrees or qualifies.

## Part 1 — `Skeleton/Section34Control.lean` (P0 v2)

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_isPLCellOn_locallyFinite_cover_of_isOpen` | **OK** | T2, second countable, compatible PL atlas suffice; `N y` need only be a neighbourhood; `Y = ∅` takes the empty index |
| `exists_locallyFinitePLPieceIn_of_isOpen` | **FALSE [V]** | `[Nonempty M₁]` missing |
| `isCombinatorialManifold_of_locallyFinitePLPieceIn` | **OK** | true for every compatible realisation (local PL Euclidean model ⇒ vertex links are PL 2-spheres); no second countability needed |
| `locallyFinite_section34CarrierSupport` | **OK** | local finiteness *relative to `U`*, indexed by faces, is right |
| `exists_isSubdivision_section34CarrierSupport_subset` | **OK** | the cover need not be locally finite: star refinement, then a face-compatible variable-scale subdivision; a uniform number of barycentric subdivisions is not enough |

* **The false leaf [V].** `LocallyFinitePLPieceIn` has a *total* field `map : E → X` (`PolyhedralGraph.lean:50`). With
  `M₁ = ∅`, `U = ∅` and the empty atlas every hypothesis holds, while `EuclideanSpace ℝ (Fin N)` is
  nonempty for every `N` (also `N = 0`), so no `map` exists. Repair: `[Nonempty M₁]` on the leaf, **and
  on `Section34ControlStatement` and its assembly**; never `U.Nonempty` (an empty open subset of a
  nonempty manifold must stay allowed). The proved tower producer already assumes `[Nonempty X]`.
* **Lead's extension [V].** The same defect sits in the *frozen* leaf
  `exists_section34NormalFamily` of `Skeleton/Section34Terminal.lean` (it also outputs a
  `LocallyFinitePLPieceIn` existentially, with no `Nonempty M₁`), reviewed OK three times. Its
  consumer `Section34CellDiagram` is universally quantified and *true* for `M₁ = ∅` (empty label
  type), so the terminal assembly must split on `IsEmpty M₁` and the leaf gets `[Nonempty M₁]`.
* **Docstring corrections.** (i) "`U = ∅`: any `N` will do" omits `M₁ = ∅`. (ii) "carriers need not hug
  the support image" means *no regular-neighbourhood shape is required*, not *no distance control*:
  containment + diameter already give `x ∈ S_t ⟹ H_t ⊆ B(h x, η x)`, so `H_t ⊆ N_ε(h '' S_t)` at the same
  scale needs no clause; a smaller scale is obtained by shrinking the input `η`. Later common
  charts and exterior criteria are supplied by the single-chart clause and the closed PL balls;
  the outer torus's smallness must control the separately chosen `Q_w`, never the whole `H_t`.
* No multiplicity hypothesis on the cover is needed: the finite reuse of a carrier is carried by
  the compact-set/local-finiteness argument already in the file.
* **Fixture:** `U = M₁ = M₂ = ℝ³`, `h(x,y,z) = (x, y, z + 10⁻² sin x)` (not PL), `η = 1`, a `10⁻³` tetrahedral
  grid and refinements, small standard cubes as carriers. **Likely surprise:** leaf (a1) — turning the
  compact-piece tower into *one* realisation in a fixed finite dimension that is topologically
  locally finite; injectivity in general position alone is not enough for an infinite complex.

## Part 2 — `CanonicalConfiguration.lean`, `PseudoCell.lean`

FIX = the specification must change, not "refuted". An OK on a proposition does not excuse its
upstream structure.

| Item | Verdict | Reason |
|---|---|---|
| `IsPlanarCellChain`, `IsRevolvedTorusChain`, `IsCanonicalConfiguration` | **FIX [V]** | adjacent `P_j` may coincide, the revolved "annulus" is then a circle |
| `Moise311`–`Moise314` | OK | 31.1–31.4; on the boundary of a polyhedral torus the bounded disk may be taken PL |
| `IsPseudoCell` | OK | the locally polyhedral reading is right |
| `IsTube` | **FIX [V]** | a plain neighbourhood plus the present overlap axioms is not a regular neighbourhood |
| `IsHandleDecompositionOfTube` | **FIX [V]** | admits families that are neither closed nor closures of components |
| `Moise321`, `Moise323` | FIX (inherited) | conclusions right; the source tube / handle predicates must be repaired |
| `Moise322` | **FIX [V]** — already repaired in `f5e1a6f23` | did not keep the vertex separation and the component labels for the *same* `E` |
| `Moise324` | **FALSE [V]** — already repaired in `f5e1a6f23` | asked the inner disk `D_J` to be PL |

* **① [V]** `P_j` need not lie on the x-axis. Counterexample to the chain as stated:
  `D_j = [j+0.6, j+2.4] × [−1,1] × {0}`, `P = ((2,0,0),(2,0,0),(3,0,0),(4,0,0))` — every clause holds, `A_0 = J_0`
  is a circle. Repair: `consecutive_ne : ∀ j : Fin 3, P j.castSucc ≠ P j.succ`.
* **② [D]** Keeping `IsCombinatorialSolidTorus` for `S''_j` is fine. The reviewer says 28.1 upgrades a
  general polyhedral solid torus to a CST; the lead read p. 201: 28.1 is about a *polyhedral torus*
  = a cyclic ring of four 3-cells, and the book says the general case is out of reach there. The
  CST is the cylindrical-diagram object defined before 24.9 (the reviewer agrees on that). In
  this tree `IsCombinatorialSolidTorus` is the cyclic ring and `HasCylindricalDiagram` the CST, so
  what 31.1 owes `moise308Nested` is *cylindrical diagram ⇒ cyclic ring* (slice the cylinder);
  28.1 is the converse. Digest AD §6 and the corrected module docstring say the same.
* **③** crossing at *every* point of the intersection, polygon vertices included; `HasPLCrossingAt` is a
  local PL normal form, not Euclidean orthogonality. **④** locally finite, not finite; a bridge to
  the book's triangulation language is still owed. **⑤** `Bd C'_i = h(Bd C_i)`; wildness is in the
  embedding, not in the intrinsic boundary; invariance of domain identifies it with the ambient
  frontier. Keep the transported form of (6).
* **⑥ [V]** Orthogonality may be replaced by a normal form; the regular neighbourhood may **not** be
  dropped. Counterexample: `K` the 1-skeleton of a planar equilateral triangle, `N` a large prism,
  `C_v` the three Voronoi sector prisms: pairwise intersections are rectangles meeting the matching
  edge only at its midpoint, but the three share the central vertical line, and `N` is a 3-cell, not
  a solid torus around the circle. §33 uses `Int N' \ K' ≅ Bd N × (0,1)` and its projection. Repair:
  a genuine regular-neighbourhood certificate with `C, D` bound to its dual-cell model; necessary
  (not claimed sufficient): `splitDisjoint` (different splitting disks disjoint) and
  `splitProper : D e ∩ frontier N = Dbd e`. Digest AD §6 independently lists what §32–§33 use.
* **Handle decomposition [V]:** moving one interior point `q` from `C''_u` to `C''_v` keeps cover,
  overlaps and one-vertex clauses. Repair: with `Eall = ⋃ e, Ec e`,
  `componentClosure : ∀ v, Cpp v = closure (connectedComponentIn (N' \ Eall) (h v))`, and pseudo-cells
  of different edges disjoint.
* **⑦ [V]** The book (p. 228–229, read by the lead) asks `Δ₁` polyhedral and `D_J ⊆ E` a 2-cell with
  the centre in its interior. Tame counterexample to the PL form: the graph
  `z = g(max(|x|,|y|))`, `g(2⁻ⁿ) = 4⁻ⁿ`, linear in between — a pseudo-cell, but no finite PL disk
  contains a neighbourhood of the centre. Repair = exactly the form already committed.

**Owed:** a common regular-neighbourhood / dual-cell model, a locally-polyhedral dictionary, one
pseudo-cell with separation and component closure. **Fixtures:** an off-axis three-rectangle chain
with transverse polygonal annuli; a genuine triangle-graph tube with `h = id` and standard pseudo
disks.
