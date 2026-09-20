# A — §33–§35 lemma list, notation and dependency map (Lane D, 2026-09-20)

Source: Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47.
PDF `D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`; printed page + 9 =
zero-based PDF index. Pages read in full for this document: **230–238** (§33, statement of
33.1 and the parts §34 consumes), **239–246** (§34, in full), **247–252** (§35, in full), plus
the statements of 27.3 (p. 199), 28.8/28.9 (p. 204), 30.4–30.8 (pp. 216–218), 32.1–32.4
(pp. 223–229).

All mathematical statements below are restatements in my own words. Flags:
**[ASSERTED]** = claimed in the book without proof or by appeal to a figure;
**[AMBIG]** = the printed statement admits two readings, both given;
**[SLIP]** = the printed cross-reference or formula appears to be wrong.

---

## 0. Where each numbered result is actually consumed

Established by reading every `Theorem n.m` citation on pp. 230–252. This is the item the
consultant could not verify (his Q4 "Not verified: where 26.4, 30.6–30.7, 27.3/28.8, 32.4 are
consumed").

| Result | Consumed at | In the proof of |
| --- | --- | --- |
| 32.1–32.3 | p. 231 | §33, construction of the pseudo-cells `E = E_e`; 32.3(8) gives smallness |
| 26.6 | p. 232 | §33 Lemma 5 (the bounded component contains `K'`) |
| 30.2 | p. 232, p. 236 | §33 Lemma 5; §33 Lemma 10 (`G₁` separates `V` from `W`) |
| 32.4 | p. 233, p. 238 | §33 Lemma 8; §33 end of proof (replace `E ∩ X` by a polyhedral disk) |
| 26.4 (Loop theorem, extended) | p. 234 | §33, `ker i* = 0` for `i* : π(Bd X) → π(N' − K')` |
| 22.9 | p. 236 | §33 Lemma 11 (`Bd X ≅ Bd N`) |
| 26.8 | p. 236 | §33 Lemma 11 (orientability) |
| 5.4 | p. 237 | §33 Lemma 13 (extend a PLH of disk boundaries over the disks) |
| 18.2 | p. 238 | §33, extend `f` from `Bd N` over all of `N` |
| **33.1** | **p. 240** | **§34 Lemma 1** (the only use of §33 inside §34) |
| **30.5** | **p. 240** | **§34 Lemma 3** |
| **30.8** | **p. 240** | **§34 Lemma 2** |
| **28.8** | **p. 244** | **§34 Lemma 11** |
| 33.1 | p. 247 | §35 introductory remark only (not in a proof) |
| **34.1** | **p. 249** | **§35.1**, to produce `f_v : C''_v → M₂` |
| **27.3** | **p. 250** | **§35.1 Lemma 1** |
| 34.1, 35.1 | p. 251 | §35.2 (34.1 as the template, 35.1 as the input) |

**30.6 and 30.7 are never cited in §§33–35.** 30.6 is used only inside the proof of 30.7, and
30.7 only inside 30.8; §34 p. 240 verifies the *hypotheses* of 30.8 (a toroidal shell
configuration), it does not invoke 30.6/30.7 directly. **26.4 and 32.x are consumed only in
§33, never in §34.** So the §34 argument proper rests on exactly four external results:
**33.1, 30.5, 30.8, 28.8**.

### The four external statements, as printed

* **33.1** (p. 230). `K` a finite connected 1-dimensional polyhedron in `R³` with no
  end-points; `U` an open set containing `K`; `h : U → R³` a homeomorphism; `ε > 0`. Then there
  are a regular neighbourhood `N` of `K` with `N ⊆ U` and a PL homeomorphism `f : N ↔ X ⊂ R³`
  such that (1) `X` is a neighbourhood of `K' = h(K)` and (2) `f` is an ε-approximation of
  `h|N`.
* **30.5** (p. 217). `C₁, C₂` topological 3-cells in `R³` (or `S³`) with `C₁ ⊆ Int C₂` and
  `Cl(C₂ − C₁)` a spherical shell. Then there is a polyhedral 3-cell `C` with
  `C₁ ⊆ Int C ⊆ C ⊆ Int C₂`.
* **30.8** (p. 218). `S₁, S, S₂` as in 30.7 — i.e. `S₁, S₂` topological solid tori in `R³` with
  `S₁ ⊆ Int S₂`, `Cl(S₂ − S₁)` a toroidal shell, and `S` a **combinatorial** solid torus with
  `S₁ ⊆ Int S ⊆ S ⊆ Int S₂` — and `J` a spine of **`S₁`**, `P₀ ∈ J`. Then the loop `p_J`
  generates `π(S, P₀)`. Moise remarks explicitly that the claim is about *every* `S` as in
  30.7, not merely about some such `S`, and that the distinction matters later.
* **28.8** (p. 204). `S` a combinatorial solid torus, `T = Bd S`; `J₁,…,Jₙ` disjoint polygons
  on `T` with `Jᵢ ≁ 0` on `S` for **every** `i` and with `⋃Jᵢ` carrying a generator of `H₁(S)`.
  Then each `Jᵢ` carries a generator of `H₁(S)`.
  Companion **28.9** (p. 204): a polygon `J ⊆ T` with `J ∼ 0` on `T` bounds a 2-cell in `T`.
* **27.3** (p. 199, used in §35.1). `J` a polygon in the interior of a PL annulus `A`. Then
  either (1) `J` bounds a 2-cell in `A`, or (2) `J` carries a generator of `H₁(A)` and a
  generator of `π(A)`.

---

## 1. Standing notation of §34 (pp. 239–240, 244–245)

`K` is a polyhedral 3-cell in `R³`; `h : K → R³` a homeomorphism; `ε > 0`.

| Object | Definition | Page |
| --- | --- | --- |
| `U` | open set in `R³` containing `K` to which `h` has been extended; legitimate after the opening reduction (push `K` into `Int K` by a PLH close to the identity, approximate there, compose back) | 239 |
| subdivision of `K` | chosen so that the simplexes are "small" (degree prescribed later) **and** so that in the link `L(v)` of every vertex `v` the interior of an edge never separates two vertices of `L(v)` from one another. The second condition is used only in Lemmas 9 and 10 | 239 |
| `K¹` | the 1-skeleton of that subdivision of `K` | 239 |
| `N` | a regular neighbourhood of `K¹` lying in `U`; may be taken inside any prescribed neighbourhood of `K¹` | 239 |
| `D_e` | the splitting disk of `N` through the mid-point of the edge `e`; `Bd D_e ⊆ Bd N` | 239 |
| `C_v` | the dual cell of `N` cut out by the splitting disks, containing exactly the one vertex `v`; `Bd C_v = (Bd C_v ∩ Bd N) ∪ ⋃_{e ∋ v} D_e` | 239 |
| `S(v)` | the half-star of `v` in `K¹`, i.e. `K¹ ∩ C_v` | 239 |
| `f₁` | a PL homeomorphism approximating `h|N`, with `f₁(N)` a neighbourhood of `h(K¹)`; supplied by Lemma 1 | 239 |
| `A' ` | `= h(A)`, for `A ⊆ U`. In particular `σ' = h(σ)`, `J' = Bd σ'`, `w' = h(w)` | 239 |
| `A''` | `= f₁(A)`, for `A ⊆ N`. In particular `N''`, `C''_v`, `D''_e`, `N''_σ` | 239 |
| `N_σ` | for a 2-simplex `σ`, the union of the dual cells of `N` containing vertices of `σ`; a solid torus, with spine `Bd σ` | 240 |
| `A''_v` | the "k-annulus" `Bd C''_v ∩ Bd N''`, i.e. a 2-sphere with `k` holes | 243 |
| `C_σ` | for a 2-simplex `σ`, a small polyhedral 3-cell **in the image**, a neighbourhood of `Bd σ'` (Lemma 5(1)); supplied by Lemma 3/5 and modified by Operations 1–2 | 240–242 |
| `D_σ` | `= Cl(σ − N)`, a polyhedral disk in the 2-simplex `σ`; `J_σ = Bd D_σ ⊆ Bd N` | 244 |
| `C(σ³)` | `= Cl(σ³ − N)` for a 3-simplex `σ³` | 244 |
| `X(σ³, v)` | `= Bd C(σ³) ∩ Bd C_v` for `v` a vertex of `σ³`; a polyhedral disk lying in `Bd N` | 244 |
| `D''_σ` | an **irreducible** disk in `Bd C_σ` whose boundary lies in `Bd N''`; then `D''_σ ∩ Bd N'' = J''_σ = Bd D''_σ` and `Bd D''_σ ⊆ Bd N''_σ` | 244 |
| `W_i` | `Bd C''_{v_i}` with the interiors of the three splitting disks `D''_e` (`e ⊂ σ³`, `e ∋ v_i`) deleted: a 2-sphere with three holes | 245 |
| `X_i, Y_i` | the two polyhedral disks into which the broken lines `W_i ∩ Bd D''_σ` (corrected: the lines lie in `W_i`, joining components of `Bd W_i`; their end-points are the marked points) decompose `W_i`; notation chosen by the unbounded-component rule below | 245 |
| `X''(σ³, v_i)` | `= X_i` | 245 |
| `C''(σ³)` | the polyhedral 3-cell bounded by the 2-sphere `⋃_i X_i ∪ ⋃_{σ ⊂ σ³} D''_σ` | 245 |

### Two notational traps (important for formalisation)

1. **`C` is overloaded by the index type.** `C_v` (vertex index) is a **source** dual cell in
   `N`; `C_σ` (2-simplex index) is an **image-side** small 3-cell around `σ' = h(σ)`. There is
   no source `C_σ` and no `C''_σ`. Lemma 9 reads `Bd C_σ ∩ Bd C''_v ∩ Bd N''` — a source-side
   symbol cannot appear there, so both `C_σ` and `C''_v` are in the image.
2. **The double prime is not always `f₁`.** For `A ⊆ N` the book sets `A'' = f₁(A)`, so `N''`,
   `C''_v`, `D''_e`, `N''_σ` really are `f₁`-images. But `D_σ`, `C(σ³)`, `X(σ³,v)` are **not**
   contained in `N`, and `D''_σ`, `C''(σ³)`, `X''(σ³,v)` are **constructed by choice**
   (pp. 244–245), not obtained by applying `f₁`. The consultant's uniform convention `Â = f₁(A)`
   is therefore correct only for the four `f₁`-images. This is also why the book ends with the
   Query (p. 246): the final `f` restricted to `N` need not equal `f₁`.

---

## 2. The lemmas of §34

**§34 has Lemmas 1–11 and Operations 1 and 2 — not thirteen lemmas.** §33 is the section with
thirteen lemmas (pp. 230–238). The brief said "Lemma 1 … Lemma 13" for §34; that count belongs
to §33.

### Lemma 1 (p. 240) — the output of 33.1, with four incidence clauses

There exist a regular neighbourhood `N` of `K¹` and a PL homeomorphism `f₁ : N ↔ N'' ⊂ R³` with

1. `N''` is a neighbourhood of `h(K¹)`;
2. `D''_e ∩ σ' ≠ ∅` only if `e` is an edge of `σ`;
3. `C''_v ∩ σ' ≠ ∅` only if `v` is a vertex of `σ`;
4. `N''_σ` is a neighbourhood of `J' = Bd σ'`;
5. `f₁` is an `(ε/3)`-approximation of `h|N`.

*Proof:* 33.1 gives `N` and `f₁` with (1) and (5); (2)–(5) then hold automatically once `f₁` is
a sufficiently close approximation of `h|N`. **[ASSERTED]** — "sufficiently close" is not
quantified, and (2)–(4) are compactness/incidence arguments the book does not write out.
Supplementary clause used later: `N` may be taken inside any prescribed neighbourhood of `K¹`,
hence `N''` inside any prescribed neighbourhood of `h(K¹)`.

### Lemma 2 (p. 240) — the generator clause

Under the conditions of Lemma 1, `f₁` can be chosen so that for every 2-simplex `σ`,
`J' = Bd σ'` carries a generator of `π(N''_σ)`.

*Proof:* one exhibits source solid tori `S₁, S₂` with
(a) `N_σ ⊆ Int S₂`;
(b) `S₁` a neighbourhood of `Bd σ ∪ ⋃_{v ∈ σ} S(v)` inside `K¹`;
(c) `Cl(S₂ − S₁)` a toroidal shell;
(d) `J = Bd σ` a spine of `N_σ`.
Then for `f₁` close enough, (e) `N''_σ ⊆ Int S'₂`; and, `f₁` having been fixed, `S₁` may be
re-chosen so that (f) `S'₁ ⊆ Int N''_σ`. The quadruple `(S'₁, N''_σ, S'₂, Bd σ')` then satisfies
the hypotheses of **30.8** with `(S₁, S, S₂, J)`, which gives the conclusion.
Note the *order of choice*: `f₁` first, then `S₁` — clause (f) cannot be obtained before `f₁`.
Note also that 30.8 is used in the form where the spine is a spine of the **inner** torus `S'₁`
and the conclusion is about the **middle** one `N''_σ`; the "every `S`" remark attached to 30.8
is what makes this legitimate. **[ASSERTED]**: that `Bd σ` is a spine of `N_σ` and that (a)–(d)
are achievable; and that `N''_σ` is a combinatorial solid torus (it is, since `f₁` is a PLH).

### Lemma 3 (p. 240) — small polyhedral 3-cell neighbourhoods in general position

Every set `σ'` has arbitrarily small polyhedral 3-cell neighbourhoods `C_σ` such that
`Bd C_σ` is in general position relative to `Bd N''`, and `Bd C_σ ∩ Bd N''` is in general
position relative to every `Bd D''_e`.

*Proof:* each `σ` has arbitrarily small 3-cell neighbourhoods `C₁ ⊆ Int C₂` with `Cl(C₂ − C₁)`
a spherical shell, hence so does `σ'`; **30.5** then supplies a polyhedral 3-cell between them;
general position is arranged by minor adjustment. Moise says only that "general position" is
meant in one of its usual senses — **[AMBIG]**: the later uses require (i) `Bd C_σ ∩ Bd N''` a
1-manifold at which the two surfaces cross (Lemma 9's "by general position, `J` lies in the
interior of the k-annulus"), and (ii) `Bd C_σ ∩ Bd N'' ∩ Bd D''_e` a finite set of transverse
points (Lemma 10, Lemma 11). Take the conjunction.
**[ASSERTED]**: that `σ` has arbitrarily small shell-separated 3-cell neighbourhoods, and that
this transfers to `σ'` under the topological embedding `h`.

### Lemma 4 (p. 241) — the homology generator on the triple intersection

Let `C` be a polyhedral 3-cell neighbourhood of `σ'`. If `C` lies in a sufficiently small
neighbourhood of `σ'`, then `Bd C ∩ Bd N''_σ ∩ Bd N''` carries a generator of `H₁(N''_σ)`.

*Proof:* take a polyhedral disk `τ ⊆ K` with `τ ∩ K² = Bd σ = Bd τ`, so `σ' ∩ τ' = Bd σ' =
Bd τ'`. Choose polyhedral 3-cell neighbourhoods `C` of `σ'` and `C'` of `τ'` small enough that
`C` meets `C''_v` only for `v ∈ σ` and that `C ∩ C' ⊆ Int N''_σ`. Since `J'` carries a generator
of `π(N''_σ)` and `Int C ∩ Int C'` is a neighbourhood of `J'`, the latter carries a generator
`Z¹` of `H₁(N''_σ)`. As `Z¹ ∼ 0` on `C'`, `Z¹` is homologous in `C ∩ C'` to a cycle `Z¹₁` on
`Bd C`, which therefore generates `H₁(N''_σ)`; as `Z¹₁ ∼ 0` on `Bd C`, it is homologous in
`Bd C ∩ N''_σ` to a 1-cycle `Z¹₂` on `Bd C ∩ Bd N''_σ ⊆ Bd N''`.
**[SLIP]** the generator step is attributed to "(4) of Lemma 1"; Lemma 1(4) only says `N''_σ` is
a neighbourhood of `J'`. The generator statement is **Lemma 2**. Both are needed and both are
available, so the proof stands; only the citation is wrong.

### Lemma 5 (p. 241) — the prepared family `{C_σ}`, seven clauses plus a smallness clause

Under the conditions of Lemmas 1 and 2 there is a family `{C_σ}` of polyhedral 3-cells, one for
each 2-simplex `σ` of `K`, such that

1. `C_σ` is a neighbourhood of `Bd σ'`;
2. `C_σ ∩ C''_v ≠ ∅` only if `v` is a vertex of `σ`;
3. every `Bd C_σ` is in general position relative to `Bd N''`;
4. every `Bd C_σ ∩ Bd N''` is in general position relative to every `Bd D''_e`;
5. distinct `C_σ` meet only inside `Int N''`;
6. every `Bd C_σ ∩ Bd N''_σ ∩ Bd N''` carries a generator of `H₁(N''_σ)`;
7. for every vertex `w` of `K` and every 3-simplex `σ³` of `K` not containing `w`, the point
   `w'` lies in the **unbounded component of** `R³ − [⋃_{v ∈ σ³} C''_v ∪ ⋃_{σ ⊂ σ³} C_σ]`;

and finally

8. the `C_σ` can be chosen so that the sets `Bd C_σ` lie in arbitrarily small neighbourhoods of
   the corresponding sets `σ' ∪ N''_σ`.

*Proof:* by Lemmas 3 and 4. The book observes that Lemmas 3 and 4 in fact give the stronger
(1′) `C_σ` is a neighbourhood of `σ'` and (8′) the `C_σ` themselves lie in arbitrarily small
neighbourhoods of `σ'`; (1) and (8) are stated instead **because (1′) and (8′) are not preserved
by Operations 1 and 2**. It also records a sufficient condition for (7): it holds whenever
`⋃_{v ∈ σ³} C''_v` lies in a small enough neighbourhood of `⋃_{v ∈ σ³} h(S(v))` and each `C_σ`
lies in a small enough neighbourhood of `σ'`. **[ASSERTED]** — that sufficient condition is not
proved.
**ℝ³-specific:** clause (7) is the first place the ambient `R³` is used essentially; "unbounded
component" has no meaning in a general PL 3-manifold `M₂`.

### Operation 1 (p. 242)

Let `J` be a polygon in `Bd C''_v ∩ Bd N'' ∩ Bd C_σ`. Suppose `J` bounds a disk `D_J ⊆ Bd C''_v`
such that `D_J` meets no splitting disk `D''_e` of `N''` and `Int D_J` meets no `C_τ` with
`τ ≠ σ`. Add `D_J` to `Bd C_σ` and split the resulting polyhedron apart at `D_J`, keeping
`Bd N''` fixed. This replaces `Bd C_σ` by two disjoint polyhedral 2-spheres `S₁, S₂`, one of
which — say `S₁` — bounds a polyhedral 3-cell `C'_σ` that is still a neighbourhood of `Bd σ'`.
Operation 1 replaces `C_σ` by `C'_σ`.
**[ASSERTED]** that exactly one of `S₁, S₂` bounds a 3-cell that is still a neighbourhood of
`Bd σ'`. This is the clause that forces Lemma 5 to state (1) rather than (1′): the discarded
sphere may carry the part of `C_σ` that covered `Int σ'`.

### Lemma 6 (p. 242)

Operation 1 preserves the conditions of Lemmas 1, 2 and 5. The book verifies only the three
non-trivial clauses: Lemma 5(2) because `Bd C'_σ ∩ C''_v ≠ ∅` only for `v` a vertex of `σ`;
Lemma 5(5) because distinct `Bd C'_σ, C'_τ` still meet only in `Int N''`; Lemma 5(7) because it
is preserved separately by (a) adding `D_J` to `Bd C_σ` and (b) the splitting, which displaces
the result into an arbitrarily small neighbourhood of itself.
**[ASSERTED]** the remaining clauses (1), (3), (4), (6), (8) and Lemmas 1, 2 are said to be
trivial and are not checked.

### Operation 2 (p. 242, Figure 34.1)

Let `B` be a broken line in `Bd C''_v ∩ Bd N'' ∩ Bd C_σ` whose end-points `x, y` lie in some
`Bd D''_e`, with no other point of `B` on any splitting disk of `N''`. Let `B'` be a broken line
from `x` to `y` **in `Bd D''_e`**, and suppose `B ∪ B'` bounds a disk `D_J` in
`Bd C''_v ∩ Bd N''` whose interior meets no `Bd C_τ`. (`D_J` cannot contain a splitting disk,
because `D_J ⊆ Bd N''`.) Operation 2 drags `B` homeomorphically across `Bd D''_e`, keeping
`Bd N''` fixed, so that `x` and `y` are removed from `Bd D''_e ∩ ⋃_τ Bd C_τ` and no new
intersection points appear.
**[ASSERTED]/figure:** the existence of the drag with "no new intersection points" is described
by reference to Figure 34.1 and explicitly left undefined as an isotopy.

### Lemma 7 (p. 242)

Operation 2 preserves the conditions of Lemmas 1, 2 and 5. **[ASSERTED]** — the entire proof is
the claim that the verifications are trivial. Note that the preservation of 5(7) is *not*
trivial in the same sense as for Operation 1: Operation 2 changes `Bd C_σ` inside `Bd N''`,
whereas Operation 1's argument for 5(7) used the small displacement of the split polyhedron.

### Lemma 8 (p. 243) — termination

Subject to the conditions of Lemmas 1, 2, 5, the family `{C_σ}` can be chosen so that neither
Operation 1 nor Operation 2 is possible.

*Proof:* Operation 1 strictly decreases the number of components of
`Bd N'' ∩ ⋃_σ Bd C_σ`; Operation 2 strictly decreases the number of points of
`[⋃_e Bd D''_e] ∩ ⋃_σ (Bd N'' ∩ Bd C_σ)`. Alternating them therefore terminates.
**Finiteness-specific:** the two counting functions are finite only because `K` is a *finite*
complex (and `N''`, `{C_σ}` finite families). Operation 1 does not obviously decrease the
Operation-2 count and vice versa, so "alternating must terminate" is itself
**[ASSERTED]** — the book gives no lexicographic or well-founded measure.

*From here on the standing hypotheses are: Lemmas 1, 2, 5 and 8.*

### Lemma 9 (p. 243) — no closed curve in a triple boundary intersection

No set `Bd C_σ ∩ Bd C''_v ∩ Bd N''` contains a polygon.

*Proof:* suppose `J` is such a polygon. By general position `J` lies in the interior of the
k-annulus `A''_v = Bd C''_v ∩ Bd N''`, and `J` bounds a disk `D_J ⊆ Bd C''_v`, which may be
taken inmost. Since Operation 1 is impossible, `J` must separate two components `J₁, J₂` of
`Bd A''_v` from one another in `A''_v`. This is impossible: for every 2-simplex `τ` with `v` as
a vertex, `Bd C_τ ∩ Bd N''` carries a generator of `H₁(N''_τ)` (Lemma 5(6), abbreviated), so
if `e₁, e₂` are the edges of `τ` at `v` then `A''_v ∩ Bd C_τ` contains a broken line from a
point of `Bd D''_{e₁}` to a point of `Bd D''_{e₂}`. Now `K` is a triangulated 3-cell, and the
subdivision was chosen so that in `L(v)` the interior of an edge never separates two vertices;
hence for any two edges `e, e'` at `v` there is a chain `σ₁,…,σₙ` of 2-simplexes at `v`, all
different from `σ`, with `e ⊂ σ₁`, `e' ⊂ σₙ`, and consecutive `σᵢ, σᵢ₊₁` sharing an edge. Splicing
the corresponding broken lines gives a broken line in `Bd C''_v ∩ Bd N''` from `D''_{e}` to
`D''_{e'}` that misses `Bd C_σ`, so `J` cannot separate `J₁` from `J₂`.
**Uses:** Operation 1's impossibility (Lemma 8); Lemma 5(6); the general-position clause; and
the **link condition on the subdivision** from p. 239.
**ℝ³/finiteness-specific:** "`K` is a triangulated 3-cell" is used to know that the link of `v`
is a 2-sphere or a disk with the required connectivity. **This is exactly the hypothesis that
35.2 does not have** (there `K` is a polyhedral 3-manifold with boundary).

### Lemma 10 (p. 243–244) — no arc returning to the same splitting disk

No set `Bd C_σ ∩ A''_v` contains a broken line `B` whose two end-points `x, y` lie in the same
set `D''_e`.

**[AMBIG]** the printed statement says "the same set `D''_e`"; the proof immediately writes
`Bd D''_e` as the union of two broken lines with end-points `x` and `y`, and Operation 2 is
stated with the end-points in `Bd D''_e`. Since `Bd C_σ ∩ A''_v ⊆ Bd N''` and
`D''_e ∩ Bd N'' = Bd D''_e`, the two readings coincide; the later use (Lemma 11, "crosses
`Bd D''_e` exactly once geometrically") requires the `Bd D''_e` reading.

*Proof:* suppose such a `B` exists; by general position it meets no other splitting disk.
`Bd D''_e` splits into two broken lines `B₁, B₂` with end-points `x, y`, and one of `B ∪ B₁`,
`B ∪ B₂` bounds a disk `D_J ⊆ Bd C''_v` not containing `D''_e`; take `B` inmost. Then `D_J`
contains no splitting disk (else a polygon in `A''_v` missing `⋃_{τ ≠ σ} Bd C_τ` would separate
two splitting disks in `Bd C''_v`, impossible exactly as in Lemma 9), and `D_J` contains no
polygon of `⋃ Bd C_τ` (else Operation 1 would be possible). Hence Operation 2 can be performed,
contradicting Lemma 8.

### Lemma 11 (p. 244) — the crossing number, one

For each 2-simplex `σ`, every component `J` of `Bd C_σ ∩ Bd N''_σ` crosses each set `Bd D''_e`
(`e` an edge of `σ`) **exactly once**.

*Proof:* by Lemma 5(6) the union of these polygons `J` carries a generator of `H₁(N''_σ)`.
**28.8** then gives that each such `J` either carries a generator of `H₁(N''_σ)` or bounds a
disk in `Bd N''_σ`.
Case 1: if `J` carries a generator, it crosses each `Bd D''_e` (`e ⊂ σ`) *algebraically* once,
and Lemma 10 upgrades this to *geometrically* once.
Case 2: if `J` bounds a disk in `Bd N''_σ`, it crosses each `Bd D''_e` algebraically zero times,
which contradicts Lemma 9 or Lemma 10. So Case 2 is impossible.
**[SLIP]/[AMBIG]** 28.8 as printed requires `Jᵢ ≁ 0` on `S` for *every* `i`, and concludes that
each carries a generator; it does not state the dichotomy "generator or bounds a disk in
`Bd S`". The dichotomy needs 28.8 together with 28.9 and the exclusion of meridians (a polygon
null-homologous in the solid torus but essential on the torus). Both readings: (a) apply 28.8 to
the subfamily of essential `J`'s and handle the rest by 28.9; (b) read the citation as covering
28.8–28.9 jointly. The later use (stage 1 of the extension) needs only the conclusion as stated.
Case 2's "easily gives a contradiction" is **[ASSERTED]**.

---

## 3. The seven-stage extension (pp. 244–246)

### 3.1 Preparatory facts

*Source side* (p. 244). `X(σ³,v)` is a polyhedral disk. If `v, v'` are the end-points of an edge
`e` of `σ³`, then `X(σ³,v) ∩ X(σ³,v')` is a broken line in `Bd D_e` whose end-points lie in two
different sets `Bd D_{σ₁}`, `Bd D_{σ₂}` and whose interior meets no third `D_σ`. `Int C(σ³)`
contains no point of `N` and no point of any `C(τ³)` with `τ³ ≠ σ³`. **[ASSERTED]** — all of
this is read off the source triangulation without proof.

*Image side* (p. 244). For each `σ`, `Bd C_σ` contains a disk whose boundary lies in `Bd N''`;
`D''_σ` is chosen to be such a disk that is **irreducible**. Then `D''_σ ∩ Bd N'' = J''_σ =
Bd D''_σ` and `Bd D''_σ ⊆ Bd N''_σ`. The existence of such a disk is **[ASSERTED]**; its
boundary is a component of `Bd C_σ ∩ Bd N''_σ`, which is what Lemma 11 governs.

*Image side* (p. 245), for `σ³ = v₀v₁v₂v₃`. Each `W_i` (= `Bd C''_{v_i}` minus the interiors of
the three splitting disks at `v_i` inside `σ³`) is a 2-sphere with three holes, and every two
components of `Bd W_i` are joined by a broken line lying in some `Bd D''_σ` (`σ ⊂ σ³`); these
broken lines cut `W_i` into two polyhedral disks `X_i, Y_i`. Since `⋃_{σ ⊂ σ³} D''_σ` does not
separate `R³` **[ASSERTED]**, some `Int X_i` or `Int Y_i` contains a limit point of the
**unbounded component of** `R³ − [⋃_{v ∈ σ³} C''_v ∪ ⋃_{σ ⊂ σ³} D''_σ]`. Name it `Y₀`; choose the
remaining labels so each `Y_i` shares a broken line with `Y₀`; then each `Y_i` has the same
property, and each `X_i` shares a broken line with `X₀`. Hence `⋃_i X_i` is a 2-sphere with four
holes, filled by the four disks `D''_σ`, and `⋃_i X_i ∪ ⋃_{σ ⊂ σ³} D''_σ` is a 2-sphere bounding
a polyhedral 3-cell `C''(σ³)`. Then `Int C''(σ³)` contains no point of any `Int Y_i`, hence none
of any `C''_v` with `v ∈ σ³`, **and none of any `C''_v` with `v ∉ σ³` — because that would
contradict Lemma 5(7)**. Consequently `Int C''(σ³)` meets no `D''_σ`, and for `σ₁, σ₂ ⊂ σ³` with
`σ₁ ∩ σ₂ = e` the set `D''_e ∩ Bd C''(σ³)` is a broken line with end-points on `Bd D''_{σ₁}` and
`Bd D''_{σ₂}` and no third point of the form `Bd D''_σ ∩ Bd D''_e`.
**[CORRECTED 2026-09-20 against the printed page: an earlier version of this file had
`Bd D''_σ ∩ Bd D''_{σ'}` here, an intersection that is empty anyway. The printed clause is the
empty-sector condition on the splitting circle `Bd D''_e`, and it is what supplies the
cyclic-order compatibility of stage 2 — so stage 2 does have a producer in the book, in this
unnumbered paragraph; its proof still has to be formalised.]**

**This paragraph is where Lemma 5(7) is consumed, and it is the only consumption of 5(7) in
§34.** It is also the second essential use of `R³`.

### 3.2 The stages

`f : K ∪ N → R³`, PL at each stage.

| # | domain added | target | already defined on | supplied by |
| - | --- | --- | --- | --- |
| 1 | `Bd D_σ ∩ Bd D_e` (a single point, for each pair `e ⊂ σ`) | `Bd D''_σ ∩ D''_e` | nothing | **Lemma 11**: `Bd D''_σ` is a component of `Bd C_σ ∩ Bd N''_σ` and crosses `Bd D''_e` exactly once, so the target is a single point too. Since `Bd D''_σ ⊆ Bd N''` and `D''_e ∩ Bd N'' = Bd D''_e`, the printed `Bd D''_σ ∩ D''_e` equals `Bd D''_σ ∩ Bd D''_e` — no typo. |
| 2 | `Bd D_e` (a polygon) | `Bd D''_e` (a polygon) | the marked points of stage 1, one for each 2-simplex `σ ⊃ e` | circle-to-circle PLH matching finitely many marked points. **[ASSERTED]**: that the *cyclic orders* of the marked points on `Bd D_e` and on `Bd D''_e` agree. Nothing in Lemmas 1–11 is stated to give this; it is the first genuinely unproved hypothesis of the assembly. |
| 3 | `Bd C_v ∩ Bd D_σ` (an arc of `J_σ` inside one dual cell) | `Bd C''_v ∩ Bd D''_σ` | its two end-points, from stage 1 | arc-to-arc PLH. Needs: `Bd C''_v ∩ Bd D''_σ` is a single arc with the matching end-points — i.e. `Bd D''_σ` meets `Bd C''_v` in one arc, which follows from Lemma 11 (one crossing of each of the two splitting disks at `v` in `σ`) together with Lemma 9 (no closed component). |
| — | `D_e` (the splitting disks) | `D''_e` | `Bd D_e`, from stage 2 | **[AMBIG]/gap**: the book assigns no stage to the splitting disks, yet asserts after stage 4 that `f` is defined on `Bd C_v`, and `Bd C_v ⊇ ⋃_{e ∋ v} D_e`. Two readings: (a) stage 2 should read `f(D_e) = D''_e`; (b) an unnumbered coning extension over each `D_e` is implicit. The later use (stage 5) requires `f` on `D_e`, so reading (a) or (b) must be adopted; (a) is the economical one, and the printed `Bd D_e` form is still needed *first* because stage 3's arcs end on `Bd D_e`. |
| 4 | `X(σ³,v)` (a polyhedral disk) | `X''(σ³,v) = X_i` (a polyhedral disk) | all of `Bd X(σ³,v)`, which is the union of arcs from stage 3 (pieces of `Bd D_σ` in `Bd C_v`) and arcs from stage 2 (pieces of `Bd D_e`) | disk-to-disk PLH extending a boundary PLH. Target is a disk by the `W_i = X_i ∪ Y_i` decomposition (p. 245); the labelling `X_i` vs `Y_i` is fixed by the unbounded-component rule. |
| 5 | `C_v` (a PL 3-ball) | `C''_v = f₁(C_v)` (a PL 3-ball) | all of `Bd C_v = ⋃_{σ³ ∋ v} X(σ³,v) ∪ ⋃_{e ∋ v} D_e`, from stages 4 and the splitting-disk extension | ball-to-ball PLH extending a boundary PLH. Target is a PL ball because `f₁` is a PLH and `C_v` is a dual cell. |
| 6 | `D_σ = Cl(σ − N)` (a polyhedral disk) | `D''_σ` (a polyhedral disk) | all of `Bd D_σ = J_σ`, from stage 3 | disk-to-disk PLH. Target is a disk by its definition as an irreducible disk in `Bd C_σ` (p. 244). The book says "now `f` is defined on each `Bd D_σ`" only after stage 5; in fact stage 3 already covers `Bd D_σ`, so the minimal prerequisite of stage 6 is stage 3. |
| 7 | `C(σ³) = Cl(σ³ − N)` (a PL 3-ball) | `C''(σ³)` (a polyhedral 3-cell) | all of `Bd C(σ³) = ⋃_{v ∈ σ³} X(σ³,v) ∪ ⋃_{σ ⊂ σ³} D_σ`, from stages 4 and 6 | ball-to-ball PLH. Target is a 3-cell by the 2-sphere argument of p. 245; the *interior* clauses there (`Int C''(σ³)` meets no `C''_v`, no `D''_σ`) are what make the images of distinct `C(σ³)` and of the `C_v` disjoint, i.e. what makes the glued `f` injective. |

**Approximation.** `f` is an ε-approximation of `h` provided the images `h(σ³)` are small enough
and the sets `C''_v` and `D''_σ` lie in small enough neighbourhoods of `h(S(v))` and `σ'`
respectively. **[ASSERTED]** — the ε-bookkeeping is not carried out; only Lemma 1(5)'s `ε/3` is
ever numerically fixed.
**Conclusion.** `f|K : K ↔ K'' ⊂ R³` is the PL ε-approximation of `h` required by 34.1.
**Query (p. 246).** Moise leaves open whether `f` can be chosen with `f|N = f₁`. So the §34
contract must *not* require agreement with `f₁`; the consultant's remark on this is correct.

### 3.3 The consultant's seven-stage table, checked

His left column ("correspondence") is **correct at every row**, with `Â = f₁(A)` replaced by the
book's `A''` and with the caveat of §1 trap 2 (`D̂^σ`, `Ĉ(σ³)`, `X̂(σ³,v)` are chosen, not
`f₁`-images). His right column is his own identification; against the book:

* row 1 "consistent matching of marked points" — correct, and the exact producer is **Lemma 11**;
* row 2 "cyclic-order compatibility" — correct **and this is a real gap**: the book asserts it;
* row 3 "matching arc components, end-points, incidences" — correct; producers are Lemmas 9+11;
* row 4 "PL types of the patches; earlier boundary maps match" — correct; the patch type comes
  from the `W_i` decomposition, and the *choice* of patch from Lemma 5(7) via `R³`;
* row 5 "complete compatible boundary data incl. shared splitting disks" — correct, and it
  exposes the missing splitting-disk stage noted above;
* row 6 "target a PL disk, whole boundary map defined" — correct; irreducibility of `D''_σ`;
* row 7 "target a PL 3-ball, boundary correspondence complete, correct intersections" — correct;
  "correct intersections" is precisely the `Int C''(σ³)` clauses of p. 245, hence Lemma 5(7).

His table omits nothing that the book supplies, and his "Missing: exact producers for the right
column" is answered above for rows 1, 3, 4, 6, 7; rows 2 and 5 have **no** producer in the book.

---

## 4. §35

### 4.1 Theorem 35.1 (p. 248)

`K` a 1-dimensional polyhedron in a PL 3-manifold `M₁`; `U` an open set containing `K`;
`h : U → M₂` a homeomorphism into a PL 3-manifold `M₂`; `φ` a **strongly positive** function on
`U` (everywhere positive and bounded away from `0` on every compact set — continuity is *not*
required). Then there are a regular neighbourhood `N` of `K` in `U` and a PL homeomorphism
`f : N ↔ X ⊆ M₂` with (1) `X` a neighbourhood of `K' = h(K)` and (2) `f` a φ-approximation of
`h|N`. (`K` may be infinite; the regular-neighbourhood convention for non-closed `K` is fixed on
p. 247 by triangulating `U` rectilinearly with respect to `M₁`.)

### 4.2 Structure of the proof of 35.1 (pp. 248–251), in order

1. **Reduction.** Assume `K` closed relative to `U`; replace `M₁` by `U`; so `h` and `φ` are
   defined on all of `M₁` and `K` is closed.
2. **Tolerance.** For compact `A ⊆ M₁` put `ε(A) = inf φ|A > 0`.
3. **Dual cells and the target cells `E_v`.** Take a regular neighbourhood `N` of `K` with dual
   cells `C_v`. If the subdivision of `M₁` is fine enough and `N` small enough, then
   **(1)** for each `v`, `h(C_v) ⊆ Int E_v` for some **polyhedral 3-cell** `E_v` contained in the
   `ε(C_v)`-neighbourhood of `h(v)` in `[M₂,d]`. **[ASSERTED]** — that a polyhedral 3-cell
   neighbourhood of the *topological* set `h(C_v)` exists inside a prescribed metric ball. This
   is the step that localises everything into a chart of `M₂`, and it is where the consultant's
   "chart-transport" lemma belongs.
4. **Piercing alteration (Figure 35.1).** Given `C_v ∩ C_w = D_e` with `e = vw`, alter `C_w` to
   `C'_w` so that `C'_w` pierces `Int D_e` in a 1-sphere `J_e`. The union of the `C'_v` is still
   a neighbourhood of `K`, and `C'_w` can be kept in any neighbourhood of `C_w`, so (1) survives.
   **[ASSERTED]/figure** — the alteration is specified only by the figure.
5. **Annuli.** For each `e` choose small regular neighbourhoods `S_e, T_e` of `J_e` with
   `T_e ⊆ Int S_e`, so that `S_e ∩ Bd C'_v`, `S_e ∩ Bd C'_w`, `T_e ∩ Bd C'_v`, `T_e ∩ Bd C'_w`
   are annuli. Put `A_e = Bd C'_v ∩ T_e` (associated with `v`) and let `B_e` be an annulus in
   `Bd C'_w` with `T_e ∩ Bd C'_w ⊆ Int B_e`, `B_e ⊆ Int S_e`, `Bd B_e ⊆ S_e − T_e` **[corrected against the
   printed page: the last clause concerns `Bd B_e`; with `B_e` it would contradict the first]**
   (associated with
   `w`).
6. **Third collection.** Add each `S_e` to the corresponding `C'_v`, obtaining `{C''_v}`; since
   `S_e` may be taken in any neighbourhood of `J_e`, `{C''_v}` still satisfies (1).
7. **Application of 34.1.** For each `v` and each `ε_v > 0`, **34.1** supplies a PL
   homeomorphism `f_v : C''_v → M₂` that is an `ε_v`-approximation of `h|C''_v`.
   *The target is `M₂`, not `R³`.* The Euclidean statement of 34.1 (p. 239) is therefore used
   through the chart given by `E_v`: this is the transport step, and it is not written out.
8. **Conditions (2)–(8)** (pp. 249–250), each obtained by taking `ε_v`, `ε_w` small enough, with
   `A'_e = f_v(A_e)`, `T'_e = f_v(T_e)`, `S'_e = f_v(S_e)`, `B'_e = f_w(B_e)` — three uses of
   `f_v` and one of `f_w`:
   (2) `E_v ⊇ f_v(C''_v)` and `E_v ⊇ f_w(S_e)` for every `e = vw`;
   (3) `f_v(Bd C'_v) ∩ f_w(Bd C'_w) ⊆ Int A'_e ∩ Int B'_e ⊆ Int T'_e`;
   (4) one component of `Bd A'_e` lies in `Int f_w(C'_w)` and the other in `M₂ − f_w(C'_w)`;
   (5) `B'_e ⊆ Int S'_e` and `Bd B'_e ⊆ M₂ − T'_e`;
   (6) `⋃_v f_v(C'_v)` is a neighbourhood of `h(K)` and no `S'_e` meets `K`;
   (7) `T'_e` contains all but one component of `B'_e ∩ f_v(C'_v)` and all but one component of
   `B'_e − f_v(C'_v)`;
   (8) `A'_e` and `B'_e` are in general position: `A'_e ∩ B'_e` is a finite disjoint union of
   polygons at which the interiors cross.
9. **Global tolerance.** Because `K` is a locally finite complex, the `ε_v` can be chosen for
   all of `K` so that (1)–(8) hold simultaneously. **[ASSERTED]** — this is the whole
   local-to-global tolerance selection, in one sentence. (Note the quantifier order: the `ε_v`
   are chosen *after* the geometric family `{C''_v}`, `{A_e}`, `{B_e}` is fixed.)
10. **Lemma 1 (p. 250).** Every polygon `J ⊆ A'_e ∩ B'_e` either bounds a disk in `A'_e` and a
    disk in `B'_e`, or carries a generator of `H₁(A'_e)` and a generator of `H₁(B'_e)`. Uses
    **27.3**, conditions (3), (4) and the separation of the two components of `Bd A'_e`.
11. **Minimality condition (p. 250).** Forget the approximation origin of the `f_v`; regard
    `f_v(C'_v), S'_e, T'_e, A'_e, B'_e` as sets satisfying (2)–(8), and choose them so as to
    minimise the total number of components of all sets `A'_e ∩ B'_e`.
12. **Lemma 2 (p. 250).** Every component `J` of `A'_e ∩ B'_e` carries a generator of `H₁(A'_e)`
    and of `H₁(B'_e)`. Proof by a disk-swap producing a new 2-sphere that bounds a polyhedral
    3-cell inside `E_w` (by (2)), preserving (2)–(8) and contradicting minimality.
13. **Lemma 3 (p. 251).** Every set `A'_e ∩ B'_e` is connected. Same minimality technique.
14. **Endgame (p. 251).** Delete `f_w(C'_w) ∩ Int f_v(C'_v)` from `f_w(C'_w)` for every `v, w`.
    This gives polyhedral 3-cells `{D_v}` with `⋃D_v` a neighbourhood of `h(K)`, with
    `D_v ∩ D_w ≠ ∅` iff `v, w` are the end-points of an edge of `K`, in which case `D_v ∩ D_w` is
    a polyhedral disk, and with distinct such intersections disjoint. Then a **three-stage**
    extension, exactly parallel in spirit to §34's seven stages but much shorter:
    `Bd(C_v ∩ C_w) ↦ Bd(D_v ∩ D_w)`, then `C_v ∩ C_w ↦ D_v ∩ D_w`, then `C_v ↦ D_v`.
    By (2), the result is a φ-approximation.

### 4.3 Theorem 35.2 (p. 251) and what carries over

**Statement.** `M₁, M₂` PL 3-manifolds; `K` a polyhedral 3-manifold with boundary in `M₁`;
`h : K → M₂` a homeomorphism (into); `φ` strongly positive on `K`. Then there is a PL
homeomorphism `f : K → M₂` that is a φ-approximation of `h`.

**The two reductions, exactly as stated.**
* **(R1)** `K` can be moved into `Int K` by a PL homeomorphism as close to the identity as one
  pleases; hence one may assume `h` and `φ` are defined on an **open set `U` containing `K`**.
* **(R2)** As in 35.1, `U` may be chosen so that `K` is **closed relative to `U`**; the theorem
  then reduces to `K` closed in `M₁` and `φ ≫ 0` on all of `M₁`.

**The subdivision condition.** Subdivide `K` so that for every simplex `σ`,
`diam h(|St σ|) < inf φ | |St σ|`, where `St σ` is the set of simplexes of `K` meeting `σ`,
together with their faces. Note this is a condition on **stars**, not on single simplexes.

**The input.** Take a regular neighbourhood `N` of the 1-skeleton `K¹` and a PL homeomorphism
`f : N ↔ N' ⊆ M₂` which is a φ-approximation of `h|N` with `N'` a neighbourhood of `h(K¹)` —
and, crucially, for **every** `φ' ≫ 0` on `M₁`, `f` may be made a `φ'`-approximation. This is
35.1 with a free tolerance.

**What is said to carry over.** The transition 35.1 → 35.2 is declared to be essentially the
transition 33.1 → 34.1, "the argument in Section 34 treated the simplexes of `K` essentially one
at a time". **No further detail is given: pp. 251–252 contain no lemma, no construction, and no
list of the changes.** So the following differences are *not* addressed in the book and are the
actual content of the obligation:

1. `K` is a **3-manifold with boundary**, not a 3-cell. §34's Lemma 9 explicitly uses "`K` is a
   triangulated 3-cell" to run the link/chain argument; for a vertex on `Bd K` the link is a
   disk, and the chain of 2-simplexes must be re-established.
2. `K` is **locally finite**, not finite. Lemma 8's termination counts components and points
   over all `σ`; §34's measure is infinite for non-compact `K`.
3. The ambient is `M₁, M₂`, not `R³`. Lemma 5(7) and the `Y₀` selection on p. 245 both use the
   **unbounded component of `R³`**; neither has a literal meaning in `M₂`.
4. The tolerance is a **function** `φ`, not a constant `ε`; every "sufficiently small/close"
   in §34 must become a pointwise estimate, and the `ε/3` of Lemma 1(5) a function.
5. 34.1 is used through charts (as §35.1 already does at step 7), so `E_v`-type target cells are
   needed throughout the §34 argument too, not just in §35.1.
6. "One simplex at a time" is **not an induction over skeleta**: §34 performs one pass of seven
   extensions over a fixed decomposition indexed by the simplexes, after Lemmas 1–11 and
   Operations 1–2 have fixed the combinatorics globally. There is no inductive hypothesis, no
   tower of stages, and no agreement clause between consecutive stages.

---

## 5. Invariants: what Operations 1 and 2 must preserve

| Invariant | Established by | Preserved by Op. 1 | Preserved by Op. 2 | Consumed by |
| --- | --- | --- | --- | --- |
| `N`, `f₁` and Lemma 1(1)–(5) unchanged | Lemma 1 (from 33.1) | Lemma 6 (unargued: the operations move only `C_σ`, and Op. 1 keeps `Bd N''` fixed under the splitting) | Lemma 7 (unargued; Op. 2 moves points *on* `Bd N''` but keeps `Bd N''` setwise fixed) | everything |
| `J' = Bd σ'` carries a generator of `π(N''_σ)` (Lemma 2) | 30.8 | Lemma 6 (unargued) | Lemma 7 (unargued) | Lemma 4, hence Lemma 5(6) |
| 5(1) `C_σ` a neighbourhood of `Bd σ'` | Lemma 3 via 30.5, weakened from 5(1′) | Op. 1 explicitly retains a 3-cell that is a neighbourhood of `Bd σ'` — 5(1′) is **lost** here | Lemma 7 | stage 6 (`D''_σ ⊆ Bd C_σ` must still surround `Bd σ'`) |
| 5(2) `C_σ ∩ C''_v ≠ ∅` only for `v ∈ σ` | Lemma 4's smallness | Lemma 6, first explicit verification | Lemma 7 | Lemma 4, Lemma 9's chain argument, p. 245 interior clauses |
| 5(3) `Bd C_σ` in general position to `Bd N''` | Lemma 3 | Lemma 6 (unargued) | Lemma 7 (unargued) | Lemma 9 (`J` interior to `A''_v`) |
| 5(4) `Bd C_σ ∩ Bd N''` in general position to each `Bd D''_e` | Lemma 3 | Lemma 6 (unargued) | Lemma 7 (unargued) | Lemma 10, Lemma 11 |
| 5(5) distinct `C_σ` meet only in `Int N''` | Lemma 3/4 smallness | Lemma 6, second explicit verification | Lemma 7 | Op. 1's own hypothesis (`Int D_J` meets no `C_τ`), p. 245 |
| 5(6) `Bd C_σ ∩ Bd N''_σ ∩ Bd N''` carries a generator of `H₁(N''_σ)` | Lemma 4 | Lemma 6 (unargued) | Lemma 7 (unargued) | Lemma 9 (via the chain of `τ`'s), **Lemma 11** |
| 5(7) `w'` in the unbounded component of `R³ − [⋃C''_v ∪ ⋃C_σ]` | Lemma 5, with a sufficient smallness condition (asserted) | Lemma 6, third explicit verification, in two parts (adding `D_J`; the small splitting displacement) | Lemma 7 (unargued — and *not* covered by Op. 1's argument, since Op. 2 is not a small displacement) | **p. 245**, the `Int C''(σ³)` clauses, hence stage 7's injectivity |
| 5(8) `Bd C_σ` in small neighbourhoods of `σ' ∪ N''_σ` | Lemma 3, weakened from 5(8′) | Lemma 6 (unargued); 5(8′) is **lost** | Lemma 7 | the final ε-estimate (p. 246) |
| Op. 1 impossible | Lemma 8 (termination) | — | — | Lemma 9, Lemma 10 |
| Op. 2 impossible | Lemma 8 (termination) | — | — | Lemma 10 |
| link condition on the subdivision (interior of an edge never separates two vertices of `L(v)`) | choice of subdivision, p. 239 | untouched | untouched | Lemma 9, Lemma 10 |

The two clauses whose preservation is asserted with no argument at all and which are
**consumed in an essential way** are 5(6) under both operations and **5(7) under Operation 2**.
Those are the first places a formalisation will stall.

---

## 6. Where the tree stands

Tree = `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\`.
PROVED = no open hypotheses; CONDITIONAL = proved from named open `Prop`s; STATED ONLY = a
`def … : Prop` with no producer; ABSENT = no counterpart.

| Book item | Tree | Status |
| --- | --- | --- |
| 25.1 / 25.2 | `MoiseChain.lean:31` / `:36` | STATED ONLY / CONDITIONAL on `Moise251PLGeneral` (`LoopTheorem/MoiseChainPL.lean:541`) |
| 26.4 Loop theorem | `MoiseChain.lean:57` | STATED ONLY |
| 27.3 annulus dichotomy | — (`AnnulusBoundary/Capping/Complement/Components/Euler.lean` are infrastructure only) | **ABSENT** as a statement |
| 28.8 / 28.9 torus polygons | — (`TorusMeridian.lean`, `CombinatorialSolidTorus.lean:19` are infrastructure) | **ABSENT** as a statement |
| 30.2 separation | `Topology/Connected/Separation.lean` | infrastructure, unnumbered |
| 30.4 | `MoiseChain.lean:86` | CONDITIONAL on `Moise252` (`SphericalShellCompression.lean:88`), also from `LemmaTwoStatement` (`LoopTheorem/LemmaTwoEndpoint.lean:45`) |
| **30.5** | `MoiseChain.lean:92`; tame form `TameNestedCells.lean:34` | wild: STATED ONLY; **tame: CONDITIONAL on `Moise304`** — and the consultant's verdict that the tame form suffices for §34 Lemma 3 is consistent with the book (Lemma 3 builds `C₂` around `σ` and transports by the embedding `h`) |
| 30.6 | `MoiseChain.lean:118` | STATED ONLY, **no consumer — and none is needed**, since §§33–35 never cite 30.6 |
| 30.7 | `MoiseChain.lean:128` | STATED ONLY, no consumer. **Mismatch:** the book concludes "`S` is a combinatorial solid torus"; the tree concludes `HasCylindricalDiagram S` (`MoiseChain.lean:124`). `IsCombinatorialSolidTorus` exists at `CombinatorialSolidTorus.lean:19` and is not used here |
| **30.8** | `MoiseChain.lean:257` (`IsSpine` at `:250`) | STATED ONLY, no consumer. **Serious mismatch — see below** |
| **33.1** | `MoiseChain.lean:136` | STATED ONLY; faithful to p. 230 (finite, connected, 1-dimensional, no end-points rendered as `neighborSet ncard ≠ 1`, `IsConnected`, `∃ e, card = 2`) |
| **34.1** | `MoiseChain.lean:99` | STATED ONLY, **no producer and no consumer tree-wide**. Matches p. 239 (Euclidean, constant ε); what §35.1 p. 249 actually applies is the `M₂`-target form, i.e. 34.1 plus a chart transport that is absent |
| **35.1** | `MoiseChain.lean:191` | STATED ONLY. Deviation: the book asks φ merely strongly positive, the tree asks `ContinuousOn φ U` and pointwise positive — a strictly weaker deliverable; recoverable by the consultant's continuous-minorant remark |
| 35.2 | `Transition361.lean:251` | CONDITIONAL on `{Moise351, Moise352InwardPush 3, Moise352SkeletonExtension 3}` (`SkeletonReduction.lean:236`). The competing arrow `moise352_of_stageStep` (`CompactRelativeApproximation.lean:256`) rests on a hypothesis the tree itself records as refuted (`LocallyFiniteApproximation.lean:22-27`) |
| (R1) inward push | `SkeletonReduction.lean:158` | **compact case PROVED**: `IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`, `ControlledInwardPush.lean:554`, conclusion verbatim. Locally finite case ABSENT; the missing brick (a collar of the polyhedral boundary inside a PL manifold) is named at `ControlledInwardPush.lean:680-700`. The claim at `SkeletonReduction.lean:38-41` that no controlled push exists is **stale** |
| (R2) `K` closed relative to some `U` | ABSENT | small infrastructure (local compactness of a tower-carried set) |
| subdivision condition of p. 251 | `SkeletonReduction.lean:107` `exists_isSubdivision_diam_image_closedStars_lt` | PROVED **for a finite complex only**; the consumer is stated for locally finite `K`, so it does not currently feed it |
| §34 as a whole | `Moise352SkeletonExtension`, `SkeletonReduction.lean:208` | STATED ONLY, and it is `Moise352 n` (`Transition361.lean:251`) with two hypotheses inserted — so `Moise352 n → Moise352SkeletonExtension n` holds by pure weakening and nothing has been discharged |
| dual cells `C_v`, splitting disks `D_e` | `DualCells.lean` (712 lines): `mem_dualCell_faces_iff:66`, `IsCombinatorialManifold.isPLBall_dualCell:288`, `splittingDisk_space:302`, `splittingDisk_space_inter:356`; `DualCellDecomposition.lean` | **PROVED** (combinatorial layer) |
| general position | `GeneralPosition.lean` (5688 lines), `HalfSpaceGeneralPosition.lean`, `ArrangementGeneralPosition.lean`, `SingularGeneralPosition.lean` | **PROVED** infrastructure; not yet in the shape Lemma 3/5(3)(4) need (surfaces in a PL 3-manifold) |
| regular neighbourhood of `K¹` | `PolyhedralGraph.lean:271` `IsLocallyFiniteRegularNeighborhoodOf`, `:34` `IsLocallyFinitePolyhedralGraph`; `derivedNeighborhood*` modules | definitions PROVED; existence is the conclusion of `Moise351` |
| solid torus `N_σ`, spine, toroidal shell | `SolidTorus.lean:15`, `CombinatorialSolidTorus.lean:19`, `NeighborhoodSolidTorus.lean`, `CommonCircleSolidTorus.lean`, `TorusCompression.lean`, `MoiseChain.lean:112` `IsToroidalShell`, `:250` `IsSpine` | definitions PROVED; the §34 Lemma 2 configuration (a) – (f) ABSENT |
| `X(σ³,v)`, `C(σ³)`, `D_σ`, `W_i`/`X_i`/`Y_i`, `C''(σ³)` | ABSENT | — |
| Operations 1 and 2, Lemmas 6–10 | ABSENT | — |
| handlebody | **no occurrence tree-wide** | ABSENT |

### The `Moise308` mismatch (new; not in the consultant's digest)

Book 30.8 (p. 218): with `S₁ ⊆ Int S ⊆ Int S₂` nested solid tori, `Cl(S₂ − S₁)` a toroidal shell
and `S` a combinatorial solid torus, and `J` a spine of **`S₁`**, the loop `p_J` generates
`π(S)`. The tree's

```lean
def Moise308 : Prop :=
  ∀ (S J : Set (EuclideanSpace ℝ (Fin 3))),
    HasCylindricalDiagram S → IsSpine S J → ∀ hJS : J ⊆ S, ∀ x : J,
      Subgroup.closure (Set.range (FundamentalGroup.map ⟨Set.inclusion hJS, _⟩ x)) = ⊤
```

(`MoiseChain.lean:257`) takes `J` to be a spine of **`S` itself** and drops the nesting and the
toroidal shell entirely. With `IsSpine S J` unfolded (`MoiseChain.lean:250`) this says: if
`S ≃ₜ D² × S¹` and `J` corresponds to `{p} × S¹`, then `π₁(J) → π₁(S)` has image generating
`π₁(S)` — which is a **triviality** (the core is a deformation retract), provable outright, and
the hypothesis `HasCylindricalDiagram S` is unused. It is therefore **not** the theorem §34
Lemma 2 needs: there `J = Bd σ'` is a spine of the *inner* torus `S'₁` and the conclusion is
about the *middle* one `N''_σ`, and Moise's own remark on p. 218 ("every `S` as in Theorem 7",
"the difference will be important later") is aimed exactly at that use. `Moise308` must be
restated with the 30.7 nesting before it can serve Lemma 2.

---

## 7. Every place the book asserts without proof or argues from a figure

| Page | Claim |
| --- | --- |
| 239 | The opening reduction (push into `Int K`, extend `h` to a neighbourhood, compose back) |
| 239 | Existence of a subdivision satisfying the link condition |
| 240 | Lemma 1(2)–(4) hold "whenever `f₁` is sufficiently close" — unquantified |
| 240 | Lemma 2's configuration (a)–(f): existence of `S₁, S₂`, that `Bd σ` is a spine of `N_σ`, and the re-choice order |
| 240 | Lemma 3: arbitrarily small shell-separated 3-cell neighbourhoods of `σ`, and their transfer to `σ'`; "general position … in one of its usual senses" |
| 241 | Lemma 4's citation of "(4) of Lemma 1" for a statement that is Lemma 2 **[SLIP]** |
| 241 | Lemma 5's sufficient condition for clause (7) |
| 242 | Operation 1: that one of the two resulting 2-spheres bounds a 3-cell still surrounding `Bd σ'` |
| 242 | Lemma 6: clauses (1), (3), (4), (6), (8) and Lemmas 1, 2 not verified |
| 242 | Operation 2 is specified by Figure 34.1 and explicitly not defined as an isotopy |
| 242 | Lemma 7: "the verifications are all trivial" — the entire proof |
| 243 | Lemma 8: that alternating two operations with two separate counters terminates |
| 244 | Lemma 11 Case 2: "easily gives a contradiction"; and the 28.8 citation covers a dichotomy 28.8 does not state **[AMBIG]** |
| 244 | Source-side incidence facts about `X(σ³,v)`, `C(σ³)`, `D_σ` |
| 244 | Existence of an irreducible disk `D''_σ` in `Bd C_σ` with boundary on `Bd N''` |
| 245 | That `⋃_{σ ⊂ σ³} D''_σ` does not separate `R³` |
| 245–246 | Stage 2's cyclic-order compatibility; the missing stage for the splitting disks `D_e` **[AMBIG]**; the final ε-bookkeeping |
| 248 | 35.1 step (1): a polyhedral 3-cell `E_v` containing `h(C_v)` inside a prescribed metric ball |
| 248 | The piercing alteration `C_w ↦ C'_w` (Figure 35.1 only) |
| 250 | That the `ε_v` can be chosen for all of `K` at once |
| 251 | That the whole of §34 carries over to 35.2 — one sentence, no lemma, no list of changes |
