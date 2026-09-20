# A2 — answer digest (external consultant, 2026-09-20; reviewed branch head `5c079459d`)

Digest of the answer to `A2-section34-contracts.md`. The consultant checked printed pp. 204,
218, 239–246, 249–251. Statements are proposed contracts, not compiled Lean. His three
transcription corrections to `A-section34-lemma-list.md` were verified against the printed
pages by the lead ✓ and applied to that file.

## Corrections

1. **p. 245 ✓.** The "no third point" clause concerns `Bd D''_σ ∩ Bd D''_e`, not
   `Bd D''_σ ∩ Bd D''_{σ'}`. It is the **empty-sector condition on each splitting circle**, and
   it supplies the cyclic-order compatibility of stage 2. So row 2 of the seven-stage table
   *does* have a producer in the book (unnumbered paragraph); its proof must be formalised.
2. **p. 249 ✓.** `T_e ∩ Bd C'_w ⊂ Int B_e`, `B_e ⊂ Int S_e`, **`Bd B_e ⊂ S_e − T_e`**.
3. **p. 245 ✓.** The arcs cutting `W_i` are `W_i ∩ Bd Δ_σ`.
4. **Stage 5 has a second omission when the source has boundary.** For a single tetrahedron the
   patches `X(σ³,v)` and the splitting disks do **not** cover `Bd C_v`:
   `Bd C_v \ ⋃ Int D_e` is a sphere with three holes, cut by the three face arcs into two disks
   `X_v`, `Y_v`; with one incident tetrahedron the right side of
   `Bd C_v = ⋃ X_{tv} ∪ ⋃ D_e` omits `Int Y_v`. Repairs: work on an **open** source (below), or
   add the exterior patch `Y_v` for every boundary vertex and extend over it in stage 4.
5. **Lemma 9's "K is a triangulated 3-cell" is unnecessary**: the link-connectivity facts hold
   in every locally finite combinatorial 3-manifold with boundary.
6. **Operation 1 needs a cleanliness clause** `D_J ∩ Bd C_σ = J`; avoidance of the other `C_τ`
   does not imply it (a ball with a blind notch: a horizontal slice is an annulus whose outer
   disk meets the ball's boundary again). Choose an innermost polygon, or put (Clean) in the
   operation's input.
7. **Lemma 11 can be repaired without 28.9**: after Lemmas 9–10 a component of
   `Bd C_σ ∩ Bd T_σ` projects to a non-empty reduced circuit of the triangle cycle, winding
   `±k`, `k ≥ 1`, so every component is non-zero in `H₁(T_σ)`; apply 28.8 to the family; the
   union carries a generator, so `k = 1`. (Thm 28.10, same p. 204, is another route.)

## 1.1 Reduce to an open, boundaryless source — without changing `Moise352`

Apply the inward push with tolerance `φ/2` to get `p, q, W`; put `η y = φ (q y) / 2` on `W`
(continuous, positive, since `q W ⊂ K`). If `g : W ↪ M₂` is a PL embedding with
`d(g y, h y) < η y`, then `F = g ∘ p` satisfies
`d(F x, h x) ≤ d(g (p x), h (p x)) + d(h (p x), h x) < φ(q (p x))/2 + φ x / 2 = φ x`,
and the PL inverse on the image is the inverse of `g` followed by `q`. So the geometric DAG may
work on a locally finite triangulation of the **open** manifold `W`, where every vertex link is a
2-sphere. *(This is a genuine reduction: the open case is a special case of 35.2.)*

## The replacement DAG (on an open source `U`, `h : U ↪ M₂`, locally finite triangulation `𝒦`)

Notation: `V_v = C''_v`, `E_e = D''_e`, `γ_e = ∂E_e`, `T_σ = N''_σ = ⋃_{v ∈ σ} V_v`; preliminary
face balls `C_σ`; selected face disks `Δ_σ = D''_σ` and residual tetrahedron balls `R_t = C''(t)`
(these are **chosen**, not `f₁`-images). `∂` is always the intrinsic boundary.

**Source cut diagram (SC1–SC3)** — a PL regular-neighbourhood theorem, not an approximation
theorem: `N` with dual balls `C_v`, splitting disks `D_e`, `d_σ = closure(σ \ N)`,
`Q_t = closure(t \ N)`, `X_{tv} = Q_t ∩ C_v`; `C_v`, `Q_t` PL 3-balls; `D_e`, `d_σ`, `X_{tv}` PL
2-balls; `C_v ∩ C_w = D_e` (`e = vw`) or `∅`; `C_v ∩ Q_t = X_{tv}` (`v ∈ t`) or `∅`;
`Q_t ∩ Q_{t'} = d_σ` for a common face or `∅`; `∂C_v = ⋃ D_e ∪ ⋃ X_{tv}`,
`∂Q_t = ⋃ d_σ ∪ ⋃ X_{tv}`; `p_{σe} = ∂d_σ ∩ ∂D_e` a point, `a_{vσ} = C_v ∩ ∂d_σ` and
`I_{te} = Q_t ∩ ∂D_e` PL arcs with the labelled end-points; `∂X_{tv}` the alternating six-arc
cycle; all families locally finite.

| Node | Input | Output |
| --- | --- | --- |
| P0 controlled source diagram | `U, h, η` | locally finite triangulation, (SC1–SC3), chart carriers `H_α` locally finite in `h(U)` with `h(|St α|) ⊂ Int H_α`, `diam H_α < η` on `|St α|` (C0); later `h(C_v) ∪ V_v ⊂ H_v`, `h(Q_t) ∪ R_t ⊂ H_t` (C1) — **these two inclusions carry the whole final error estimate** |
| P1 controlled graph-neighbourhood selection | P0, 35.1 | a **joint** choice of `N, f₁` with (G): `h(|𝒦¹|) ⊂ Int N''`, the two incidence implications, `h(∂σ) ⊂ Int T_σ`, `h v ∈ Int V_v`, `π₁(h ∂σ) → π₁(T_σ)` onto. An arbitrary output of 35.1 cannot be frozen and declared to have these. |
| P2 torus generator transfer | P1, outer/inner torus certificate | Lemma 2 (see 30.8 below) |
| P3 initial face balls | P1–P2, ball interpolation, general position | the family `C_σ` with (F): PL 3-ball, `h(∂σ) ⊂ Int C_σ`, `C_σ ∩ V_w = ∅` (`w ∉ σ`), transversality to `∂N''` and `γ_e`, `C_σ ∩ C_τ ⊂ Int N''`, `H₁(∂C_σ ∩ ∂T_σ ∩ ∂N'') → H₁(T_σ)` onto; plus (Ext) and carrier containment. Initially also `h σ ⊂ Int C_σ` — **not retained after compression** (Lemma 5, p. 241). |
| P4a protected compression | a **clean** Operation 1 disk | replaces one `C_σ`, preserves the invariants (the homological clause must be an explicit conclusion), `c_σ⁺ ≤ c_σ − 1`, `p_σ⁺ ≤ p_σ` |
| P4b protected bigon slide | an Operation 2 bigon | replaces one `C_σ`, preserves the invariants, `c_σ⁺ = c_σ`, `p_σ⁺ = p_σ − 2` |
| P5 locally finite normalization | P3–P4, fixed locally finite carriers | a family admitting neither operation |
| P6 normal traces, exterior face disks | P5, link conditions | (D): `Δ_σ ⊂ ∂C_σ` a PL disk, `Δ_σ ∩ N'' = ∂Δ_σ ⊂ ∂T_σ ∩ ∂N''`, `∂Δ_σ ∩ γ_e = {p''_{σe}}`, `∂Δ_σ ∩ V_v = a''_{vσ}` one arc, different `Δ_σ` disjoint. (Exterior because an innermost circle's disk inside `N''` would lie in `T_σ`, contradicting the generator.) |
| P7 four-face recognition | finite configuration around one tetrahedron | (T1) `∂R_t = ⋃ X''_{tv} ∪ ⋃ Δ_σ`, `R_t ∩ V_v = X''_{tv}`; (T2) `R_t ∩ V_w = ∅` (`w ∉ t`), `R_t ∩ Δ_σ` = `Δ_σ` or `∅`; **(T3)** `I''_{te} := R_t ∩ E_e ⊂ γ_e` an arc with the two labelled end-points and **no other marked point in its interior** (the p. 245 clause) |
| P8 vertex-patch and pairwise recognition | P6–P7 on a finite star | (V) `∂V_v = ⋃ E_e ∪ ⋃ X''_{tv}` with the source incidences; (TT) `R_t ∩ R_{t'}` = `Δ_σ` or `∅` (nesting excluded by a vertex of `t` not in `t'`) |
| E1–E7 | the constructed pieces | the seven PL extensions |

**Uniform extension lemma (stages 3–7 and the splitting disks).** `F : A → B` a PL
homeomorphism; locally finite families of PL `d`-balls `P_i`, `Q_i`, `1 ≤ d ≤ 3`,
`P_i ∩ A = ∂P_i`, `Q_i ∩ B = ∂Q_i`, `F : ∂P_i → ∂Q_i` a PL homeomorphism,
`P_i ∩ P_j ⊂ A`, `Q_i ∩ Q_j ⊂ B`, `F(P_i ∩ P_j) = Q_i ∩ Q_j` ⇒ a PL homeomorphism
`F⁺ : A ∪ ⋃ P_i → B ∪ ⋃ Q_i` extending `F` with `F⁺ P_i = Q_i`.

**Stages.** 1 marked points `p_{σe} ↦ p''_{σe}`; 2 `⋃ ∂D_e → ⋃ γ_e` with `F(I_{te}) = I''_{te}`, by
the marked-circle sector lemma from (T3); **2b** (inserted) `D_e → E_e` by disk extension,
**chosen once per edge** and used by both incident vertex balls; 3 the arcs `a_{vσ}`; 4 the
patches `X_{tv}` (six-arc boundary cycles, (V)); 5 `C_v → V_v` (whole boundary already mapped);
6 `d_σ → Δ_σ`; 7 `Q_t → R_t`. Each stage agrees with the previous on the cumulative domain; the
final map is **not** required to equal `f₁` on `N`. By (C1) the stage-7 map approximates `h`.

**Marked-circle sector lemma.** Distinct labelled points `p_i ∈ S`, `q_i ∈ S'` on PL circles;
the source consecutive-sector graph a cycle or a path through all labels; for each edge `ij` a
target arc `J_{ij}` from `q_i` to `q_j` with no `q_k` in its interior; sectors with disjoint
interiors ⇒ a PL homeomorphism `S → S'`, `p_i ↦ q_i`, sectors onto the `J_{ij}`. **Generators
and crossing numbers alone do not give stage 2**: four longitudes on `∂(D² × S¹)` meeting a
meridian in source order `1,2,3,4` and target order `1,3,2,4` satisfy every numerical condition
and no circle homeomorphism realises the labelling.

## Q3 — Operation 2 preserves 5(6) and 5(7)

The bigon lies at a seam `e = vw` with `e < σ` (its end-points lie in `C_σ ∩ V_v ∩ V_w`, so
Lemma 5(2) puts `v, w ∈ σ`). **(Slide):** an ambient PL isotopy `H_s` with `H₀ = id`,
`H_s N'' = N''` (setwise), `H_s = id` on `h(|𝒦¹|)`, `H_s C_τ = C_τ` (`τ ≠ σ`),
`supp H_s ∩ N'' ⊂ Int_{N''}(V_v ∪ V_w)`, support compactly inside the carriers; on `∂N''` it
removes the two intersections with `γ_e` and changes no other. Put `C_σ⁺ = H₁ C_σ`.
5(6): `H_s T_σ = T_σ`, so the new trace is `H₁` of the old and the `H₁`-surjectivity is
conjugated. 5(7): with `O_t = ⋃_{a ∈ t} V_a ∪ ⋃_{τ < t} C_τ`, `O_t⁺ = H₁ O_t`, markers `h w` are
fixed, and a compactly supported homeomorphism carries the exterior component to the exterior
component (chart-locally: `H₁` fixes the outer collar of `H_t`).

## Q4

**Links.** `L` a finite triangulation of a 2-sphere or 2-disk, `G = L¹`: (Link-E) `G − a` is
connected for every edge `a` (replace the edge by the other two sides of a triangle on it);
(Link-V) `G − z` is connected for every vertex `z` (`|L| \ {z}` retracts onto the deletion
complex). Lemma 9 uses (Link-E); Lemma 10's returning-arc argument uses (Link-V).

**Rank.** `c_σ = #π₀(∂C_σ ∩ ∂N'')`, `p_σ = #(∂C_σ ∩ ⋃ γ_e)`, `r_σ = c_σ + p_σ`; (R1), (R2)
above; counters of other faces are unchanged; so `r_σ` strictly decreases whenever `σ` is
modified.

**Locally finite labelled normalization.** `I` countable, objects `C_i` in fixed compact
carriers `H_i` locally finite in `V`; (1) a move labelled `i` changes only `C_i`, keeps it in
`H_i`, strictly decreases `r_i ∈ ℕ`; (2) other ranks unchanged; (3) legality of a move with a
compact witness depends only on the objects whose carriers meet the witness; (4) each invariant
depends on finitely many labels and is preserved ⇒ a family satisfying the invariants and
admitting no legal move, each member obtained by finitely many moves. (Visit every label
infinitely often; a label changes at most `r_i` times; a legal move of the limit has a compact
witness meeting finitely many carriers, all eventually constant, so it would have been
performed.) A move may expose a move on another label — fair revisiting handles it. This is a
finite-change construction of pieces, **not** a tower of approximating maps.

**Chart-local exterior invariant.** For each tetrahedron `t` fix a PL chart ball `H_t ⊃ O_t`;
`Ext_{H_t}(O_t)` := the component of `H_t \ O_t` containing `∂H_t`;
(Ext) `w ∉ t`, `h w ∈ H_t` ⇒ `h w ∈ Ext_{H_t}(O_t)`. Sufficient: if `Int R_t` met a non-incident
`V_w`, the connected `Int V_w` would lie inside the sphere `∂R_t` with its marker.

**Relative target local finiteness.** (LF-Y) every `y ∈ Y = ⋃ Q'_i` has an open `O ∋ y` in `M₂`
meeting finitely many `Q'_i`; sufficient and non-circular: `Q'_i ⊂ H_i ⊂ h(U)` with `(H_i)`
locally finite in `h(U)`.

**Order of choices.** `η` → nested chart cover and subdivision → source control neighbourhoods
and outer tori → `λ` (a continuous minorant of the chart, containment and avoidance margins,
`λ < η/4`) → `(N, f₁)` → inner tori and face balls → protected operations → PL fillings.

## Q5 — the correct 30.8

The tree's `Moise308` is the spine-of-its-own-torus lemma *preceding* 30.8; its
`HasCylindricalDiagram` hypothesis is not needed for that conclusion. Add, do not change:

```lean
def Moise308Nested : Prop :=
  ∀ (S₁ S S₂ J : Set (EuclideanSpace ℝ (Fin 3))),
    IsTopologicalSolidTorus S₁ → IsTopologicalSolidTorus S₂ → IsCombinatorialSolidTorus S →
    S₁ ⊆ interior S → S ⊆ interior S₂ →
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) →
    IsSpine S₁ J → ∀ hJS : J ⊆ S, ∀ x : J,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x)
```

(`IsTopologicalSolidTorus S` suffices for the middle torus.) **Proof:** the shell gives a strong
deformation retraction `S₂ ↘ S₁`; `π₁ J → π₁ S → π₁ S₂` is an isomorphism of infinite cyclic
groups; the two maps are multiplication by `n, m` with `mn = ±1`. No existence theorem for an
intermediate torus is used: **30.6–30.7 are not needed.** Smaller consumer lemma: `S ⊂ T` solid
tori, `J ⊂ S`, `J` a spine of `T` ⇒ `π₁ J → π₁ S` is an isomorphism (same factorisation); it
avoids the shell when the construction supplies `IsSpine T J`. For the inner-torus route record
`IsSpine S₁ J` explicitly — "a neighbourhood of the loop and its half-stars" is not the
definition of a spine.
