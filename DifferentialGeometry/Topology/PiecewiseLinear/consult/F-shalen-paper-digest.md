# F — Digest of Shalen 1984, read in full, against this tree

P. B. Shalen, *A "piecewise-linear" method for triangulating 3-manifolds*, Adv. Math. **52**
(1984) 34–80. Read cover to cover (journal pp. 34–80 = PDF pp. 1–47) on 2026-09-20 by the
Claude digest lane. Everything below is paraphrase in our own notation; page numbers are
**journal** pages. Lean paths are relative to
`DifferentialGeometry/Topology/` in the checkout `D:\differential-geometry-moise-int`.

Answers `F-shalen-route.md` Q1–Q5 and the lead's A–F request. Companion reading: the owner's
roadmap `main04.tex`, and `consult/A2-answer-digest.md`, `consult/D-answer-digest.md` Part 2.

**Target (p. 34, proved p. 78–79).** `M`, `M*` PL 3-manifolds (boundary allowed), `M*` metric,
`h : M → M*` a topological embedding with `h(∂M) ⊆ ∂M*` and `h|∂M` PL, `ε` any continuous
positive function on `M`. Then `h` is `ε`-approximated by a PL embedding agreeing with `h`
on `∂M`. This is our `PLApproximationManifold 3` endpoint, with `Q = ∂M` instead of a general
protected polyhedron; Prop 9.3 has the general protected `Q` for boundaryless `M`.

---

## A. Dependency graph, section by section

Notation: `𝒞` a reduced curve system; `(T,η)` a surface thickening; `|η| = η(T × I̊)`;
`T*` an η-interpolated surface; `ρ_M(ε)` the PL-Schoenflies filling scale (§0).

### §0 Preliminaries (pp. 35–37) — definitions and the external list

Regular neighbourhood meeting `∂` regularly; collar neighbourhood `c : T × I → M` with
`c(x,½) = x` and `c(T×I) ∩ ∂M = c(∂T × I)`; two-sidedness = having a collar; `|c| = c(T × I̊)`;
separation; `ε`-approximation, `ε`-homeomorphism, `ε`-isotopy.

`ρ_M(ε)` (p. 36): for **compact** metric PL `M` and `ε > 0`, PL Schoenflies gives `ρ > 0` such
that every PL 2-sphere of diameter `< ρ` bounds a PL 3-cell of diameter `< ε`; `ρ_M(ε)` is
declared to be *the largest such number `≤ ε`*. Always `ρ_M(ε) ≤ ε`.

Incompressibility (p. 37): two-sided PL surface `T ⊆ M` is incompressible if every PL disc
`D ⊆ M` with `D ∩ T = ∂D` has `∂D` bounding a disc in `T`. **Equivalent to π₁-injectivity**;
the non-trivial direction is Hempel Cor. 6.2, i.e. Dehn's lemma + the loop theorem.

Nielsen (p. 37), in Shalen's weak surface form: a homotopy equivalence between **closed** PL
surfaces of non-positive Euler characteristic is homotopic to a PL homeomorphism
(Hempel Thm 13.1 proves more).

### §1 Isotopies (pp. 37–43) — used only from §4 on

| # | Statement (brief) | Uses | Used by |
|---|---|---|---|
| Def | reduced curve system: closed PL 1-mfd in a closed PL surface bounding no disc and no annulus | — | §1, §4, §5, §6 |
| Def | `δ`-regular surface: every PL disc/annulus has all points `< δ` from its boundary | — | 1.1A, 4.6, 5.1 |
| **1.1A** | `𝓜` closed PL surface, `δ`-regular; `𝒞` reduced; `j : 𝒞 → 𝓜` PL embedding homotopic to the inclusion with `diam(C ∪ j(C)) < δ` ⇒ `j` extends to a PL homeo `J : 𝓜 → 𝓜`, PL `5δ`-isotopic to `id` | 1.2–1.6 | 4.7, 5.1 |
| Cor 1.1A | same without metric: `j` extends to `J` PL isotopic to `id` | 1.1A with `δ = diam 𝓜` | 4.7, 5.1 |
| **1.1B** | `𝓜` compact PL 3-mfd; `𝒞 ⊆ 𝓜` two-sided PL 2-mfd, all components **discs**; `j` restricts to `id` on `∂𝒞`; `diam(C ∪ j(C)) < ⅓ρ_𝓜(ε/3)` ⇒ `j` extends to `J` PL `ε`-isotopic to `id` rel `∂𝓜` | 1.2–1.6, **PL Schoenflies** | 8.1 |
| 1.1 | conjunction of 1.1A/1.1B, uniform in `n = 2,3` | — | §1 proof |
| Def | pushing-boundary `S = α ∪ β`, `α ⊆ J(C)`, `β ⊆ j(C)`, `α ∩ β = ∂α = ∂β`; pushing-region `D` (an `n`-cell, or an annulus when `n = 2`); good homeomorphism | — | 1.2–1.6 |
| 1.2 | `J ≃ id`, `J(Ĉ) ⋔ j(Ĉ)` compact `(n−2)`-mfd ⇒ a pushing-boundary exists; `n=2` a pushing-region exists | **Epstein [5] Lemmas 2.4, 2.5** (`n=2`); innermost-disc (`n=3`) | 1.1 proof |
| 1.3 | `diam(S ∪ J⁻¹S) < 3δ` for a good `J` | the choice of regular nbhd `𝒩` of `𝒞` | 1.4 |
| 1.4 | `S` bounds a pushing-region `D` with `diam(D ∪ J⁻¹D) < ε` | 1.3; `δ`-regularity (`n=2`); **`ρ_𝓜(ε/3)` + PL Schoenflies** (`n=3`) | 1.1 proof |
| 1.5, 1.6 | which components of `𝒞` a pushing-region can meet (`N_C ⊆ X_C` etc.) | definitions | 1.1 proof |
| — | proof of 1.1: induction on `r`-very-good homeomorphisms; **small general-position isotopy**, second derived neighbourhood `D̃`, extend `k : D̃ → D̃` by the identity | general position, derived nbhds | — |

### §2 Interpolated surfaces (pp. 43–46)

| # | Statement | Uses | Used by |
|---|---|---|---|
| Def | surface thickening `(T,η)`: `T` compact PL surface, `χ(T) ≤ 0`, `η : T × I → M*` a **topological** embedding; `|η| = η(T×I̊)` is open in `M*`, hence a PL 3-mfd | — | everywhere |
| Def | η-interpolated surface `T*`: **incompressible closed** PL surface in `|η|` separating `η(T×0)` from `η(T×1)` in the closed image | — | §2–§8 |
| 2.1 | every closed PL surface in `|η|` separates the closed image | **mod-2 intersection number + homotopy invariance** | 2.2, 2.3, 4.4 |
| Cor 2.1 | a closed PL 2-mfd in `|η|` either bounds a compact PL submanifold or separates the two ends | 2.1 | 4.4, 7.3, 7.5 |
| 2.2 | if a closed PL 2-mfd separates the two ends, some component does | connectedness, compactness | 2.3 |
| **2.3** | an η-interpolated surface **exists** | 2.1, 2.2, `χ` maximality, compression raises `χ` by 2, *geometric* incompressibility only — **no loop theorem here** | 4.4 |
| **2.4** | `T* ↪ |η|` is a homotopy equivalence; and `π₁(T*) → π₁(Q̄)` is iso for each component `Q` of `|η| − T*` | **Dehn+loop via Hempel 6.2**; **van Kampen**; **Kurosh amalgam intersection** `im A ∩ im B = im C`; asphericity of `χ ≤ 0` surfaces; **π₁-iso between aspherical spaces ⇒ homotopy equivalence** | 2.5, 4.2, 5.2 |
| **2.5** | any interpolated `T*` admits an **interpolated homeomorphism** `η′ : T → T*` (PL, homotopic to `η|T` in `|η|`) | 2.4, **Nielsen** | 4.2, 4.7 |

### §3 Straightening out surfaces (pp. 46–49) — the "no long fingers" mechanism

Hypothesis: `K`, `M*` compact PL 3-mfds, `K` connected, `η : K → Ṁ*` a topological embedding,
`𝒲 ⊆ K` a two-sided **incompressible** PL 2-mfd, `𝒩` a regular nbhd of `𝒲` in `K`.
Definitions of `𝒲`-region `ℛ`, `ℛ_#`, `ℛ_♭`, and of `(η,𝒲,𝒩)`-regularity of a compact PL
surface `S ⊆ η(K̊)`: for every `𝒲`-region `ℛ` and every compact PL surface `L ⊆ S` with
`∂L ⊆ η(ℛ̊_♭)`, either `L ⊆ η(ℛ̊_#)` or `L` carries a two-sided s.c.c. in
`η((Fr_K ℛ)_#)` not bounding a disc in `S`.

**3.1** (the only numbered result of §3). `S` compact PL surface, `π₁(S) → π₁(η(K̊))` injective,
`∂S ∩ η(𝒩) = ∅`, `S ∩ η(𝒩)` two-sided in `η(𝒩)` ⇒ there is a PL embedding `j : S → η(K̊)`
agreeing with the inclusion on `∂S` with `j(S)` `(η,𝒲,𝒩)`-regular; **if `π₂(K) = 0`, `j` can be
taken homotopic rel `∂S` to the inclusion**. Uses: general position, regular neighbourhoods,
compression discs (Dehn/loop via incompressibility), minimisation of `#π₀(∂W_j)`, `π₂(K) = 0`.
Used by: 4.4, 5.2. Printed proof contains the dimensional slip `main04.tex` already records.

### §4 Approximations on surfaces (pp. 49–55)

| # | Statement | Uses | Used by |
|---|---|---|---|
| 4.1 | `C` non-contractible two-sided s.c.c. in a PL surface `T`, `f : C → C′` homotopic in `T` to the inclusion ⇒ `C ≃ C′` (PL homotopic) | **cyclic cover of a surface is an open annulus**; covering homotopy | 4.2 |
| 4.2 | `B` non-contractible two-sided s.c.c. in `T`, `v` a regular nbhd: (i) `∃ B* ⊆ T* ∩ η(v̊×I̊)` two-sided non-contractible in `T*`; (ii) every such `B*` `≃ η(B)` in `|η|`; (iii) `B* ≃ η′(B)` in `T*` for every interpolated `η′` | 2.4, 2.5, 4.1, non-cyclic `π₁` of `χ ≤ 0` surfaces | 4.5, 4.7, 5.2, 5.3, 5.1 |
| Def | `𝓑`-region, **elementary** `𝓑`-region (interior = a component of `T − 𝓑`) | — | 4.3–4.7, 6.3, 7.2 |
| **4.3** | `(T,η)` in compact `M*`, `𝓑` reduced with `diam η(R×I) < δ` for each **elementary** `𝓑`-region `R` ⇒ there is a `2δ`-regular interpolated `T*` and an interpolated homeo `η′ : T → T*` that is a **`2δ`-approximation** to `η|T` | 4.4, 4.6, 4.7 | 6.3 |
| 4.4 | an `(η,𝒲,𝒩)`-regular interpolated surface exists (`K = T×I`, `𝒲 = 𝓑×I`) | 2.3, 3.1, 2.1, Cor 2.1, `H₂(·;ℤ₂)`, `π₂(T×I) = 0` | 4.3 |
| 4.5 | a curve `γ ⊆ T* ∩ η((B×I)_#)` homotopic into `η(R×I̊)` for a region `R` not containing `B` is contractible in `T*` | 4.2(ii), transversality of `H : S¹×I → T` to `∂R`, minimisation, reducedness | 4.6 |
| 4.6 | `(η,𝒲,𝒩)`-regular ⇒ `2δ`-regular in the §1 sense | 4.5, the `diam` hypothesis | 4.3 |
| 4.7 | `(η,𝒲,𝒩)`-regular `T*` ⇒ an interpolated homeo `η′` which is a `2δ`-approximation to `η|T` | 2.5, 4.2(i),(iii), **Cor to 1.1A**, PL homeos of 1-spheres | 4.3 |

### §5 Extending PL approximations to pretzels (pp. 55–61) — "pretzel" = possibly non-orientable handlebody

| # | Statement | Uses | Used by |
|---|---|---|---|
| Def | collar `c` **compatible** with `𝒫` and `𝒟`; **thickness** of a collar | — | 5.1, 6.3, 8.1 |
| **5.1** | `𝒫 ⊆ Ṁ` compact PL 3-mfd, `T` a component of `∂𝒫` with `χ(T) ≤ 0`, `𝒟 ⊆ 𝒫` proper 2-mfd with **disc** components of diameter `< δ`, `∂𝒟 ⊆ T` reduced, `c` compatible of thickness `< δ`, `h` an isometric topological embedding, `T*` a `δ`-regular `hc`-interpolated surface, `η′` a `δ`-approximating interpolated homeo, `T*` separates `M*` ⇒ `η′` extends to a PL embedding `T ∪ 𝒟 → 𝒫*` which is a **`23δ`-approximation** to `h|(T ∪ 𝒟)` | 5.2, 5.3, 4.2(iii), **Cor to 1.1A and 1.1A with `δ → 4δ`**, collar extension of a `20δ`-isotopy | 6.3 |
| 5.2 | for each component `E` of `ℰ` there is a PL disc in `h(E̊)` with non-contractible boundary in `T*` | 4.2(i), **van Kampen** (`π₁(𝒫*) ≅ π₁(h(𝒫₁))`, second assertion of 2.4), **Dehn's lemma**, 3.1 regularity | 5.3 |
| 5.3 | a family `(D*_{1,E})` of **disjoint** properly embedded PL discs, `∂D*_{1,E}` non-contractible in `T*`, `D*_{1,E}` in the `δ`-nbhd of `h(E)` | 5.2, **general position**, minimisation of `#π₀(⋃D*_E ∩ T*)`, innermost-disc surgery, `δ`-regularity, `χ(T) ≤ 0` | 5.1 |
| Cor 5.1 | qualitative version, **no metric estimate**: `η′ : ∂𝒫 → T*` extends to a PL embedding `∂𝒫 ∪ 𝒟 → 𝒫*` | 5.1 ("much easier") | 7.5 |

### §6 Heegaard structures (pp. 61–66) — the compact theorem

Def (p. 61): a **Heegaard structure** in a compact connected PL 3-mfd `M₀` is `⟨T, 𝒟⁰, 𝒟¹⟩` with
(i) `T ⊆ M₀` closed PL surface, `χ(T) ≤ 0`; (ii) `M₀ − T` has two components with compact PL
closures `P⁰`, `P¹`; (iii) `𝒟^i ⊆ P^i` compact PL 2-mfd with **disc** components;
(iv) `𝒟^i ∩ T = ∂𝒟^i`; (v) `𝒟^i ∩ T` are **reduced** curve systems in `T`; (vi) each component
of `M₀ − (T ∪ 𝒟⁰ ∪ 𝒟¹)` is the interior of a closed PL 3-cell. `T ⊆ Ṁ₀` is **not** stipulated.
Chambers; mesh = largest chamber diameter.

| # | Statement | Uses | Used by |
|---|---|---|---|
| **6.1** | every compact connected metric PL `M₀` has a Heegaard structure of mesh `< δ`, with (a) `T − ∂E` connected for every chamber `E`, and (b) some component of `M₀ − T` has manifold boundary exactly `T` | fine triangulation, **second derived nbhd of `K⁽¹⁾`**, **dual 2-skeleton `K⁽²⁾*`**, `χ(T) = 2χ(P⁰) = 2χ(K⁽¹⁾) ≤ 0`, `χ` of spheres-with-holes, barycentric subdivision | 6.3, 8.1 |
| **6.2** | `ε < ½ diam 𝒫`, `δ′ = ⅓ρ_{𝒫*}(ε/2)`; `X ⊆ 𝒫` compact subpolyhedron with each component of `𝒫 − X` the interior of a closed PL 3-cell `E` of diameter `< δ′` and `X − ∂E` connected ⇒ every PL embedding `h′_X : X → 𝒫*` which is a `δ′`-approximation to `h_𝒫|X` **extends** to a PL embedding `𝒫 → 𝒫*` which is an `ε`-approximation | **PL Schoenflies via `ρ`**, **PL ball extension (Alexander)**, diameter bookkeeping, connectedness of `X − ∂E` | 6.3, 7.5 |
| **6.3** | **the compact Approximation Theorem**: `M`, `M*` compact PL 3-mfds, `h : M → M*` topological, `M₀ ⊆ Ṁ` compact PL ⇒ `h|M₀` is `ε`-approximated by a PL embedding | `δ = (1/138)ρ_{M*}(ε/2)`; 6.1 (a),(b); 4.3; 5.1 with `δ → 2δ` (giving `46δ`); 6.2 with `δ′ = 46δ` | 9.1 |

### §7 Fitting PL approximations together on surfaces (pp. 66–73) — the longest section

| # | Statement | Uses | Used by |
|---|---|---|---|
| 7.1 | `A`, `A*` PL annuli, `h|∂A` a PL homeo onto `∂A*` ⇒ `h ≃ rel ∂A` a PL homeo `A → A*` | **relative PL approximation of *maps*** (not embeddings), regular nbhds, `π₂(S¹×I) = 0` | 7.4 |
| **7.2** | `δ ≤ ⅓ρ_{\|η\|}(ε/6)`, `diam η(T) > ε`, `𝓑` reduced with small elementary regions ⇒ `∃ α > 0` such that any two `α`-approximations `η′₁, η′₂ : T×I → M*` to `η` are related by a PL homeo `j : M* → M*`, PL `ε`-isotopic to `id` rel `M* − \|η\|`, with `jη′₁\|T = η′₂\|T` | 7.3, 7.4, 7.5 | 8.1 |
| 7.3 | for small `α`, PL annuli `A* ⊆ η(B̆_#×I̊)` with `∂A* = η′₁(B₊) ∪ η′₂(B₋)` disjoint from `η′₁(T₊) ∪ η′₂(T₋)` | seven conditions (i)–(vii) for small `α`, **general position**, minimal-intersection annulus, innermost disc, **incompressibility**, `H₂(·;ℤ₂)`, Cor 2.1 | 7.4 |
| 7.4 | a PL homotopy `ℋ : K×I → \|η\|` with prescribed behaviour on `T₊`, `T₋`, `𝓑×[¼,¾]` | 7.3, **homotopy extension property for polyhedral pairs**, 7.1, deformation retracts | 7.5 |
| 7.5 | a PL embedding `η″ : T×[¼,¾] → \|η\|`, an `ε/3`-approximation to `η`, agreeing with `η′₁` on `T₊` and `η′₂` on `T₋` | 7.4, interpolated-surface recognition (π₁-injectivity, `H₂(·;ℤ₂)`, Cor 2.1), **Cor 5.1**, **6.2** | 7.2 |

### §8 Fitting PL approximations together on compact manifolds (pp. 73–75)

**8.1.** `M`, `M*` compact PL 3-mfds, `M₀ ⊆ Ṁ` compact PL, `h : M → M*` topological. Then for
every `ε > 0` there is `α > 0` such that any two `α`-approximations `h′₁, h′₂ : M → M*` to `h`
satisfy `J ∘ h′₁|M₀ = h′₂|M₀` for some PL homeo `J : M* → M*` which is PL `ε`-isotopic to the
identity **rel `M* − h(Ṁ)`**. Proof in three stages: 6.1 + a thin collar + **7.2** match the
central surface (`j₁`); **1.1B** twice matches the two meridian systems (`j₂`); **Alexander
isotopies** inside the chambers match the 3-cells (`j₃`); `J = j₃j₂j₁`. Used by 9.1.

### §9 The general theorem (pp. 75–79)

| # | Statement | Uses | Used by |
|---|---|---|---|
| **9.1** | `M₃ ⊆ Ṁ₂ ⊆ Ṁ₁`, `K ⊆ Ṁ₃` compact polyhedron, `δ > 0` ⇒ `∃ α > 0`: every PL `α`-approximation `h′` to `h\|M₃` extends to a PL `δ`-approximation `h″` to `h\|M₂` **agreeing with `h′` on `K`** | **6.3** and **8.1** | Cor, 9.3 |
| Cor 9.1 | `h` PL near a compact `K ⊆ M̊₀` ⇒ `h\|M₀` is `δ`-approximated by a PL embedding **equal to `h` on `K`** | 9.1 | 9.2 |
| **9.2** | `M`, `M*` **boundaryless**; `P` a PL 3-submanifold with compact components, closed as a subset; `L` protected polyhedron with `h` PL near `L`; one `δ_C` per component ⇒ one PL embedding on `P ∪ L`, equal to `h` on `L`, meeting every `δ_C` | Cor 9.1, pairwise separation estimates, local finiteness | 9.3 |
| **9.3** | `M`, `M*` boundaryless, `Q ⊆ M` polyhedron closed as a subset, `h` PL near `Q`, `ε` continuous positive ⇒ `h` is `ε`-approximated by a PL map agreeing with `h` on `Q` | **alternating shells** `P = ⋃(N_{2i} − N̊_{2i−1})`, `S = M̄ − (P ∪ L)`, regular nbhds `R′ ⊂ R̊`, 9.1 per component of `R`, 9.2 on `P ∪ L`, distance estimates for injectivity | Approximation Thm |
| — | **Approximation Theorem**: reduce to `h` a homeomorphism, straighten on a pair of boundary collars (`J`, `J*`, `h₁` PL on `c(∂M×[0,½])`), then apply **9.3** on `Ṁ` with `Q = c(∂M×(0,¼])`, paste | 9.3, collars | — |

`main04.tex` is right that 9.3's printed word "homeomorphism" is stronger than the proof gives
(the construction yields a PL **embedding**; surjectivity needs a separate argument).

---

## B. External inputs, exact form, availability

Legend: **P** present and proved here; **PC** present but conditional/statement only; **A** absent.

| # | Input, exact form Shalen needs | Where used | Tree? | Size if absent |
|---|---|---|---|---|
| 1 | **Dehn's lemma**: a PL s.c.c. in `∂P` null-homotopic in `P` bounds a properly embedded PL disc. `P` compact, **boundary allowed, orientability NOT assumed** (§5's handlebody is explicitly "possibly non-orientable") | 5.2 **directly**; and through #2 | **A** — see §G. Neither `Moise252` nor `Moise264` is Dehn's lemma; the tree has no statement of it. Derivable only from the **normal-subgroup** loop theorem (Hempel Ex. 4.4), which the tree also lacks | medium on top of #2, **but it needs the `N`-form** |
| 2 | **Loop theorem**, only via Hempel Cor. 6.2: two-sided `T ⊆ M` incompressible `⟺ π₁(T) → π₁(M)` injective. Shalen never uses the normal-subgroup form **for this**, but see #1 | §0, 2.4, 3.1, 4.4, 7.3(vii), 7.5 | **PC** — `MoiseChain.lean:36` `Moise252` (boundary component, `IsOrientable`, finite), `:57` `Moise264` (interior two-sided surface, finite, **no orientability**); both conditional on three open producers. No `Incompressible` definition anywhere (`ToroidalShellCompression.lean:10` is a docstring word only) | see §G |
| 3 | **Nielsen (surface form)**: a homotopy equivalence between **closed** PL surfaces of `χ ≤ 0` is homotopic to a PL homeomorphism. Orientable **and non-orientable** | **2.5 only** | **A**. No `Nielsen`, no surface classification, no mapping-class API; not in Mathlib either | **chapter-scale, possibly multi-chapter** — the gate of the whole route |
| 4 | **3-dim PL Schoenflies**: a PL 2-sphere bounds a PL 3-ball | via `ρ_M(ε)`: 1.4, 6.2, 7.2, 8.1 | **P, unconditional** — `PiecewiseLinear/PLSchoenflies.lean:11` `IsPLSphere.exists_isPLBall_frontier_eq`; input proved at `SchoenfliesFoundations.lean:7` (not an axiom) | — |
| 4b | **PL ball extension / Alexander trick**: a PL homeo of 2-spheres extends over the bounded 3-cells | 6.2, 8.1 (`j₃`), 5.1 (collar) | **P/partial** — `PLSchoenflies.lean:7` `IsPLSphere.isSimplyEmbedded` (stronger: an ambient PL homeo fixed outside a chosen convex open set, `SimplyEmbedded.lean:9`); `BallGluing.lean:51`, `BoundaryDiskExtension.lean:11,39`, `AmbientExtension.lean` | small bridge |
| 4c | **A positive filling scale in a *manifold***: `ρ_M(ε)` for compact metric PL `M` | §0, then everywhere | **A** — #4 is stated in `EuclideanSpace ℝ (Fin 3)` only; and Shalen's definition is **ill-posed** (see C-1) | medium |
| 5 | **Epstein's two curve lemmas** ([5] Lemmas 2.4, 2.5): two homotopic embedded s.c.c. on a surface bound an annulus, resp. a disc | **1.2, `n = 2` only** | **A** | small–medium |
| 6 | **Amalgam intersection** (Kurosh [9] p. 32): `G = A *_C B` with injective edge maps ⇒ `im A ∩ im B = im C` | **2.4 only** | **A** as an identity. Infrastructure **P**: `VanKampen/AmalgamatedProduct.lean:225,236`, `Algebra/Group/AmalgamatedProduct.lean:15` (`pushoutI_existsUnique_lift`), `Algebra/Group/FreeProduct.lean` | small–medium (Mathlib `Monoid.PushoutI` normal form should give it) |
| 7 | **van Kampen** for a two-piece closed decomposition along a bicollared surface | 2.4, 5.2 | **P** — `Topology/VanKampen/*` incl. `TwoSidedCollarCover.lean`, `BoundaryCollarInjection.lean` | — |
| 8 | **mod-2 intersection of a loop with a closed surface + homotopy invariance**; `H₂(·;ℤ₂)` separation | 2.1, 4.4, 7.3, 7.5 | **partial** — `Connected/Separation.lean`, `Connected/TwoSided.lean`, `PiecewiseLinear/BoundaryHomology.lean`, `Homology/*`, `ToroidalShellHomology.lean`; the geometric intersection pairing not found | medium |
| 9 | **Asphericity recognition**: π₁-iso between connected aspherical spaces ⇒ homotopy equivalence; closed surfaces with infinite π₁ are aspherical; `π₂(T×I) = 0`, `π₂(handlebody) = 0` | 2.4, 3.1, 4.4, 7.1 | **A** by name (`Homology/HomotopyEquivalence.lean` exists; no aspherical API). Hurewicz **P**: `Homology/HurewiczOne.lean`, `FieldHurewiczOne.lean` (`HurewiczLowDegrees.lean` has a `sorry`) | medium–chapter |
| 10 | **Cyclic cover of a surface is an open annulus** | 4.1 only | **A**. Mathlib covering-space API reused elsewhere (`Covering/PLMapLift.lean`, `Covering/PLNeighborhoodLift.lean`, `FundamentalGroup/CommutativeCover.lean`) | medium |
| 11 | **Euler characteristic**: `χ(∂P) = 2χ(P)` for a compact PL 3-mfd; `χ` of spheres-with-holes; additivity; compression raises `χ` by 2 | 2.3, 4.4, 6.1 | **partial** — `EulerPolyhedra.lean:15,20,30,35,45`, `EulerUnion.lean:90` `eulerChar_union_add_inter`, `SurfaceEulerParity.lean:18` (parity only, **not** `χ(∂P)=2χ(P)`) | medium |
| 12 | **Regular / derived neighbourhoods**: existence, second derived, meeting `∂` regularly, dual cells, `N(K⁽¹⁾)` complement. **Uniqueness is never invoked in the paper** | §1 proof, §3, §5, 6.1, 9.3 | **partial** — `PiecewiseLinear/DerivedNeighborhood.lean:67` + retraction/homology files; `IsLocallyFiniteRegularNeighborhoodOf` (used in `MoiseChain.lean:191`). **Dual cells: A** | medium; dual cells chapter-scale (bundled with 6.1) |
| 13 | **Collars/bicollars**, with compatibility and **thickness** control | §5, 6.3, 8.1, §9, final proof | **partial** — `Collar/*`, `BicollarNeighborhood.lean`, `PiecewiseLinear/BicollarEmbedding.lean:92`, `CollarBoundary.lean`; thickness-controlled PL collar of a two-sided closed PL surface not found | medium |
| 14 | **General position / transversality**: surface ⋔ surface in a 3-mfd, map ⋔ a 1-mfd, small general-position isotopy | 1.1 proof, 4.5, 5.3, 7.3 | **PC** — the *same* open item as on the Moise side: `GeneralPositionInDoubleBufferedStatement`; partial: `ArrangementGeneralPosition.lean`, `CarrierPerturbation.lean` | chapter-scale (already counted on both sides) |
| 15 | **Isotopy extension** — **NOT NEEDED**. Shalen only extends by the identity across a regular nbhd or collar, plus the Alexander trick | 1.1 proof, 5.1, 8.1 | **A** (`IsotopyExtension`/`AmbientIsotopy`: zero hits) and **not required** | — |
| 16 | **Regular-neighbourhood uniqueness** — **NOT NEEDED** anywhere in the paper | — | **A** and not required | — |
| 17 | **Homotopy extension property for polyhedral pairs** | 7.4 explicitly | **A** by name; `Attachment/*`, `Morse/CellAttachment.lean` are adjacent | medium |
| 18 | **Relative PL approximation of *maps*** (a map, PL on a subpolyhedron, approximated by a PL map rel it) | 7.1 | **P, proved** — `MoiseChain.lean:214` `plMapApproximation`, `:228` `plPolyhedronMapApproximation`, `:243` `plManifoldMapApproximation` (relative, `EqOn g f Q`) | — |
| 19 | **Innermost-circle / innermost-disc surgery on surfaces in 3-manifolds** | 1.2, 3.1, 5.3, 7.3 | **partial** — `LoopTheorem/InnermostCleanDisk.lean`, `LoopTheorem/CutAndPaste.lean` (built for the tower, different shape) | medium |
| 20 | **Fine triangulation of a compact PL 3-mfd with small vertex stars; barycentric subdivision** | 6.1 | **P/partial** — `SimplicialApproximation.lean`, subdivision layer | small |
| 21 | **Locally finite families, compact exhaustions, regular nbhds closed as subsets** | 9.2, 9.3 | **P/partial** — `LocallyFiniteApproximation.lean`, `CompactFamily.lean`, and the A2/D-designed locally finite normalization | small–medium |
| 22 | **Handlebodies / Heegaard splittings** | §5, §6 | **A** — zero hits for `Handlebody`, `Heegaard` | chapter-scale |

---

## C. Terse-source risk — steps stated as evident that are real formal work

1. **`ρ_M(ε)` is not well defined as printed (p. 36).** "Of all such numbers which are `≤ ε`, the
   largest will be denoted by `ρ_M(ε)`." The set of admissible `ρ` need not be closed, so a
   largest element need not exist. Every estimate in §1, §6, §7, §8 chains through it
   (`⅓ρ_𝓜(ε/3)`, `(1/138)ρ_{M*}(ε/2)`, `⅓ρ_{𝒫*}(ε/2)`, `⅓ρ_{|η|}(ε/6)`, `½ρ_{P^i}(ε/9)`,
   `⅓ρ_{|hc|}(ε′/6)`). `main04.tex` Ch. 19 already flags this; the fix is a *chosen* admissible
   scale, and then **every printed inequality must be re-derived**.
2. **`ρ` is defined only for compact `M`, but 7.2 (p. 67) uses `ρ_{|η|}(ε/6)` with `|η|` open**
   (an open subset of `M*`). Likewise 6.3 (p. 65) needs `ρ_{M*}(ε/2) ≤ ρ_{𝒫*i}(ε/2)` and
   justifies it in one sentence via `diam T* > ε/2`. Both are genuine obligations.
3. **General position, four separate times, each in a different form.** p. 41 "alter `J` by a
   small general-position isotopy so as to guarantee that `J_t(Ĉ*)` and `j(Ĉ*)` intersect
   transversally in a compact, possibly empty `(n−2)`-manifold"; p. 53 "we may suppose that `H`
   is transversal to `∂R`" for a map `H : S¹×I → T`; p. 58 "we may take the `D*_E` to be in
   'general position'"; p. 68 "by moving the interior of `C₀` into general position". This is
   the same producer the Moise route is already blocked on.
4. **Innermost-disc arguments, five times, each with a different minimality.** p. 39 (`α` minimal
   with respect to inclusion among discs of `J(C) ∩ j(C)`); p. 48 (minimal `n_j = #π₀(∂W_j)`);
   p. 58 (minimal `#π₀(⋃_E(D*_E ∩ T*))`, with a two-case argument and a `χ(T) ≤ 0` appeal);
   p. 68 (minimal `#π₀(C₁ ∩ η′₂(T₋))` and then minimal `D₀ ⊆ η′₂(Ṅ′)`); p. 53 (minimal
   `#π₀(H⁻¹(∂R))`). Each needs: the surgered object is still embedded, still proper, still on
   the right side, still in the right relative homotopy class.
5. **Cut-and-paste on surfaces stated as "clearly".** p. 45, proof of 2.3: "`T*′ = (T* ∪ ∂E) − Å`
   is again a PL 2-manifold, separating ..., and `χ(T*′) = χ(T*) + 2`". p. 69: "we may replace
   `A*₀` by an annulus `A*` ... having `b₁` and `b₂` as boundary components". Both are the
   compression/annulus-exchange operations `main04.tex` Ch. 13 lists but the tree does not have.
6. **Taming inside a homotopy, p. 44 (proof of 2.1).** "`α` is homotopic to a curve `α′` in
   `η(T×(0,ε))` for any `ε > 0`; and we may take `α′` to be PL." This is a PL-approximation step
   inside an intersection-number argument and needs the intersection number to be invariant
   under the move.
7. **"Topologically an open 3-cell", p. 57.** Lemma 5.2 uses that `h(E̊)` is topologically an
   open 3-cell to conclude `B*` is contractible there — fine, but then van Kampen is applied to
   a decomposition of `h(𝒫₁)` whose pieces are described only by "`𝒫* ∩ Q̄ = T*`". The
   collared-van-Kampen bridge (`main04.tex` Ch. 11) is exactly the missing piece.
8. **Regular-neighbourhood choices that carry estimates.** p. 38 "we may clearly also choose `𝒩`
   so that for any components `C`, `C′` of `𝒞` for which `C ∩ j(C′) = ∅`, we have
   `N_C ∩ j(N_{C′}) = ∅`"; p. 52 "clearly we may choose the regular neighbourhood `N` of `𝓑` so
   that `η((R×I)_#)` has diameter `< δ` for every elementary `𝓑`-region `R`"; p. 60 "for any
   `α > 0` we may choose a collar neighbourhood `Γ` of `T*` in `𝒫̊₁` having thickness `< α`".
   Three distinct "choose a neighbourhood small enough" producers.
9. **`π₂(K) = 0` used as a slogan.** p. 49 refines 3.1 under `π₂(K) = 0`; p. 52 "note that since
   `χ(T) ≤ 0`, we have `π₂(K) = 0`" with `K = T×I`; p. 67 `π₂(S¹×I) = 0`. Each needs the
   asphericity API of #9 above.
10. **Local finiteness and injectivity in 9.2/9.3 (pp. 77–78).** The final injectivity argument
    is four lines of distance bookkeeping over an infinite alternating family
    (`δ_E`, `δ_C`, `α_E`, `p_D`, `R′ ⊂ R̊`). The tree has already been burned once on exactly
    this shape (`consult/D-answer-digest.md` Part 2: the frozen-stage lemma and the impossible
    stage-indexed carriers).
11. **The dimensional slip in §3** (`main04.tex` records it) and the apparent **misprint on p. 37**
    citing "[5]" (Epstein) for the amalgamation result, where p. 46 correctly cites "[9]"
    (Kurosh, p. 32).

---

## D. What Shalen replaces in the Moise route, and what he does not

**(a) Is Lemma 2 of the loop theorem still needed? Yes, in full, and slightly more.**
Shalen uses Dehn's lemma and the loop theorem as black boxes in these forms:
* Dehn's lemma **directly** in 5.2 (p. 57): a PL s.c.c. in the boundary of a compact PL 3-manifold,
  contractible in it, bounds a properly embedded PL disc.
* The loop theorem only through the incompressibility criterion (Hempel Cor. 6.2). **The
  normal-subgroup formulation is never used** — the ordinary-kernel form suffices.
* `M` is compact in every use site (`𝒫*`, `M*`, `K`), but `η(K̊)` and `|η|` are **open**, so
  compact localisation is needed — the tree's `Moise252`/`Moise264` both carry `Finite K.faces`.
* **Orientability is nowhere assumed.** §5 is titled "extending PL approximations to pretzels"
  and the definition on p. 55 allows "compact (but possibly non-orientable) handlebody".
  The tree's `Moise252` (`MoiseChain.lean:36`) carries `IsOrientable 3 K`, and the proved chain
  is `… ∧ OrientableCoverReductionStatement → Moise252`. So switching to Shalen **adds** a
  non-orientable obligation to that lane rather than removing anything from it.

So: the entire loop-theorem side of the project is preserved verbatim, and its three open items
(relative general position, the descent step's boundary branches and disjoint two-circle closed
case, the orientable exclusion of the one-circle case) are unaffected.

**(b) Does it avoid Moise §30–33 and §34's P3–P8? Yes, completely.**
There is no pseudo-cell, no canonical configuration, no 30.4–30.8, no spherical or toroidal
shell, no cylindrical diagram, no 33.1, no face ball, no protected compression, no bigon slide,
no tetrahedron or vertex recognition, no labelled PL-cell assembly. Shalen's §6 replaces the
whole of §34 with four moves: a fine Heegaard structure (6.1), approximate the central surface
(4.3), extend over the two meridian disc systems (5.1), fill the chambers (6.2). Consequently
these tree assets become **dead** on the Shalen route: `Moise308Nested` (`Moise308Nested.lean:351`),
`Moise304`/`Moise305`/`Moise305Tame` (`MoiseChain.lean:86,92`, `TameNestedCells.lean:27`),
`Moise306`/`Moise307`, `HasCylindricalDiagram`, spherical and toroidal shells, solid-torus
neighbourhoods of trivalent graphs, link connectivity, the marked-circle sector lemma, the source
cut diagram, chart-local 34.1, `Moise331`, `Moise341`.
These survive: PL Schoenflies and `IsSimplyEmbedded`; the uniform ball-family extension lemma
(reusable in 6.2 and 7.5); the tolerance-control layer; the locally finite normalization schedule;
the relative PL map approximation theorems; the van Kampen/amalgam layer; Hurewicz;
`Moise352InwardPush`/`Moise352Open`/`Moise352`.

**(c) Does it still need a controlled 35.1? No — and this is the biggest structural gain.**
Shalen takes the regular neighbourhood of the 1-skeleton (`P⁰` = second derived neighbourhood of
`K⁽¹⁾`, p. 62) as a **purely PL object with no approximation attached**. He never asks for a PL
homeomorphism close to `h` on it. All the approximation happens afterwards, on `T = ∂P⁰` (4.3)
and on the meridian discs (5.1). So `Moise351` (`MoiseChain.lean:191`) — and a fortiori the
*controlled* 35.1 that `consult/A2-answer-digest.md` P1 says cannot be obtained by freezing an
arbitrary output of 35.1 — **disappears entirely**. What replaces it is Lemma 6.1: dual cells,
`χ(∂P) = 2χ(P)`, connectivity of `T − ∂E`. That is real work but it is *uncontrolled PL
combinatorics*, not a controlled approximation producer.

**(d) Compact → non-compact with continuous `ε`, versus what the tree has.**
Shalen: 9.1 (relative on nested compact cores; quantifier order: outer error first, inner
tolerance second, prescribed inner embedding last) → 9.2 (one PL embedding on a locally finite
family `P ∪ L` with one tolerance per component) → 9.3 (**alternating shells**
`P = ⋃(N_{2i} − N̊_{2i−1})`, `S = M̄ − (P∪L)`, nested regular nbhds `R′ ⊂ R̊`) → boundary case by
a pair of collars.
Against the tree:
* `Moise352InwardPush 3` is **proved** (`Moise352InwardPushProof.lean:42`), and
  `moise352_of_inwardPush_of_open` plus `Moise352OfOpen.lean:41` give
  `Moise352Open 3 → Moise352 3`. This is functionally the same reduction as Shalen's boundary
  step at the end of §9 — reach the interior first, then work boundarylessly. **Keep it as is
  under either route.**
* `Moise352Open` (`OpenSourceReduction.lean:297`) is exactly the hypothesis shape of Shalen's
  9.3 restricted to `Q = ∅`. So Shalen's 9.3 would be the *producer* of `Moise352Open`.
* The tree's own non-compact assembly — `Moise352Stages` (`LocallyFiniteApproximation.lean:478`),
  `Moise352StageStep` (`CompactRelativeApproximation.lean:224`), `Moise352StageInjection`
  (`StageTransport.lean:469`) — was shown defective in `consult/D-answer-digest.md` Part 2
  (frozen-stage lemma; stage-indexed carriers impossible for every `η`). **Shalen's 9.2/9.3 is a
  published, refereed replacement of precisely that construction, in precisely the shape the
  consultant recommended ("No tower … locally finite carriers").** This is worth taking
  regardless of which compact machine is used.
* Price of admission: 9.1 needs **8.1**, which needs all of §7. The tree has nothing for either.
* Erratum to carry: 9.3's "homeomorphism" is an embedding.

---

## E. `main04.tex` — chapter list and fidelity

46 chapters + 4 appendices, all still "architectural role" boxes (no proofs written).

Part I: 1 topological manifolds/embeddings/isotopies · 2 paths and π₁ · 3 coverings, monodromy,
deck · 4 singular (co)homology · 5 van Kampen and amalgamated products.
Part II: 6 simplicial complexes · 7 subdivisions and PL maps · 8 stars/links/combinatorial
manifolds · 9 PL manifolds and pairs · 10 PL structures on covers · 11 collars, regular nbhds,
**handlebodies** · 12 PL isotopies and extension · 13 PL general position in dim 2, 3 ·
14 Euler characteristic, mod-2 intersection, separation · 15 metric control.
Part III (off the critical path): 16 Jordan/RMT/planar Schoenflies · 17 PL approximation of
surface embeddings.
Part IV: 18 PL balls, spheres, 3-dim Schoenflies · 19 controlled PL balls and local filling scales.
Part V: 20 the statements · 21 local triangulations and compatibility · 22 wildness and tameness.
Part VI: 23 curves, annuli, **reduced curve systems** · 24 compact surfaces, cyclic covers,
asphericity · 25 the covering tower · 26 incompressible surfaces, Dehn, loop · **27 Nielsen** ·
28 controlled alignment on surfaces (**1.1A**) · 29 controlled alignment of disc systems (**1.1B**).
Part VII: 30 thickenings and separating surfaces (**2.1–2.3**) · 31 homotopy type of an
interpolated surface (**2.4, 2.5**) · 32 regional straightening (**3.1**) · 33 controlled
approximation of the central surface (**4.3**) · 34 extension across meridian discs (**5.1**) ·
35 fine Heegaard structures (**6.1**) · 36 controlled chamber filling (**6.2**) · 37 PL
approximation on compact cores (**6.3**).
Part VIII: 38 annular bridges and coherence near a surface (**7.2**) · 39 coherence on compact
3-manifolds (**8.1**) · 40 relative approximation on nested cores (**9.1**).
Part IX: 41 protected approximation on locally finite families (**9.2**) · 42 boundaryless
noncompact approximation (**9.3**).
Part X: 43 gluing two PL structures on a compact manifold (**project bridge, not in Shalen**) ·
44 Moise triangulation · 45 Hauptvermutung · 46 smooth consequences.
Appendices: A boundary case (end of §9) · B Bing's stronger gluing · C concordance · D blueprint.

**Fidelity: high, and the errata are already right.** One chapter per Shalen result-cluster, in
Shalen's own order after the foundations. Verified improvements over the paper:
* splitting §1 into Chs. 28/29 is correct — 1.1A and 1.1B genuinely have different inputs
  (Epstein + `δ`-regularity versus PL Schoenflies + `ρ`);
* placing §1 *after* PL Schoenflies removes Shalen's forward reference to `ρ_M` in §0/§1;
* "the Hempel tower and Dehn–loop chapters do not consume Nielsen" (Ch. 24, 27) is correct —
  Nielsen is used exactly once, in 2.5;
* "the loop theorem is used in the next chapter … not in the maximal-Euler-characteristic
  construction itself" (Ch. 30) is correct — 2.3 uses only geometric incompressibility;
* "do not demand that all complementary regions have negative Euler characteristic" (Ch. 23) is
  correct — on a torus every complementary region of a reduced system is an annulus;
* Ch. 11's insistence on the **non-orientable** handlebody matches §5 exactly;
* the three recorded errata (ill-posed `ρ`, the §3 dimensional slip, embedding-vs-homeomorphism
  in 9.3) are all real;
* Ch. 43's diagnosis is the key one: Shalen proves approximation **between already-PL manifolds**
  and asserts (p. 35) without proof that this "implies the triangulation theorem and
  Hauptvermutung"; the local-to-global bridge is genuinely absent from the paper.

**Two places where `main04.tex` over-specifies.** Ch. 12 lists as endpoints "the PL isotopy
extension theorem in the forms later consumed" and "uniqueness of regular neighbourhoods up to
controlled ambient PL isotopy". From a full reading, **Shalen needs neither**: every extension in
the paper is by the identity across a regular neighbourhood or a collar, plus the Alexander trick
on 3-cells. Dropping both from Ch. 12 removes what would otherwise be a chapter of work.
Also missing from Ch. 5: the **Kurosh intersection identity** is stated there, good, but nothing
records that it is needed *only* in 2.4 — worth noting so it is not over-generalised.

**Chapters the tree already partly has**: 1–9 (foundations), 11 (collars, derived nbhds — not
handlebodies), 13 (partial), 14 (Euler for finite complexes; not `χ(∂P)=2χ(P)`), 15 (partial),
**18 (done, unconditional)**, 20 (`Transition361.lean:251`, `MoiseChain.lean`), 25–26 (the
tower/Dehn/loop lane, conditional and orientable-only), 40–42 (the inward push and open reduction
proved; the stage machinery is the wrong shape), 45 (Hauptvermutung consumer in the chain).
**Chapters with literally nothing**: 24 (asphericity, cyclic covers), **27 (Nielsen)**, 28, 29,
30–39, 43, and the handlebody/dual-cell half of 11.

---

## F. Verdict, with uncertainty

**Chapter-scale pieces remaining, (i) Moise §34–35 versus (ii) Shalen.**

*(i) Moise.* From `consult/A2-answer-digest.md` and `consult/D-answer-digest.md` Part 2:
**about 7** — (1) a *controlled* 35.1 / joint `(N,f₁)` selection (P0–P1); (2) the face-ball family
with (F)/(Ext) plus the two protected operations and the locally finite rank normalization
(P3–P5); (3) exterior face disks (P6); (4) tetrahedron and vertex recognition (P7–P8); (5) the
terminal locally finite labelled PL-cell assembly (E1–E7); (6) 30.8 / torus generator transfer;
(7) the loop-theorem lane's three open items. Plus `Moise331`, `Moise341`. Nature: mostly
*controlled* producers, each one an approximation statement with an error budget.

*(ii) Shalen.* **About 8–9**, of which 5–6 are genuinely new theory: (1) **Nielsen for closed PL
surfaces of `χ ≤ 0`, orientable and non-orientable**; (2) handlebodies, dual cells, Heegaard
structures with `χ(∂P)=2χ(P)` (6.1); (3) all of §7 → 8.1 (annular bridges and compact coherence —
seven printed pages, five lemmas, a nested error budget); (4) §1 (1.1A/1.1B and the six lemmas,
with the Epstein inputs); (5) §2–§4 (interpolated surfaces, the amalgam/asphericity package,
cyclic covers, regional straightening, reduced systems incl. the torus/Klein-bottle cases); (6) §5
(5.1–5.3); (7) a well-posed filling scale `ρ` in a manifold; (8) incompressible ⟺ π₁-injective;
(9) the same loop-theorem lane as (i), **plus** its non-orientable extension. Nature: mostly
*uncontrolled* geometric theory, with the control confined to §1, 4.3, 5.1, 6.2, §7.

**Three most likely statement-level surprises in Shalen's route.**
1. **Nielsen (Prop 2.5).** The dependency closure of Hempel Thm 13.1 is unaudited, and Shalen
   needs it for possibly **non-orientable** closed surfaces (the §5 handlebody is explicitly
   non-orientable, hence `T = ∂P⁰` in 6.1 may be non-orientable). Most quotable Nielsen
   statements are orientable-only. If Ch. 27 turns out to require surface classification plus
   mapping-class theory, it is a book by itself — and the tree and Mathlib have **zero**.
2. **`ρ_M(ε)` and everything downstream.** The definition is ill-posed (a largest admissible `ρ`
   need not exist); it is defined for compact `M` but applied to the **open** `|η|` in 7.2; and
   `ρ_{M*}(ε/2) ≤ ρ_{𝒫*i}(ε/2)` in 6.3 is justified in one sentence. Every constant in §1, §6,
   §7, §8 (`1/138`, `46δ`, `23δ`, `20δ`, `5δ + 2ε/3`, `⅓ρ(ε/6)`) is downstream of it. Expect the
   printed budget to need rebuilding, not transcribing.
3. **The `(η,𝒲,𝒩)`-regularity definition (§3) and reduced systems on `χ = 0` surfaces (§4).**
   Regularity is a nested quantifier over all `𝒲`-regions and all compact PL surfaces `L ⊆ S`
   with `∂L ⊆ η(ℛ̊_♭)`; 3.1's proof silently needs the surgered `j′` to remain an embedding,
   proper, two-sided, and in the right relative class, and §3 already contains a printed
   dimensional slip. 4.3's mesh hypothesis is on **elementary** regions only; on `T²` and the
   Klein bottle the existence of fine reduced systems is a separate proof, and Shalen never
   gives it. (Runner-up: Lemma 2.1's one-line taming step, p. 44.)

**Is a hybrid sensible? Yes, and narrowly.**
* **Take Shalen §9 (9.1/9.2/9.3) as the non-compact assembly under either compact machine.**
  `consult/D` proved the tree's stage machinery false; Shalen's alternating shells are the
  published, correct version of the same construction, and `moise352InwardPush_three` +
  `Moise352Open` already sit on exactly its interface. Cost: 8.1, hence §7.
* **Take Shalen Lemma 6.2 as the terminal assembly** in place of the "locally finite labelled
  PL-cell assembly" of `consult/D`. 6.2 is two printed pages, needs only PL Schoenflies (which
  this tree has **unconditionally**, `PLSchoenflies.lean:11`) plus diameter bookkeeping, and is
  strictly cheaper than a graded-face-poset induction in dimensions 1–3.
* **Do not adopt §2–§5 until Nielsen is settled.** Everything from 2.5 onward is conditional on it.

**Blunt answer to the lead's question.** *Nielsen + Epstein + Dehn is more work than Moise §34,
measured in what this tree would have to build.* Dehn's lemma is consumed by **both** routes, so
it is not a differential cost — but Shalen additionally needs it without orientability, which our
`Moise252` does not currently give. Epstein's two lemmas are bounded (small–medium). Nielsen alone
is plausibly comparable to the entire P0–P8 list, because there is no partial credit anywhere:
no surface classification, no mapping classes, no homotopy-equivalence API for surfaces, nothing
in Mathlib. Add §7 (compact coherence), which has no counterpart in the Moise plan at all, and
Shalen's near-term formalization cost is **higher**, not lower.

**Recommendation, with its uncertainty.** Do not switch the §34–35 side wholesale. Do adopt the
three Shalen components that are cheap and that fix known defects: **6.2** (chamber filling),
**9.2/9.3** (alternating shells), and the **erratum list** (`ρ`, §3, 9.3). Keep the loop-theorem
lane exactly as it is. Then run one scoping task on **Hempel Thm 13.1's dependency closure,
including the non-orientable case** — that single unknown decides whether the rest of Shalen is a
6-month detour or a 2-year one, and it is cheap to resolve.
*Uncertainty:* moderate-to-high, and it cuts against this recommendation in one respect. Moise
§34's remaining items are *ill-understood*: ten statements on that chain have already been found
false, and two rounds of external consultancy were needed before the DAG could even be stated.
Shalen's remaining items are *well-understood and large*. For a project repeatedly damaged by
terse sources, "large and refereed" may be worth more than "unknown and hand-drawn", and if the
Nielsen audit comes back cheap the balance flips to a full switch.
**(Section G below settles the Nielsen audit. It comes back cheaper than feared.)**

---

## G. Reconciling Hempel with Shalen and with this tree

Source: J. Hempel, *3-Manifolds*, AMS Chelsea reprint of the 1976 Annals Studies 86. Read:
Ch. 4 (pp. 39–51), Ch. 6 (pp. 58–63), Ch. 13 through 13.6 (pp. 136–144), plus the preface.
Printed page = PDF page − 16. Hempel works in the **PL category throughout** (Ch. 1 is his PL
summary: regular neighbourhoods, general position). Standing convention in Ch. 6: *surface*
means a compact connected 2-manifold, either properly embedded in `M` or contained in `∂M`.

### G.1 The loop theorem

**Hempel 4.2 (p. 39, after Stallings).** `M` **any** 3-manifold; `F` **any connected**
2-manifold **in `∂M`**; `N` a **normal subgroup** of `π₁(F)`; if
`ker(π₁(F) → π₁(M)) ∖ N ≠ ∅` then there is a proper embedding
`g : (B², ∂B²) → (M, F)` with `[g|∂B²] ∉ N`.
**Standing hypotheses: none beyond these.** No orientability. No compactness. No second
countability stated. `F` must lie in `∂M`, and `F` must be connected.
Hempel's tower form is **4.10 (p. 47)**, which adds the localisation `g(B²) ⊆ f(B²) ∪ U` for any
neighbourhood `U` of `Σ(f)` — Shalen never needs the localisation, but Hempel's own §3 (Lemma 3.1)
style arguments do.

**Is the tower proof orientable-only? No — decisively not.** Three independent confirmations:
* 4.2 and 4.10 carry no orientability hypothesis, while the *sphere* theorem 4.3/4.11 (p. 40,
  p. 50) explicitly does (`M` orientable), and Hempel remarks the sphere theorem is false as
  stated for non-orientable `M`.
* **Lemma 4.6 (pp. 43–44) treats the non-orientable case explicitly.** Its final clause says that
  if `f⁻¹(α(S¹))` is connected then the double curve `α` is orientation-reversing and `M` is
  non-orientable; Case 2 of its proof builds the regular neighbourhood `T` of `α(S¹)` as a
  **solid Klein bottle** and does the surgery there.
* Hempel's preface (p. viii) states the book's policy of extending results to non-orientable
  and/or bounded manifolds, and p. 39 names "orientability in the loop theorem" as an
  *unnecessary hypothesis* eliminated by post-Papakyriakopoulos work.

**How the tower avoids orientation covers.** The covers are **2-sheeted covers of the compact
regular neighbourhood `V_i` of `f_i(B²)`**, existing by **Lemma 4.9 (p. 47)**: a compact 3-manifold
with non-empty boundary, some component of which is not a 2-sphere, has a connected double cover
— proved from `H₁(V;ℤ₂) ≠ 0`, via `H₂(V,∂V;ℤ₂) ≅ H¹(V;ℤ₂)` (**Poincaré–Lefschetz duality mod 2**)
and the mod-2 Hurewicz map. Compactness is *manufactured* at each stage by passing to a regular
neighbourhood, so it is never a hypothesis on `M`. Termination (pp. 48–49): make `f₁,…,f_n`
simultaneously simplicial w.r.t. one fixed triangulation of `B²` (relative derived subdivisions
`K′ mod L`, `K″ mod L`, and `N(L, K″ mod L)` as the regular neighbourhood — his Thm 1.6/Cor 1.7),
then `X(f_i) = {(σ,τ) : f_i(σ̊) ∩ f_i(τ̊) ≠ ∅}` strictly decreases. At the top `∂V_n` is all
2-spheres, so `F_n` is **planar**, `π₁(F_n)` is normally generated by its boundary curves, and
since `N_n` is a *proper normal* subgroup some boundary curve `J` escapes it and bounds a 2-cell
in `∂V_n`. **Descent is by cut-and-paste (4.6, 4.7), never by projecting an embedded disc** — which
is exactly the trap `main04.tex` Ch. 25 warns about and the reason the tree's route felt forced
into the orientable case.

**Why the normal subgroup `N` is not decoration.** Lemma 4.7 (pp. 44–46) handles a simple double
**arc** and can only produce *two* maps `f₁, f₂` with `[f|∂B²]` lying in the smallest normal
subgroup containing `[f₁|∂B²]` and `[f₂|∂B²]`. Hempel says at the end of the 4.10 proof (p. 50)
that part (iii) of 4.7 is essential in the application. **So the `N`-form is forced by the arc
case; a proof that only ever tracks `N = 1` cannot run the induction.**

### G.2 Dehn's lemma

**Hempel 4.1 (p. 39).** `M` **any** 3-manifold; `f : B² → M` a map such that for some
neighbourhood `A` of `∂B²` in `B²`, `f|A` is an embedding and `f⁻¹(f(A)) = A`; then `f|∂B²`
extends to an embedding `g : B² → M`. No orientability, no compactness.
**Hempel derives it from the loop theorem, not conversely**: Exercise 4.4 (p. 40) — take `R` a
regular neighbourhood of `f(∂B²)` in `M` and apply 4.2 to `closure(M − R)`. That application uses
a non-trivial `N`, so **Dehn's lemma is downstream of the normal-subgroup form.**

**Shalen's use (Lemma 5.2, p. 57).** `B*` is an *already embedded* PL simple closed curve lying in
`T*`, a boundary component of the compact PL 3-manifold `𝒫*`, contractible in `𝒫*`; he needs a PL
disc `D₀* ⊆ 𝒫*` with `∂D₀* = B*` **exactly** (the rest of 5.2 locates `D₀*` by its boundary).
The loop theorem with `N = 1` does **not** supply this: it returns a disc bounded by *some*
essential curve, not the prescribed one. `𝒫*` may be non-orientable (§5's handlebody is
explicitly "possibly non-orientable"). So Shalen genuinely needs Dehn's lemma proper, for a
compact, possibly non-orientable PL 3-manifold with boundary.

### G.3 Corollary 6.2 and the incompressibility criterion

**Hempel's incompressibility (p. 58)** is *stronger* than Shalen's. `F` is incompressible in `M`
if **none** of: (i) `F` is a 2-sphere bounding a homotopy 3-cell; (ii) `F` is a 2-cell with
`F ⊆ ∂M`, or there is a homotopy 3-cell `X ⊆ M` with `∂X ⊆ F ∪ ∂M`; (iii) there is a 2-cell
`D ⊆ M` with `D ∩ F = ∂D` and `∂D` not contractible in `F`.
**Shalen's (p. 37) is clause (iii) alone.** For every surface Shalen applies this to,
`χ ≤ 0`, so (i) and (ii) are vacuous and the two definitions agree — but this must be recorded as
an explicit reconciliation, not assumed.

**Hempel 6.1 (p. 58).** `S` a compact 2-manifold in a 3-manifold `M`, each component either
properly embedded and **2-sided** in `M` or contained in `∂M`. If `ker(π₁(F) → π₁(M)) ≠ 1` for
some component `F`, there is a 2-cell `D ⊆ M` with `D ∩ S = ∂D` and `∂D` not contractible in `S`.
Proof: general position `f : (B²,∂B²) → (M,F)` with `f|∂B²` essential, minimise
`#π₀(f⁻¹(S))`, then **apply the loop theorem to `M` cut open along `F′`**.
**Hypotheses: no orientability, no compactness on `M`; compactness and 2-sidedness on `S` only.**
The interior case is reduced to the boundary case by cutting — this is the bicollar step
`main04.tex` Ch. 26 lists.

**Hempel 6.2 (p. 59).** `F` a **2-sided** incompressible surface in a 3-manifold `M` ⇒
`ker(π₁(F) → π₁(M)) = 1`. **No orientability, no compactness on `M`.** Two-sidedness is
necessary; Hempel gives 6.3 as the counterexample family (a 1-sided `P²` in an orientable `M`).
This is precisely the non-trivial direction Shalen cites on p. 37.

### G.4 Theorem 13.1 — the Nielsen input, and the best news in this digest

**Hempel 13.1 (p. 137, "The Analogue for Surfaces").** `F`, `G` **compact 2-manifolds** with
`π₁(F) ≠ 1`; `f : (F,∂F) → (G,∂G)` with `f_*` **monic**. Then `f` is homotopic through maps of
pairs to `f₁` with either (i) `f₁ : F → G` a **covering map**, or (ii) `F` an **annulus or Möbius
band** with `f₁(F) ⊆ ∂G`. If `f|J` is already a covering map on a boundary component `J`, the
homotopy can be taken rel `J`.
**No orientability hypothesis. Both boundary and closed cases are proved.** It is stated for
compact 2-manifolds only, which is exactly Shalen's setting.

**Deriving Shalen's form.** `F`, `G` closed PL of `χ ≤ 0` ⇒ `π₁(F) ≠ 1`; a homotopy equivalence
gives `f_*` iso, hence monic; (ii) is impossible because `F` is closed while an annulus or Möbius
band has boundary; so `f ≃ f₁` a covering map; a covering map between closed surfaces inducing a
π₁-**isomorphism** is one-sheeted, i.e. a homeomorphism. Hempel's ambient category is PL, so `f₁`
is PL. **That is Shalen's p. 37 statement, obtained in four lines from 13.1.**

**Does 13.1 hide a 3-manifold or loop-theorem dependency? No.** This resolves the worry recorded
in `main04.tex` Ch. 27 and App. C. 13.1 opens Chapter 13 as a purely 2-dimensional warm-up for
13.6; the dependency runs **13.1 → 13.6**, never back. Its proof (pp. 137–140) uses only:
* covering-space classification — the cover `G′` of `G` with `f′_* : π₁(F) → π₁(G′)` an
  isomorphism, and lifting `f` to `f′`;
* π₁-injectivity of boundary curves of a compact 2-manifold with `π₁ ≠ 1`, and homotoping a
  π₁-monic map of circles to a covering of circles;
* change-of-basepoint maps and a **finite-index** argument: the images of `(f′|J_i)_*` have finite
  index in `π₁(K)`, so the intersection does, so the relevant cover `F̃` is compact and hence an
  annulus — i.e. **recognition of the annulus/Möbius band by infinite-cyclic π₁**;
* a first-Betti-number induction `β₁(G₁) < β₁(G′)` after cutting `G′` along a properly embedded
  non-separating arc;
* for `∂G = ∅`: existence of a 2-sided non-separating s.c.c. in a closed surface `≠ S², P²`,
  and the fact that `π₁` of the cut surface is **free**, so a monic `f_*` cannot factor through it.

**Prerequisite theory absent from this tree**, in the order 13.1 needs it: subgroup-correspondence
for coverings of surfaces (partially reusable from Mathlib and `Covering/*`); π₁-injectivity of
boundary curves; **recognition of the annulus and Möbius band by π₁ ≅ ℤ** (needs enough surface
classification); first Betti number of a compact surface and its drop under cutting along a
non-separating arc (the tree has `Homology/BettiNumber.lean`, so this is a bridge not a build);
freeness of π₁ of a surface with non-empty boundary (the tree has `Algebra/Group/FreeProduct.lean`,
`FiniteFreeProductInduction.lean`); existence of a 2-sided non-separating s.c.c. on a closed
surface of `χ ≤ 0`. **Estimate: one chapter, not a book.** Nothing in it is a 3-manifold theorem,
nothing needs Dehn's lemma, the loop theorem, or the tower. This substantially lowers the
risk-1 estimate in §F: Nielsen is the *largest* new piece but it is bounded, published in full,
and orthogonal to everything the project is currently stuck on.

### G.5 Reconciliation table — Hempel vs. Shalen vs. this tree

| Item | Hempel's hypotheses | Shalen's use | Tree's statement | Strong enough? |
|---|---|---|---|---|
| **Loop theorem** 4.2/4.10, pp. 39, 47 | any 3-mfd, `F` connected in `∂M`, **normal subgroup `N`**, no orientability, no compactness | only via Cor. 6.2, on `\|η\|`, `η(K̊)`, `𝒫*` (some **open**), `M*` possibly **non-orientable** | `Moise252` (`MoiseChain.lean:36`): boundary component, **`IsOrientable 3 K`**, `Finite K.faces`, `N = 1` only | **No.** Three gaps: the `N`-form, non-orientability, non-compact/open ambient (compact localisation) |
| **Dehn's lemma** 4.1, p. 39; derived from 4.2 by Ex. 4.4, p. 40 | any 3-mfd, no orientability, no compactness | **Lemma 5.2, p. 57**, directly, with the boundary curve **prescribed**, on a compact possibly non-orientable `𝒫*` | **no statement in the tree**. `Moise264` (`:57`) is *not* Dehn's lemma | **No** — must be added, and its natural proof runs through the `N`-form |
| **Cor. 6.2** p. 59 (incompressible ⇒ π₁-injective) | any 3-mfd, no orientability, no compactness; `F` compact, **2-sided** | p. 37 and then 2.4, 3.1, 4.4, 7.3(vii), 7.5 | `Moise264` (`MoiseChain.lean:57`) is its **contrapositive for an interior two-sided surface**: `Finite K.faces`, `IsTwoSided L.space`, **no orientability** — and is the closest thing the tree has | **Nearly.** Right shape and right orientability; missing: the boundary-surface case, the `Incompressible` definition, the equivalence packaged as such, and non-compact `M` |
| **Thm 13.1** p. 137 (Nielsen input) | compact 2-mfds, `π₁(F) ≠ 1`, `f_*` monic; **no orientability**; closed and bounded both proved; PL category | p. 37, used **once**, in Prop 2.5 (p. 46), for closed PL surfaces of `χ ≤ 0` | **nothing** | **N/A** — one chapter to build, no 3-manifold prerequisites |

### G.6 Consequences for the project's current lane

1. **The orientable restriction on the Lemma 2 / loop-theorem route is self-imposed, not forced by
   the source.** Hempel proves the loop theorem for arbitrary, possibly non-orientable `M`, and
   handles the non-orientable case *inside* the double-curve surgery (4.6, solid Klein bottle),
   not by an orientation-cover reduction. `OrientableCoverReductionStatement`
   (`LoopTheorem/CoverReductionOrientable.lean:69`) buys the restriction that Shalen's §5 then
   refuses to accept. Worth re-examining before more is built on `IsOrientable 3 K`.
2. **`Moise264` is the more valuable of the two tree statements** for either route: it is the
   interior two-sided case, it already omits orientability, and it is the exact contrapositive of
   Cor. 6.2, which is Shalen's only structural use of the loop theorem.
3. **`Moise252`'s `N = 1` is a real limitation, not a simplification.** Hempel's arc case (4.7)
   needs the normal subgroup to close the induction, and Dehn's lemma needs it again (Ex. 4.4).
   If the tree's tower is genuinely running an `N = 1` induction, that is worth re-checking
   against 4.7(iii) — Hempel calls that clause essential.
4. **Two further external inputs surface from Hempel that §B did not list**: Poincaré–Lefschetz
   duality mod 2 (for 4.9's double cover — **absent from the tree**, no `PoincareDuality`/
   `Lefschetz` hits anywhere), and relative derived subdivision `K′ mod L` with
   `N(L, K″ mod L)` as a regular neighbourhood (Hempel Thm 1.6 / Cor 1.7), which is what makes
   the tower terminate. The tree's `derivedNeighborhood` (`DerivedNeighborhood.lean:67`) is the
   right object; the *relative-mod-`L`* version and the termination bookkeeping are not there.
5. **Nielsen is no longer the unknown it was in §F.** Revised risk order for Shalen's route:
   (1) `ρ_M(ε)` and the error budget; (2) §7 → 8.1 coherence; (3) §3 regularity and reduced
   systems on `χ = 0` surfaces. Nielsen drops to fourth: large, bounded, self-contained.
