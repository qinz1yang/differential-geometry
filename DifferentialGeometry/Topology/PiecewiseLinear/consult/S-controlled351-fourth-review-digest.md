# Digest — fourth external review of `Skeleton/ControlledGraphNeighborhood.lean` (snapshot `7634bd42f12b`)

Marks: **[V]** checked by the lead; **[–]** not independently verified.
Two corrections first: the worker's worry about accumulation on `∂(h''U)` need **not** be excluded —
what must be excluded is accumulation at points **inside `h''U` that are not in the union of the
supports**. And the present preparation has **no outer torus**; the last leaf re-quantifies `c, S₂`
existentially and does not express "fix the outer torus, then approximate".

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34VertexPreparation` | **FALSE [V]** | it receives only `hQint` yet must put all `Q_v` incident to a triangle in one chart |
| `exists_section34PiercingPackage` | **FIX** | the present margins do not make approximations keep (2)–(7); and the output is not tied to the input `G` as a controlled perturbation |
| `exists_section34ProtectedCircleRemovalStep` | **FIX** | Lemma 1's homological input suffices; isolation of the operation from the other edges is missing |
| `exists_section34ProtectedCircleRemoval` | **FIX** | wrong ambient for the local finiteness of supports; the proved one-label descent drops the support-preservation conclusions |
| `exists_section34EdgeMatching` | **FIX** | `hQsep`, `hQlf` are passed correctly; the pre-selected outer torus and its protection through all stages are not in the interface |

## 1. Preparation
**Counterexample [V]** (lead read the leaf: hypotheses `hU hh hframe hN hQint` only; the
predicate's last field asks `∀ s, ∃ c ∈ maximalAtlas, ⋃_{w incident s} Q w ⊆ c.source`): `S³` with a
standard finite triangulation and dual cut, `U = M₁ = M₂ = S³`, `h` a non-identity PL symmetry, all
`Q_v = S³` — the field forces `S³ ⊆ c.source`. **Repair:** pass the common-chart control as
*produced data*, `hQchart : ∀ s, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, (⋃ (w) (_ : Section34Incident w.1 s.1), Q w) ⊆ c.source`;
its supplier is an additional controlled carrier choice, if necessary refined jointly with the cut.
(Lead's note: the natural supplier is P0 — carriers `H α` chosen as PL balls *inside charts*, with
`Q v ⊆ H s` for every incident triangle `s`; this strengthens `Section34CarrierControl` and the
output of the cut-frame leaf.)
**Margins.** The order geometry → `ε_v` → approximation is right; the list is too short. Two
separate bounds `ε_v < d`, `ε_w < d` do not stop the two sides from meeting after moving `d/2` each,
and the crossed carrier containment of (2) does not follow from each side's confinement. At least:
`∀ x ∈ ∂B_e, y ∈ T_e, ε_v + ε_w < dist (h x) (h y)`;
`∀ x ∈ S_e, ball (h x) (max ε_v ε_w) ⊆ interior (Q v) ∩ interior (Q w)`; a separation margin for the
forbidden part of (3); the **source-side inside/outside marking** of (4):
`A_{e0} ⊆ interior C'_w`, `A_{e1} ∩ C'_w = ∅`; the collar of (5); protection of the *whole* graph core
for (6); component / connecting-path certificates for (7). These geometric facts precede "take `ε`
small". Also: Moise's slight alteration (p. 248) does not claim `C_v ⊆ C'_v`; keeping that extra
inclusion needs its own verification — it is not a verbatim transcription.
The piercing package should consume the completed stability certificate and then make a
margin-preserving general position move. (Its present output is not required to be close to the
input `G`, so the insufficient margins are not yet a counterexample to the bare existence leaf.)

## 2. Single removal step
The three `CarriesFundamentalGroupOnto` fields suffice for Lemma 1: circle, annulus and solid torus
have `π₁ ≅ ℤ`; in `π₁(A_{e0}) → π₁(T_e) → π₁(S_e)` the first arrow and the composite are isomorphisms,
hence so is the second; `Sn e ⊆ Cc v` lets one transport along the *same* `G_v` — no need for
`G_w|S_e = G_v|S_e`. **Missing:** local finiteness does not make one operation avoid the annuli of
other edges. A producible sufficient repair: `∀ e d, e ≠ d → Disjoint (Sp e) (Sp d)` (with
`A'_d ⊆ T'_d ⊆ S'_d`, `B'_d ⊆ S'_d` this isolates); the producer chooses pairwise disjoint small tubes
first and puts their separation margin into the approximation. The local replacement must be
realised as the declared `G'`, not only as a set-level statement.

## 3. Simultaneous removal
"Locally finite inside `⋃ S'_e`" is not enough: pairwise disjoint thin boxes at heights `2⁻ⁿ` from
`(0, 2⁻ⁿ, 0)` to `(1, 2⁻ⁿ, 0)` are locally finite in their union; PL moves inside each send the first
point to the second; the paste fixes the origin and is discontinuous there. (Refutes the pasting
inference, not `hpack`.) **Repair:** local finiteness in `Y = h '' U`,
`hSpLF : LocallyFinite (fun e => {y : h '' U | (y : M₂) ∈ Sp e})`, and **fixed compact envelopes**
`hK : ∀ w, IsCompact (K w) ∧ Q w ⊆ K w ∧ K w ⊆ h '' U` — in the intended application
`K_v = H (car v)`, which the assembly has but does not pass. Each `K_v` meets finitely many supports,
each label is operated on finitely often, and `G_v(C''_v) ⊆ K_v` throughout: every `G v` stops
changing on all of `C''_v`, giving PL-ness **without any infinite composition on `M₂`**. Stronger
local finiteness alone, without envelopes, does not give this. And
`exists_section34PiercingConditions_count_le_one` currently *drops* the step's `EqOn`, core fixing
and other-annuli clauses; they must be kept in its conclusion to serve as the black box.

## 4. Joint producer
Exact meets, marker, rim and the homeomorphism-of-pairs certificate stay as joint outputs. Writing
`∃ G' ∃ S₂` at the end is not itself wrong; what is missing is that the **outer torus is chosen
before the universal quantifier over the input approximation and protected afterwards**. Data flow:
`(c_σ, S_{2σ}, J_{eσ}, geometric buffers) → ε → G → protected normalization → (G', S_{1σ}, T_{eσ}, Φ_σ)`,
recording beforehand `J_{eσ} = c_σ (h (∂σ))`, `IsSpine (S_{2σ}, J_{eσ})`, and carrying "the target
blocks lie in `Int S_{2σ}`" through all stages. After `J_{eσ} ⊆ Int T_{eσ}` one shrinks the outer
torus's product-core neighbourhood to choose `S_{1σ}`; `Φ_σ` is the restriction of the **same
chosen chart** (p. 240: outer first, inner afterwards).

**Missing obligations:** production of the common chart / outer torus control; complete stability
margins; isolated supports; a finite descent that keeps the support clauses. **Fixture:** fine
standard cut, `h = g ∘ ψ`, the book's pierced cells, pairwise disjoint small tubes, one removable
pair of transverse intersection circles on one edge. **Most likely surprise:** mistaking "finite
descent per label" for "each map is modified finitely often" without passing fixed compact
envelopes into the induction.

## Worker's due-diligence results (2026-09-21, before the fourth repair)
* **Margins — reviewer verified, with a partial disagreement.** `ε_v < d`, `ε_w < d` give only
  `ε_v + ε_w < 2d` (`ε_v = ε_w = 0.9 d` lets `G_w(∂B_e)` meet `G_v(T_e)`): sum bounds are needed
  wherever *two* approximations meet. Not everywhere: for (6) the second set is the fixed `h(K)` and
  for the marker clauses the second point is `h(core)`, so one-sided bounds are correct there and
  were kept.
* **Box model — verified as a refutation of the pasting inference**, not of `hpack`.
* **`K_v = H (car v)` — verified and now proved in the assembly** (compactness from the closed-ball
  carrier clause via `IsPLCellOn.isCompact`; `Q w ⊆ H (car w)`; `H (car w) ⊆ h '' U`).
* **`C_v ⊆ C'_v` — the book does not assert it** (p. 248; confirmed independently by
  `consult/T-section35-1-construction-digest.md`). The worker thinks it is nevertheless true under
  the additive-bump reading; conservative option taken: replaced by `C_v ⊆ C''_v`; no clause
  depended on the old inclusion.
* Honest limit found: the margins prove condition (2), the disjointness halves of (5), (6) and the
  disjointness of the supports for **every** `ε`-close family (`section34MarginConditions`, proved);
  the *interior-containment* halves of (3)–(7) need "an interior point of a compact PL 3-cell maps
  to an interior point of its image" — the same missing `IsPLCellOn` invariance-of-domain package
  that P6 and P8 need. They stay inside the package leaf.
* Deviation: `hSpLF` (local finiteness of the supports in the subspace `h '' U`) is a field of the
  package, not an input of the simultaneous leaf — `Sp` is fixed through all later stages, and the
  assembly could not prove it without a new star-finiteness clause on `𝒦'`.
