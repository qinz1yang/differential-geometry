# Digest — external review of `Skeleton/Section34Terminal.lean` (snapshot `75001aafd9da`)

Verdicts: 1 FIX, **3 FALSE**. Corrections to our docstring: the four index types `Pa Ar Eg Mk` and
their projections are called "incidence sets", but **the code does not make them incidences**;
and Lemma 5(7) serves P7 (outer-side choice, exclusion of non-incident vertices), it is not what
P6 needs to pick exterior face disks.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34NormalFamily` | **FIX** | existence can hold, but the output does not express the real P0–P5 configuration |
| `exists_section34FaceDisks` | **FALSE** | allows an empty trace; the homology generator alone still does not give single transverse points |
| `exists_section34ResidualBalls` | **FALSE** | a carrier can exclude a whole target face disk that must be kept |
| `section34TargetRecognition` | **FALSE** | an abstract source cell decomposition does not give the eight label kinds Moise's typed incidences |

**What stays.** `face := {m | src m ⊆ src l}` is correct and, with strict dimension drop, boundary
decomposition and exact intersections, enough for the terminal assembly. The parent exporter is
correct but is a *terminal forgetful step*: P0 still needs `S_α`-level closed-star control,
chart-ball carriers and operation buffers; `N`, `f₁` are chosen jointly by P1.

## Counterexamples
* **P6, empty trace.** Standard locally finite cut diagram, target = a non-trivial PL translate;
  take each `fbl σ` a small 3-ball *outside* `N'' = ⋃ V_v`, pairwise disjoint. All face-ball clauses
  hold, both operations are impossible (no intersection curves), yet `Δ_σ ⊆ ∂C_σ`,
  `Δ_σ ∩ N'' = ∂Δ_σ` forces a PL 2-disk with empty boundary.
* **P6, 5(6) alone is not enough.** Outside a standard solid torus take a 3-ball thinning along the
  boundary whose trace is one primitive meridional PL circle `J` sharing a non-degenerate arc with
  some `γ_e`: the operations stay impossible, the only candidate boundary is `J`, single-point
  intersection fails.
* **P7, carrier.** Target diagram and face disks standard, `h x = x + a` with `|a|` larger than a
  cell diameter, `car (tetraBall t) = h(Q_t)`, vertex carriers `C_v ∪ h(C_v)`, `η` a larger
  constant: every hypothesis holds, but `Δ_σ ⊆ R_t ⊆ h(Q_t)` and `Δ_σ ⊆ Q_t`, `Q_t ∩ h(Q_t) = ∅`.
* **P8, untyped incidences.** `U = M₁ = M₂ = S³`; source: two hemispheres, the common `S²` cut into
  two cap disks `D₀, D₁` and two rectangles `d₀, d₁` (six edges, four vertices); all six edges
  labelled `Ar` with suitable projections, the four vertices projected to the four pairs
  `(D_j, d_i)`, `Tt = Pa = Eg = ∅`: all source clauses hold. Target: an unknotted solid torus split
  into two 3-balls meeting in two splitting disks, `Δ_i` disjoint meridian disks of the
  complementary solid torus. The source has `d_i ⊆ C_{v₀}`, so P8 asks `Δ_i ⊆ V_{v₀}` — contradicting
  exteriority. Not a hole in `hsourceInter`: it never promised Moise's typed incidences.

## The corrected interface
`Normal⁺ := Section34NormalFamily ∧ CutFrame ∧ GraphFrame ∧ Control ∧ Ext ∧ Trace`.
* **`CutFrame`**: the full SC1–SC3 of a locally finite combinatorial 3-manifold `K`, with **exact
  flags** `Pa ≃ {(t,v) : v ∈ t}`, `Ar ≃ {(σ,v) : v ∈ σ}`, `Eg ≃ {(t,e) : e < t}`,
  `Mk ≃ {(σ,e) : e < σ}`, triangle/tetrahedron flags and link conditions. `face` stays defined by
  source inclusion.
* **`GraphFrame`**: P1's jointly produced `N`, `f₁` and (G) — not a final global map.
* **`Control`, `Ext`**: fixed PL chart-ball carriers locally finite in `h(U)`:
  `S_α = ⋃_{v ∈ α} |St̄ v|`, `h(S_α) ⊆ Int H_α`, `H_α ⊆ h(U)`,
  `∀ x ∈ S_α, ∀ y z ∈ H_α, dist y z < η x`; and
  `O_t := ⋃_{v ∈ t} V_v ∪ ⋃_{σ < t} C_σ ⊆ Int H_t`, `h w ∈ Int V_w`,
  `w ∉ t → h w ∈ H_t → h w ∈ Ext_{H_t}(O_t)`. Supplied by P0/P1 and the protected operations; **not**
  recoverable from the parent exporter.
* **`Trace`** (the complete Lemma 11 certificate):
  `∂C_σ ∩ ∂N'' = ∂C_σ ∩ ∂T_σ = ⨆_{i < r_σ} J_{σi}` with `r_σ > 0`, each `J_{σi}` a PL circle
  crossing each `γ_e` (`e < σ`) transversally exactly once — non-empty, finite, disjoint; never a
  possibly vacuous `∀ component, ∃! p`. The *upstream* prepared predicate (P3–P5) keeps 5(1), 5(3),
  5(4), 5(7) and the surjection `H₁(∂C_σ ∩ ∂T_σ ∩ ∂N''; ℤ) → H₁(T_σ; ℤ)`; moving Lemma 11's
  conclusion into the terminal family shifts Lemmas 9–11 upstream, it does not remove them.
* **`Residual⁺`** (P7 additionally produces):
  `∂R_t = ⋃_{σ<t} Δ_σ ∪ ⋃_{v∈t} X_{tv}`; `∂I_{te} = {p_{σ₁e}, p_{σ₂e}}`,
  `{σ₁, σ₂} = {σ : e < σ < t}`; `∂X_{tv} = ⋃_{v∈σ<t} a_{vσ} ∪ ⋃_{v∈e<t} I_{te}`; the
  no-other-marked-point clause stays.

Leaf shapes: `exists_section34NormalFamily : inputs → ∃ data, Normal⁺ data`;
`exists_section34FaceDisks : Normal⁺ → ∃ disks, FaceDiskFamily`;
`exists_section34ResidualBalls : Normal⁺ → FaceDiskFamily → ∃ residuals, Residual⁺`;
`section34TargetRecognition : Normal⁺ → FaceDiskFamily → Residual⁺ → the recognition conclusion`.

**Missing obligations:** the complete cut/graph frame; the trace recognition of Lemmas 9–11; P7's
controlled sphere and marked-boundary production. **Fixture:** a fine-mesh standard cut diagram,
`h = g ∘ ψ`, `g` a non-identity PL translation, `ψ` non-PL supported inside one residual
tetrahedron and fixed on the graph neighbourhood, all eight label kinds present. **Most likely
surprise:** forgetting a terminal-forgettable geometric certificate too early and then believing
that exact source intersections can produce the target's namesake incidences.
