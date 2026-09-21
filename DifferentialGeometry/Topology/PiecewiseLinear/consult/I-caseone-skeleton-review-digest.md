# Digest — external review of `Skeleton/ClosedBranchCaseOne.lean` (snapshot `06a96eb1de64`)

Verdicts: 1 OK, 1 VACUOUS, **2 FALSE**. The final orientability exclusion is mathematically correct;
the chain to it is not. **Our docstring claim that marking transport was moved "inside item 8" is
not implemented:** item 8's conclusion forgets the connection to `τ`, `ρ`, `sheet`, and
`IsAdaptedBranchTube` does not even require `N.space ⊆ L.space`.

| Leaf | Verdict | Reason |
|---|---|---|
| `NormalSingularCellData.exists_isMarkedCrossingChartAt` (L4) | **OK — freeze** | two-sided crossing + the actual source collar; the genuine non-orientable Case 1 disk inhabits it |
| `exists_isAdaptedBranchTube` (L8) | **VACUOUS** | its full input is exactly the orientable Case 1 configuration, which is impossible; not testable on any tuple |
| `exists_isSheetExchange_of_isAdaptedBranchTube` (L9) | **FALSE** | external orientable tube with half-turn monodromy: every marked point goes to its opposite |
| `apply_apply_eq_self_of_isAdaptedBranchTube` (L10) | **FALSE** | external orientable tube with quarter-turn monodromy: `u² rᵢ = rᵢ₊₂` |

## Fixture (source side; also the source part of both counterexamples)
Möbius band `𝓜_ε = (ℝ × [−ε, ε]) / ((s+1, v) ∼ (s, −v))`, source annulus
`A = (ℝ/2ℤ) × [−ε, ε]`, `f([s], v) = ([s, v], v) ∈ ℝP² × I`, capped at `v = ε` by the complementary
disk of the band in `ℝP²`. Source `P` is a disk; the only double curve is `Γ = core × {0}`,
`J = f⁻¹Γ = (ℝ/2ℤ) × {0}`, `τ([s], 0) = ([s+1], 0)`. Ambient `M = ℝP² × S¹`; for
`NormalSingularCellData` take `BdM = B = f(∂P)` (arbitrary subsets there). Local coordinates
`(s, w, z)`, sheets `z = ±w`; `x = (z+w)/2`, `y = (z−w)/2` turns them into `y = 0`, `x = 0` with
both positive rays on the positive collar side. Its small adapted tube has reflection end map
`u(x, y) = (y, x)` — the shared non-degenerate test object of the repaired chain.

## The counterexamples to L9 and L10
`P_c = [−1,1]²`, `r₀ = (1,0)`, `r₁ = (0,1)`, `r₂ = (−1,0)`, `r₃ = (0,−1)`; PL mapping torus
`N_u = P_c × [0,1] / ((x,0) ∼ (u x, 1))`, an orientable solid torus. Glue **abstractly**: core of
`N_u` ↔ the actual branch `Γ ⊂ L`; the lateral trace `T_u` ↔ disjoint polygonal circles in a
nonsingular patch of `Z = f(P)`; nothing else. Realise the finite glued complex in a large `E`
(distinct vertices ↦ distinct basis vectors). Then `L.space ∩ N_u.space = Γ ∪ T_u`,
`Z ∩ ∂N_u = T_u`, every slice meets `Z` in exactly the four marked points: **every clause of
`IsAdaptedBranchTube` holds**, with `Γ` even the actual core. `u = −id`: `u rᵢ = rᵢ₊₂`, opposite
stays opposite under any parametrisation ⇒ L9 fails. `u(x,y) = (−y, x)`: `u² rᵢ = rᵢ₊₂` ⇒ L10
fails (and it *satisfies* L9's conclusion). The two conclusions are logically independent; both
must come from one stronger transport statement.

## The repair
1. **Freeze L4.**
2. **Replace L8** by an orientation-free, source-tracked producer: drop `(hor : IsOrientable 3 L)`
   from its binders and `IsOrientable 3 N` from the predicate; new predicate
   `IsSourceTrackedBranchTube L hD c J τ ρ N hN Pc hPc φ u r` = old cylindrical / four-point /
   end-map clauses **plus** `N.space ⊆ L.space`, `Γ ⊆ N.space \ (boundaryComplex 3 N).space`
   traversed once by the cylindrical parameter (a PL circle parametrisation `β : ℝ/ℤ → Γ`),
   **plus source realisation**: continuous `aᵢ : [0,1] → J`, `sᵢ : [0,1] → [−1,1] \ {0}` with
   `f (aᵢ t) = β [t]` and `φ (rᵢ, t) = ι (f (ρ (aᵢ t, sᵢ t)))`; the four pairs
   `(aᵢ 0, sign (sᵢ 0))` distinct; **alternating pairing** `a₀ 0 = a₂ 0`, `a₁ 0 = a₃ 0`,
   `a₀ 0 ≠ a₁ 0` (no sign assignment to indices 1, 3 — both cyclic orders stay allowed). It is
   testable on the non-orientable fixture (reflection tube, `u : r₀ ↔ r₁, r₂ ↔ r₃`).
3. **Tube orientability separately**, in the assembly, from ambient orientability and the actual
   inclusion / derived neighbourhood (the subdivision orientation producer exists).
4. **Both monodromy conclusions from one transport theorem.** Proposed interface:
   `BranchTime := Set.Icc (0:ℝ) 1`; `structure SourceRayTransport (p : X → loopCircle) (u) (r)`
   with `lift : Fin 4 → C(BranchTime, X)`, `side : Fin 4 → Bool`,
   `over_base : p (lift i t) = (t.val : loopCircle)`,
   `label_injective : Injective fun i => (lift i 0, side i)`,
   `seam : u (r i) = r j → lift i 0 = lift j 1 ∧ side i = side j` (the file's convention
   `φ (x, 0) = φ (u x, 1)`; it does **not** assume a lift ends at its deck partner). `seam` is
   *proved* from the realisation data: equal `D`-images of two collar points in `C \ J`,
   `doublePointPreimage D ∩ C = J`, injectivity of `ρ`.
   `SourceRayTransport.square_fixes_rays` (connected two-sheeted cover `p`, `hcard`, `hperm`):
   `∀ i, u (u (r i)) = r i` — a lift of one circuit in a connected double cover ends at the other
   fibre point; `seam` twice; `label_injective`. Sheet exchange: same hypotheses + cyclic
   parametrisation + the three pairing equalities. Suppliers: `branchProjection_isCoveringMap`,
   `branchProjection_fiber_encard_eq_two` transported along `β`; connectedness from the
   source-circle theorem; "no continuous section" is already recorded.

## Audit of our six departures from the design
1 collar sign reversed (`Ioc 0 1`, positive = `Q` side): correct. 2 charts indexed by the source
point: correct and necessary (not a global sheet numbering over `Γ`). 3 dropping the ill-typed
`IsPiecewiseAffineOn e`: correct as typing, but PL compatibility must come through
chart-coordinate statements or the simplicial pair (`ClosedBranchCaseOneTubeCarrier`). 4 dropping
item 5: the rejection is right, **the replacement is missing** — anchor one lift on an evenly
covered arc, enumerate the other by `τ`, compare only where the normal forms hold; its
consequences must be *retained in the tube's output*. 5 no cleanliness of `Q`: correct. 6
`FourArcSphere`: the theorem exists, but its application (actual four-arc parametrisations,
`hsep`, `hsep'`, `π (i+2) = π i + 2` at every branch vertex) is still an obligation.
Also: `hpre` is redundant given `hmc`.

**Most likely surprise after the repair:** the cyclic splice — a construction can preserve the
unlabelled four-page configuration while losing which source sheet and collar side each page is.
The half-turn and the quarter-turn isolate the two ways that loss defeats the argument.

## Follow-up review of the repaired skeleton (snapshot `b78a0d15cc11`, 2026-09-21)
`exists_isSourceTrackedBranchTube`: **OK — frozen.**
* `cyclic` (index order = cyclic order) and the `0–2`, `1–3` pairing of `realisation` are
  compatible. Möbius fixture: `x = (z+u)/2`, `y = (z−u)/2`, end map `U(x,y) = (y,x)`,
  `r = ((δ,0), (0,δ), (−δ,0), (0,−δ))`, `a₀ = a₂ = [t]`, `a₁ = a₃ = [t+1]`, signs `(+,+,−,−)`.
  `{0,2},{1,3}` = two sides of one source sheet; the monodromy is the **reflection** `(0 1)(2 3)`,
  not a quarter turn; `cyclic` does not ask `U` to preserve the order, nor `aᵢ 0 = aᵢ 1`.
* `derived` asks more than inclusion but is attainable: start from `Lc = restrict R Γ`,
  `N = derivedNeighborhood R Lc` for the common subdivision of `ClosedBranchCaseOneTubeCarrier`;
  **choose `R`, `N`, `φ` and the source arcs together** — an arbitrary small neighbourhood may have
  a boundary that folds back under the collar projection. Our docstring was wrong on two points
  (fixed): `derived` does not ask `Lc ⊆ R` nor `Lc.space = Γ`; and recording `derived` instead of
  `N.space ⊆ L.space` is an interface choice (a general equal-dimension restriction lemma via a
  common subdivision and `IsOrientable.of_le` would do), not a mathematical necessity.
* Labels must come from the alternating four rays of the crossing and be transported along the
  given collar; they cannot be chosen after the fact.
* **Substance of the leaf / most likely surprise:** the marked cell normalisation and gluing
  *relative to the given `ρ`*. The existing link/cylinder normalisation controls unmarked set
  images only, not the base-point projection to the same collar and the four continuous arcs.
* Fixture: the Möbius model capped in `ℝP² × I`, placed in the double `ℝP² × S¹` (closed ambient);
  a solid Klein bottle alone cannot carry the whole disk.
