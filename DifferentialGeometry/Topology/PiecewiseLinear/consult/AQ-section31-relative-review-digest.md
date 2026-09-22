# Digest — relative general position in Section 31, 2026-09-21

External answer supplied by the owner during the lead handover. Marks: **[V]** checked
against the current Lean source or the explicit mathematical model; **[–]** not formalised
or independently established. Source checked at local commit `a84961963`:
`Skeleton/Section31CanonicalConfiguration.lean`, SHA256
`b341156283d0069c6a29ea2ece1bde6137d53800fa3406e054fc831631d7d1a4`.

## Verdict and due diligence

| Item | External verdict | Lead check |
|---|---|---|
| `Fits` | OK | [V] Exactly CST, `A ⊆ interior S`, and `S ⊆ U`; the leaf separately takes `IsOpen U`. |
| `PairGP` | OK | [V] Both crossing and finite disjoint polygon clauses are present. An empty index type correctly permits disjoint boundaries. No simultaneous normal form for the entire family is requested. |
| `exists_generalPosition_solidTorus_relative` | OK, freeze | [V] `F : Fin m → Set E3` is fixed before the existential choice of `S`; its entries may repeat or equal `S₀`. [–] A sufficiently small generic translation is the proposed proof, not a checked Lean producer. |
| Original L6 | Correct assembly | [V] Keep `S' 0`, choose `S₁` relative to it, then `S₂` relative to `![S' 0, S₁]`; `PairGP.symm` supplies both adjacent pairs. The extra first/third pair is harmless. |

[V] The compactness proof for `h '' A j` uses continuity of the embedding on `N` and
`A j ⊆ N`, not global continuity of `h`. Independent focused check on lease c at
`2026-09-22T04:13:43Z`: Lean exit 0, exactly nine leaf `sorry` warnings, no other diagnostics,
source stable. All eight still-sorried original leaf blocks are byte-identical both to HEAD
and to `5ec76cf74^`. The relative leaf is now **frozen**, but all nine current leaves remain
OPEN proof obligations. No disagreement with the external verdict was found.

## Section 32 interface

[V] The tower uses its existential ambient homeomorphism `φ`, not an unidentified original
map `h`. First choose the source tower and `φ`, then write
`B i = φ '' A i` and `V i = interior (φ '' S i)`.

[–] Proposed construction, not implemented: extract the single-torus producer already used
inside `moise311` (inner shell, `Moise307`, cylindrical-diagram/CST bridge), choose one seed
`R i` with `Fits (B i) (V i) (R i)` for every integer, keep all even seeds, and choose the odd
term at `2*k+1` relative to `![R (2*k), R (2*k+2)]`. One choice of the seeds and one choice of
all odd terms gives a single family; each triple is its restriction. There is no minimum
integer and no infinite perturbation process.

[V] The tower's `closureLower`, `closureUpper`, and local-finiteness fields concern the outer
sets `φ '' S i`. Pairwise general position cannot supply them. Nonadjacent disjointness and
avoidance of `Z` must follow from those fixed outer data and containment of the new tori.
The existing tower leaf need not gain a hypothesis once the relative theorem is actually
proved; a proposition definition or an import of a skeleton does not provide that proof.

## Non-degenerate model and remaining work

[V, mathematical check only] Put `ρ(x,y,z)=max(|x|,|y|)`,
`S₀={1≤ρ≤3, |z|≤1}`, `A={ρ=2,z=0}`, and
`U={1/2<ρ<7/2, |z|<3/2}`. Translate by `(1/10,1/5,3/10)` and take `F 0=S₀`.
Relative to the translated torus, points of `A` have radial coordinate in `[9/5,11/5]`
and height magnitude `3/10`; the translated torus lies in radial range `[4/5,16/5]`
and height range `[-7/10,13/10]`, so both containment margins are strict.
The point `(3,-14/5,0)` is a genuine crossing, with local planes `x=3` and `y=-14/5`.
[–] No Lean CST or full `PairGP` certificate for this model has been constructed.

Owed: the relative theorem proof, the extracted single-torus producer, the two-choice
assembly, and the controlled source tower. The most likely implementation gap is upgrading
edge/face crossings from a dimension count to the two-plane `HasPLCrossingAt` normal form.
