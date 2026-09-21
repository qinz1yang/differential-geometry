# L. Consult — does the pairing seed exist? (the mathematical core of general position in the double)

*请用中文回答；Lean 标识符与公式保持原样。先给结论（存在 / 不存在 / 需加假设），再给证明或反例；
总长约 2000 字。*

**Where.** Repository https://github.com/liao9yuan/differential-geometry-dev, branch
`moise-integration`, `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/GeneralPositionInDouble.lean`,
leaf `exists_pairingStableSubdivision_in_adaptedChart` (after five statement reviews, digest
`consult/J-generalposition-skeleton-review-digest.md`; read its fourth and fifth sections).

**Setting (one step of the chart-by-chart normalization, Moise §25 Lemma 2).** `M` a compact metric
PL 3-manifold (the double), `D : S → M` a locally injective, at most two-to-one PL singular disk,
proper (`D⁻¹(BdM) ∩ S = ∂S`), lying on one side `C`. An adapted chart `ec` with `ℓ ≥ 0` on `C`,
`ℓ = 0` exactly on `BdM`. A cut-out piece `Rc ⊆ S` (finite PL surface with boundary) containing all
sheets through `closure W`, with physical boundary part `Lc = Rc ∩ ∂S` and a frozen outer collar
`Ac` whose image misses `closure W`; seam conditions `Rc \ Ω ⊆ Nb`, `Rc ∩ Nb ⊆ Ac`. A closed set
`Z ⊆ O` (`O` open) on which `D` already has PL normal double crossings
(`HasPLNormalDoubleCrossingAt`, boundary models on `BdM` included); `Z ∩ closure W` may be non-empty.
A whole-source control complex `T` and scales fixed beforehand.

**The seed.** We need: a finite subdivision `R` of `Rc` with `ec ∘ D` facewise affine, `τ > 0`, a
compact `K` with `D(Rc) ⊆ int K ⊆ K ⊆ V`, and a vertex map `φ_*` in the constrained parameter space
`P_R` (frozen vertices fixed, `Lc`-vertices in `ker ℓ`) together with `ρ > 0`, such that **every**
`φ ∈ P_R` within sup-distance `ρ` of `φ_*` is `τ`-admissible (others at positive height), keeps
`StarInj T` of the glued map `g_φ`, keeps the simplices with a frozen vertex off `ec(closure W)`,
and admits the **pairing certificate** near `Z ∩ K`: open `U ⊆ O`, `U' ⊇ Z ∩ K`, PL homeomorphisms
`χ : U → U'`, `ψ : S ∩ D⁻¹U → S ∩ g_φ⁻¹U'` on the *full* source preimage with `g_φ ∘ ψ = χ ∘ D` and
`χ(U ∩ BdM) = U' ∩ BdM`. `φ_*` need not be the unperturbed map.

**Questions.**
1. Does such a seed always exist? If yes, give the construction: in particular how to make the old
   crossings over `Z ∩ K` *stable under all small vertex moves* of the final `R` (the old crossing
   may be a "bent" normal crossing — rays `A: (1,0),(0,1)`, `B: (1,1),(−1,1)` — where a small
   translate of one sheet creates a tangency), while `Ac`, `Lc`, `StarInj T` and the error budget
   are kept. Is a preliminary *relative straightening* (making both sheets flat near the double
   curve inside the protected region) available within these constraints, and does it survive
   the final common subdivision (new free vertices must move independently)?
2. If it does not always exist, what is the cheapest change of the *induction* that avoids it —
   e.g. normalising charts in an order and with regions `W j` such that the protected `Z` never
   meets the support `K` except where both sheets are already flat in the current chart; or
   protecting `Z` by freezing (enlarging `Ac`) instead of by pairing; or replacing vertex
   perturbation by a PL ambient isotopy supported off `Z`?
3. For the boundary models (double arc ending on `BdM`): is there any additional obstruction?
