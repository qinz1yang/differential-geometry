/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of the controlled form of Moise 35.1

The assembly `controlledGraphNeighborhood` proves the endpoint
`ControlledGraphNeighborhoodStatement` for real from the four leaves of this file; every `sorry`
is a leaf and none sits inside an assembly.  The chain is: the source cut diagram of a
subdivision together with the fine carriers (steps 1--5 of pages 248--249), the vertex stage
through the proved chart local `Moise341` (step 6, page 249), the edge stage carrying the
annulus package, conditions (2)--(8), Lemmas 1--3 and the deletion that produces the target
cells (steps 7--13, pages 249--251), the two control clauses of Section 34 Lemma 1(4) and
Lemma 2, and finally the locally finite pasting, which is proved in `Section34Frame` from
`exists_isPLHomeomorphInto_union_of_locallyFinite_pieces`.

Quantifier order is the content.  The triangulation `𝒦` and the carrier control `(η, H)` come
first, because Section 34 chooses them once for the whole approximation problem; only then the
prescribed neighbourhood `W` of the one skeleton and the free tolerance `ψ`, which Moise 35.2
supplies afresh; and the subdivision `𝒦'`, the cut diagram, the regular neighbourhood and `f₁`
stand in one existential, because Lemma 1's incidence clauses are read off a jointly chosen
neighbourhood and map and cannot be imposed on an arbitrary output of plain `Moise351`.

All vocabulary is now the one copy in `Section34Frame`: `Section34Label`, `IsPLCellOn`,
`section34Dim`, `section34Face`, the typed index sets, `Section34CutFrame`,
`Section34GraphFrame`, `Section34CarrierControl`, `CarriesFundamentalGroupOnto`, and the proved
exporters `exists_nhds_finite_of_subset_carriers` and
`exists_isPLHomeomorphInto_dualCellPaste`.  The earlier duplicates `Section34CutLabel`,
`IsControlledPLCell`, `section34CutDim`, `section34CutFace` are gone; a skeleton cannot be
imported, since the focused checker offers a module to importers only from a receipt with zero
diagnostics, so the shared names had to become a module of their own.

Index question for the external reviewer.  Dual balls and splitting disks are indexed by the
vertices and edges of the subdivision `𝒦'` lying in `graphSkeletonSpace 𝒦`, because only a
subdivision can put the regular neighbourhood inside the prescribed `W` and respect the free
tolerance `ψ`; face disks and residual balls are indexed by the triangles and tetrahedra of `𝒦`
itself, because `h '' simplexRim 𝒦 s` has to lie in the solid torus built from dual balls, which
is false for a triangle of `𝒦'` interior to a triangle of `𝒦`.  Mixed incidence is therefore
`Section34Incident`, membership of the `𝒦'`-vertices in the closed `𝒦`-simplex, and the digest's
exact flag `Pa ≃ {(t,v) : v ∈ t}` is read in that sense.  Whether the reviewer intends the same
reading is not settled.

No forgetful corollary to `Moise351` is proved, and it is not short.  Three things block it.
`Moise351` starts from an arbitrary `K` with `IsLocallyFinitePolyhedralGraph (n := 3) K`, closed
in `U`, whereas the endpoint starts from a triangulation of `U` whose one skeleton is the graph;
producing one from the other is the relative triangulation theorem, absent here.  `Moise351`
supplies only the tolerance, whereas the endpoint also asks for a carrier control, whose
existence needs `h '' U` to be a neighbourhood of each `h '' S_t`, that is invariance of domain
for `h`, and a locally finite carrier family; both are separate producers.  And `Moise351`'s
local finiteness of `K` is carried relative to `K` itself while the conclusion needs it relative
to `U`; with `K` closed in `U` the two agree, but that reduction is nowhere in the tree.

The Lemma 2 clause is `CarriesFundamentalGroupOnto J T`, that is `J ⊆ T` together with
surjectivity of `FundamentalGroup.map` of the inclusion at every base point of `J`.  For `J` a
polygon and `T` a solid torus this is exactly "J carries a generator of `π(T)`"; no singular
homology statement is used.

The leaves, with content and review state.

`exists_section34CutFrame` (steps 1--5, changed by the index decision, unreviewed): the
subdivision `𝒦'` of `𝒦` with the same realisation map, the cut frame, the regular neighbourhood
`N = ⋃ C_v` of the one skeleton of `𝒦` inside `W`, the assignment `car` of a simplex of `𝒦` to
every dual cell with `C_v ⊆ S_(car v)` and finite fibres, and the fine carriers `Q v` with
`h '' C_v ⊆ interior (Q v)`, `Q v ⊆ H (car v)`, pairwise distances in `Q v` below `ψ`, and the
separation `Q v ∩ h '' σ ≠ ∅ → Section34Incident v σ` that conditions (2) and (3) are read off.

`Moise341.exists_section34VertexApproximation` (step 6, unreviewed): conditional on `Moise341`,
which is an explicit hypothesis of this leaf and of the endpoint theorem, the piecewise linear
embeddings of the disjoint locally finite family of dual balls confined to the fine carriers,
with piecewise linear cell images.  Its intended supplier is the proved chart local
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`.

`exists_section34EdgeMatching` (steps 7--13, unreviewed): the alteration that makes the family
match along the splitting disks, that is `EqOn` on `C_v ∩ C_w` and the exact meet
`G v '' (C_v ∩ C_w) = G v '' C_v ∩ G w '' C_w`, still confined to the fine carriers, with the
union a neighbourhood of `h '' |𝒦¹|`.  This is the leaf most likely to be mis-sized: it carries
the piercing alteration, the `A_e`/`B_e` package, 27.3, Lemmas 1--3 and the minimality argument
in one statement.

`section34MeridianAndNeighborhood` (Section 34 Lemma 1(4) and Lemma 2, changed by the index
decision, unreviewed): for the pasted map, the vertex point clause, `h '' ∂σ ⊆ interior (T_σ)`
and the generator clause, for the triangles of `𝒦`.

Proved here, not leaves: the assembly, which in particular proves conditions (2) and (3) of
Section 34 Lemma 1 from the carrier separation and the combinatorics of the splitting disks, and
the `ψ` estimate from the fine carriers.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def ControlledGraphNeighborhoodStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ 𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U,
      IsCombinatorialManifold 3 𝒦.complex →
    ∀ (η : M₁ → ℝ) (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂),
      Section34CarrierControl U 𝒦 h η H →
    ∀ {W : Set M₁}, IsOpen W → graphSkeletonSpace 𝒦 ⊆ W → W ⊆ U →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
    ∃ (𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))) (f₁ : M₁ → M₂),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
        Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        Section34GraphFrame U W h ψ H 𝒦 𝒦' src car f₁

section Leaves

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {car : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34CutFrame [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (η : M₁ → ℝ) (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (hH : Section34CarrierControl U 𝒦 h η H)
    (hW : IsOpen W) (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hWU : W ⊆ U)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3)))
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
        Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
          (graphSkeletonSpace 𝒦) U ∧
        section34CutNeighborhood src ⊆ W ∧
        (∀ w, car w ∈ 𝒦.complex.faces) ∧
        (∀ w, src (.vertexBall w) ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
        (∀ t : Finset (EuclideanSpace ℝ (Fin 3)), {w | car w = t}.Finite) ∧
        (∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) ∧
        (∀ w, Q w ⊆ H (car w)) ∧
        (∀ w, ∀ x ∈ src (.vertexBall w), ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
        ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
          (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1 := by
  sorry

theorem Moise341.exists_section34VertexApproximation (h341 : Moise341) [T2Space M₁]
    [SecondCountableTopology M₁] [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w))) ∧
        (∀ w, G w '' src (.vertexBall w) ⊆ Q w) ∧
        ∀ w, IsPLCellOn 3 (G w '' src (.vertexBall w))
          (G w '' srcBd (.vertexBall w)) := by
  sorry

theorem exists_section34EdgeMatching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w)))
    (hGQ : ∀ w, G w '' src (.vertexBall w) ⊆ Q w)
    (hGcell : ∀ w, IsPLCellOn 3 (G w '' src (.vertexBall w))
      (G w '' srcBd (.vertexBall w))) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G' w) (src (.vertexBall w))) ∧
        (∀ w, G' w '' src (.vertexBall w) ⊆ Q w) ∧
        (∀ w w', EqOn (G' w) (G' w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        (∀ w w', G' w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          G' w '' src (.vertexBall w) ∩ G' w' '' src (.vertexBall w')) ∧
        (⋃ w, G' w '' src (.vertexBall w)) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
  sorry

theorem section34MeridianAndNeighborhood [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {f₁ : M₁ → M₂} (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w)))
    (hGQ : ∀ w, G w '' src (.vertexBall w) ⊆ Q w)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hagree : ∀ w, EqOn f₁ (G w) (src (.vertexBall w)))
    (hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    (∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (f₁ '' src (.vertexBall w))) ∧
      (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
        interior (section34FaceTorus (fun w => f₁ '' src (.vertexBall w)) s)) ∧
      ∀ s : Section34SimplexIndex 𝒦 3,
        CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1)
          (section34FaceTorus (fun w => f₁ '' src (.vertexBall w)) s) := by
  sorry

end Leaves

theorem controlledGraphNeighborhood (h341 : Moise341) :
    ControlledGraphNeighborhoodStatement.{u} := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh 𝒦 h𝒦 η H hH W hW hΓW hWU ψ hψc hψpos
  obtain ⟨hHint, hHsub, hHlf, hHdiam⟩ := hH
  obtain ⟨𝒦', src, srcBd, car, Q, hsubdiv, hmapeq, hframe, hN, hNW, hcarF, hcarS, hcarfib,
    hQint, hQH, hQsmall, hQsep⟩ :=
    exists_section34CutFrame hU hh 𝒦 h𝒦 η H ⟨hHint, hHsub, hHlf, hHdiam⟩ hW hΓW hWU ψ hψc
      hψpos
  obtain ⟨G₀, hG₀, hG₀Q, hG₀cell⟩ :=
    h341.exists_section34VertexApproximation hU hh hframe hQint
  obtain ⟨G, hG, hGQ, hcompat, hmeet, hGnbhd⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hQint hG₀ hG₀Q hG₀cell
  obtain ⟨hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, -, -, -, -, -, -, hsplit⟩ :=
    id hframe
  have hCclosed : ∀ w, IsClosed (src (Section34Label.vertexBall w)) := fun w =>
    (hcell _).isCompact.isClosed
  have hDclosed : ∀ w, IsClosed (G w '' src (Section34Label.vertexBall w)) := fun w =>
    ((hcell _).isCompact.image_of_continuousOn (hG w).continuousOn).isClosed
  have hsub : ∀ w, src (Section34Label.vertexBall w) ⊆ U := fun w =>
    (subset_iUnion src (Section34Label.vertexBall w)).trans hcover.subset
  have hsrcLF : ∀ x ∈ ⋃ w, src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 x,
      {w | (src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp hx
    obtain ⟨V, hV, hfin⟩ := hLF x (hsub w₀ hw₀)
    refine ⟨V, hV, Set.Finite.of_finite_image (f := fun w =>
      (Section34Label.vertexBall w : Section34CutLabelOf 𝒦 𝒦'))
      (hfin.subset ?_) ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw
    · intro a _ b _ hab
      simpa using hab
  have htgtLF : ∀ y ∈ ⋃ w, G w '' src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 y,
      {w | (G w '' src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    refine exists_nhds_finite_of_subset_carriers (h '' U) _ H car
      (fun w => (hGQ w).trans (hQH w)) (fun w => hHsub _ (hcarF w)) hcarfib ?_
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  obtain ⟨f₁, hf₁, hf₁G, hf₁im⟩ :=
    exists_isPLHomeomorphInto_dualCellPaste h (fun w => src (.vertexBall w)) G hCclosed
      hDclosed hG hcompat hmeet hsrcLF htgtLF
  have himg : ∀ w, f₁ '' src (Section34Label.vertexBall w) =
      G w '' src (Section34Label.vertexBall w) := fun w => (hf₁G w).image_eq
  have hf₁Q : ∀ w, f₁ '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [himg w]
    exact hGQ w
  have hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hrw : f₁ '' section34CutNeighborhood src =
        ⋃ w, G w '' src (Section34Label.vertexBall w) := hf₁im
    rw [hrw]
    exact hGnbhd
  obtain ⟨hvertexInt, hrim, hmeridian⟩ :=
    section34MeridianAndNeighborhood hU hh hframe hN hQint hG hGQ hf₁ hf₁G hnbhd
  refine ⟨𝒦', src, srcBd, car, f₁, hsubdiv, hmapeq, hframe, hN, hNW, hf₁, hnbhd, ?_,
    hvertexInt, ?_, ?_, hrim, hmeridian, hcarF, hcarS, hcarfib, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    refine hQsmall w x hw (f₁ x) (hf₁Q w ⟨x, hw, rfl⟩) (h x) ?_
    exact interior_subset (hQint w ⟨x, hw, rfl⟩)
  · intro e s hne
    obtain ⟨w, w', hww', hunion, hdisk⟩ := hsplit e
    have hwsub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w) := hdisk ▸ inter_subset_left
    have hw'sub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w') := hdisk ▸ inter_subset_right
    have hw : Section34Incident w.1 s.1 := by
      refine hQsep w s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w (image_mono hwsub hy₁), hy₂⟩
    have hw' : Section34Incident w'.1 s.1 := by
      refine hQsep w' s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w' (image_mono hw'sub hy₁), hy₂⟩
    change ((e.1 : Finset (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3)))
    rw [hunion, Finset.coe_union]
    exact union_subset hw hw'
  · intro w s hne
    obtain ⟨y, hy₁, hy₂⟩ := hne
    exact hQsep w s ⟨y, hf₁Q w hy₁, hy₂⟩
  · intro w
    refine union_subset ?_ ((hf₁Q w).trans (hQH w))
    exact fun y hy => hQH w (interior_subset (hQint w hy))

end DifferentialGeometry.Topology.PiecewiseLinear
