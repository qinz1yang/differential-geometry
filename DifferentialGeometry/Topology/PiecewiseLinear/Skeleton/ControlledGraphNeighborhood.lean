/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of the controlled form of Moise 35.1

The assembly `controlledGraphNeighborhood` proves the endpoint
`ControlledGraphNeighborhoodStatement` for real from the six leaves of this file; every `sorry`
is a leaf and none sits inside an assembly.  The endpoint is **not** a producer of
`Section34NormalPlus`: it supplies P1 only, that is the cut frame and the graph frame,
conditional on `Moise341`.  The carrier control of P0, the exterior clause and the Lemma 11
trace certificate remain obligations of the other half.

The realisation ambient `Ea` is universally quantified in the endpoint, next to the
triangulation it realises; it is never the chart model.  `LocallyFinitePLPieceIn Ea 3 M₁ U`
realises all of `U` inside `Ea`, so writing `EuclideanSpace ℝ (Fin 3)` there would exclude
`U = S³`.  `IsCombinatorialManifold 3 𝒦.complex`, `IsSubdivision 𝒦'.complex 𝒦.complex` and
`𝒦'.map = 𝒦.map` now sit inside `Section34CutFrame`, so the conclusion still carries them.

Quantifier order is the content.  The triangulation `𝒦` and the carrier control `(η, H)` come
first, because Section 34 chooses them once for the whole approximation problem; only then the
prescribed neighbourhood `W` of the one skeleton and the free tolerance `ψ`, which Moise 35.2
supplies afresh; and the subdivision `𝒦'`, the cut diagram, the regular neighbourhood and `f₁`
stand in one existential, because Lemma 1's incidence clauses are read off a jointly chosen
neighbourhood and map and cannot be imposed on an arbitrary output of plain `Moise351`.

Pages 248--250 are followed literally: the preparation certificates are fixed **before** any
map.  `Section34VertexPreparation` produces the enlarged cells `C''_v`, the confinement
`h '' C''_v ⊆ Int (Q v)` and the tolerances `ε_v` with `B(h x, ε_v) ⊆ Int (Q v)` on `C''_v` and
`ε_v < dist (h x) (h v)` for `x ∈ Bd C''_v`; only then does the chart local `Moise341` supply
maps `ε_v`-close to `h` on `C''_v`, which a map shrinking `C''_v` into a small tetrahedron
cannot be.  `Section34PiercingConditions` is conditions (2)--(8) with the annuli `A_e`, `B_e`,
the regular neighbourhoods `S_e ⊃ T_e` of the piercing circles and the two boundary circles of
each annulus.  Conditions (7) and (8) are stated as "all components off `T'_e` lie in one
component" and "the intersection is a finite disjoint family of polygons lying in the two cell
interiors"; the crossing in Moise's sense is recorded only through that last containment.

`h x = x + a` with `f₁ = id` and `Q_v = ℝ³`, the periodic translation that refuted the old
meridian leaf, is now excluded at the joint producer: the marker clause, the rim containment
and the nested-torus certificate are **outputs** of the last edge leaf, and `J ⊆ T` already
fails for it.  The generator clause itself is no longer a leaf:
`carriesFundamentalGroupOnto_of_nestedSolidTorus` is proved in `Section34Frame` from the
unconditional `moise308Nested`, transported along the certificate's homeomorphism of pairs.

No forgetful corollary to `Moise351` is proved, and it is not short.  `Moise351` starts from an
arbitrary locally finite polyhedral graph closed in `U`, whereas the endpoint starts from a
triangulation of `U` whose one skeleton is the graph; it supplies only the tolerance, not a
carrier control; and its local finiteness is carried relative to the graph, not relative to `U`.

The leaves, with content and review state.

`exists_section34CutFrame` (steps 1--5): reviewed 2026-09-21 OK, pending the lead's
due-diligence check; statement changed, by the realisation ambient and by the move of the
subdivision clauses into `Section34CutFrame`.  It produces `𝒦'`, the cut frame, the regular
neighbourhood `N = ⋃ C_v` of the one skeleton inside `W`, the assignment `car` with finite
fibres, and the fine carriers `Q v`.

`exists_section34VertexPreparation` (preparation certificates, new after review N, unreviewed):
the enlarged cells, the buffers and the tolerances, all before any map.

`Moise341.exists_section34VertexApproximation` (step 6, changed after review N, unreviewed):
conditional on `Moise341`, a piecewise linear embedding of each `C''_v` that is an
`ε_v`-approximation of `h` there.  Its supplier is the proved chart local
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`, whose shape it matches.

`exists_section34PiercingPackage` (the piercing alteration and conditions (2)--(8), new after
review N, unreviewed): the annulus package and the general position of (8).

`exists_section34ProtectedCircleRemoval` (Lemmas 1--3, new after review N, unreviewed): a
label-wise finite descent with locally finite supports, not a minimisation of a possibly
infinite total count, ending with every `A'_e ∩ B'_e` connected.

`exists_section34EdgeMatching` (the deletion and the three stage extension, changed after
review N, unreviewed): the joint producer.  It outputs the exact meet, the marker clause, the
rim containment and the nested-torus certificate; the initial approximations are not preserved,
conditions (2)--(8) are what is carried, and the `ψ` estimate comes from the fine carriers.

Proved here, not leaves: the assembly, which in particular proves conditions (2) and (3) of
Section 34 Lemma 1 from the carrier separation and the combinatorics of the splitting disks,
the `ψ` estimate, and the generator clause from the nested-torus certificate.
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
    ∀ (Ea : Type) [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
      (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U), IsCombinatorialManifold 3 𝒦.complex →
    ∀ (η : M₁ → ℝ) (H : Finset Ea → Set M₂), Section34CarrierControl U 𝒦 h η H →
    ∀ {W : Set M₁}, IsOpen W → graphSkeletonSpace 𝒦 ⊆ W → W ⊆ U →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea) (f₁ : M₁ → M₂),
      Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        Section34GraphFrame U W h ψ H 𝒦 𝒦' src car f₁

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Bb Ab₀ Ab₁ Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34CutFrame [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (η : M₁ → ℝ) (H : Finset Ea → Set M₂) (hH : Section34CarrierControl U 𝒦 h η H)
    (hW : IsOpen W) (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hWU : W ⊆ U)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂),
      Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
          (graphSkeletonSpace 𝒦) U ∧
        section34CutNeighborhood src ⊆ W ∧
        (∀ w, car w ∈ 𝒦.complex.faces) ∧
        (∀ w, src (.vertexBall w) ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
        (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
        (∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) ∧
        (∀ w, Q w ⊆ H (car w)) ∧
        (∀ w, ∀ x ∈ src (.vertexBall w), ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
        ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
          (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1 := by
  sorry

theorem exists_section34VertexPreparation [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQint : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hQsmall : ∀ w, ∀ x ∈ src (Section34Label.vertexBall w), ∀ y ∈ Q w, ∀ z ∈ Q w,
      dist y z < ψ x) :
    ∃ (Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁) (ε : Section34VertexIndex 𝒦 𝒦' → ℝ),
      Section34VertexPreparation U 𝒦 𝒦' h src Q Cc CcBd ε := by
  sorry

theorem Moise341.exists_section34VertexApproximation (h341 : Moise341) [T2Space M₁]
    [SecondCountableTopology M₁] [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q Cc CcBd ε) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
        ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w := by
  sorry

theorem exists_section34PiercingPackage [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q Cc CcBd ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cc w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) :
    ∃ (ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
      (Sn Tn Aa Bb Ab₀ Ab₁ Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
      (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂),
      Section34PiercingConditions U 𝒦 𝒦' h src Q Cc CcBd ends Sn Tn Aa Bb Ab₀ Ab₁ Bb₀ Bb₁
        G' := by
  sorry

theorem exists_section34ProtectedCircleRemoval [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q Cc CcBd ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h src Q Cc CcBd ends Sn Tn Aa Bb Ab₀ Ab₁
      Bb₀ Bb₁ G) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      Section34PiercingConditions U 𝒦 𝒦' h src Q Cc CcBd ends Sn Tn Aa Bb Ab₀ Ab₁ Bb₀ Bb₁
          G' ∧
        ∀ e, IsConnected (G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e) := by
  sorry

theorem exists_section34EdgeMatching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q Cc CcBd ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h src Q Cc CcBd ends Sn Tn Aa Bb Ab₀ Ab₁
      Bb₀ Bb₁ G)
    (hconn : ∀ e, IsConnected (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e)) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G' w) (src (.vertexBall w))) ∧
        (∀ w, G' w '' src (.vertexBall w) ⊆ Q w) ∧
        (∀ w w', EqOn (G' w) (G' w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        (∀ w w', G' w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          G' w '' src (.vertexBall w) ∩ G' w' '' src (.vertexBall w')) ∧
        ((⋃ w, G' w '' src (.vertexBall w)) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) ∧
        (∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (G' w '' src (.vertexBall w))) ∧
        (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
          interior (section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s)) ∧
        ∀ s : Section34SimplexIndex 𝒦 3,
          ∃ (S₁ S₂ Te Je : Set (EuclideanSpace ℝ (Fin 3)))
            (Φ : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ≃ₜ Te),
            (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔
                  (Φ y : EuclideanSpace ℝ (Fin 3)) ∈ Je) ∧
              IsTopologicalSolidTorus S₁ ∧ IsTopologicalSolidTorus S₂ ∧
              IsCombinatorialSolidTorus Te ∧ S₁ ⊆ interior Te ∧ Te ⊆ interior S₂ ∧
              IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) ∧
              IsSpine S₁ Je ∧ Je ⊆ Te := by
  sorry

end Leaves

theorem controlledGraphNeighborhood (h341 : Moise341) :
    ControlledGraphNeighborhoodStatement.{u} := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh Ea _ _ _ 𝒦 h𝒦 η H hH W hW hΓW hWU ψ hψc hψpos
  obtain ⟨-, hHsub, hHlf, -, -⟩ := id hH
  obtain ⟨𝒦', src, srcBd, car, Q, hframe, hN, hNW, hcarF, hcarS, hcarfib, hQint, hQH,
      hQsmall, hQsep⟩ :=
    exists_section34CutFrame hU hh 𝒦 h𝒦 η H hH hW hΓW hWU ψ hψc hψpos
  obtain ⟨Cc, CcBd, ε, hprep⟩ :=
    exists_section34VertexPreparation (ψ := ψ) hU hh hframe hN hQint hQsmall
  obtain ⟨G₀, hG₀, hG₀dist⟩ := h341.exists_section34VertexApproximation hU hh hframe hprep
  obtain ⟨ends, Sn, Tn, Aa, Bb, Ab₀, Ab₁, Bb₀, Bb₁, G₁, hpack⟩ :=
    exists_section34PiercingPackage hU hh hframe hN hprep hG₀ hG₀dist
  obtain ⟨G₂, hpack₂, hconn⟩ :=
    exists_section34ProtectedCircleRemoval hU hh hframe hprep hpack
  obtain ⟨G, hG, hGQ, hcompat, hmeet, hGnbhd, hmarker, hrim, hcert⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hprep hpack₂ hconn
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hsplit, -⟩ := id hframe
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
  have hfun : (fun w => f₁ '' src (Section34Label.vertexBall w)) =
      fun w => G w '' src (Section34Label.vertexBall w) := funext himg
  have hf₁Q : ∀ w, f₁ '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [himg w]
    exact hGQ w
  have hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hrw : f₁ '' section34CutNeighborhood src =
        ⋃ w, G w '' src (Section34Label.vertexBall w) := hf₁im
    rw [hrw]
    exact hGnbhd
  have hmer : ∀ s : Section34SimplexIndex 𝒦 3,
      CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1)
        (section34FaceTorus (fun w => G w '' src (Section34Label.vertexBall w)) s) := by
    intro s
    obtain ⟨S₁, S₂, Te, Je, Φ, hΦ, hS₁, hS₂, hTe, h₁T, hT₂, hshell, hspine, hJe⟩ := hcert s
    exact carriesFundamentalGroupOnto_of_nestedSolidTorus
      ((hrim s).trans interior_subset) Φ hΦ hS₁ hS₂ hTe h₁T hT₂ hshell hspine hJe
  refine ⟨𝒦', src, srcBd, car, f₁, hframe, hN, hNW, hf₁, hnbhd, ?_, ?_, ?_, ?_, ?_, ?_,
    hcarF, hcarS, hcarfib, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    refine hQsmall w x hw (f₁ x) (hf₁Q w ⟨x, hw, rfl⟩) (h x) ?_
    exact interior_subset (hQint w ⟨x, hw, rfl⟩)
  · intro w
    rw [himg w]
    exact hmarker w
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
    have hkey : ((e.1 : Finset Ea) : Set Ea) ⊆ convexHull ℝ ((s.1 : Finset Ea) : Set Ea) := by
      rw [hunion]
      exact union_subset hw hw'
    exact hkey
  · intro w s hne
    obtain ⟨y, hy₁, hy₂⟩ := hne
    exact hQsep w s ⟨y, hf₁Q w hy₁, hy₂⟩
  · intro s
    rw [hfun]
    exact hrim s
  · intro s
    rw [hfun]
    exact hmer s
  · intro w
    refine union_subset ?_ ((hf₁Q w).trans (hQH w))
    exact fun y hy => hQH w (interior_subset (hQint w hy))

end DifferentialGeometry.Topology.PiecewiseLinear
