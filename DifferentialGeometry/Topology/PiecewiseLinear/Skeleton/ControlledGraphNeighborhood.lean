/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of the controlled form of Moise 35.1

The assembly `controlledGraphNeighborhood` proves the endpoint
`ControlledGraphNeighborhoodStatement` for real from the six leaves of this file; every `sorry`
is a leaf and none sits inside an assembly.  The endpoint statement is unchanged.  The endpoint
is **not** a producer of `Section34NormalPlus`: it supplies P1 only, that is the cut frame and
the graph frame, conditional on `Moise341`.  The carrier control of P0, the exterior clause and
the Lemma 11 trace certificate remain obligations of the other half.

The realisation ambient `Ea` is universally quantified in the endpoint, next to the
triangulation it realises; it is never the chart model.  `LocallyFinitePLPieceIn Ea 3 M₁ U`
realises all of `U` inside `Ea`, so writing `EuclideanSpace ℝ (Fin 3)` there would exclude
`U = S³`.

Quantifier order is the content.  The triangulation `𝒦` and the carrier control `(η, H)` come
first, because Section 34 chooses them once for the whole approximation problem; only then the
prescribed neighbourhood `W` of the one skeleton and the free tolerance `ψ`, which Moise 35.2
supplies afresh; and the subdivision `𝒦'`, the cut diagram, the regular neighbourhood and `f₁`
stand in one existential, because Lemma 1's incidence clauses are read off a jointly chosen
neighbourhood and map.

Pages 248--250 are followed literally, and the *pierced* cells `C'_v` are separated from the
*enlarged* cells `C''_v`.  `Section34VertexPreparation` fixes, before any map, the endpoint
assignment of the edges, `C'_v` with `C_v ⊆ C'_v` and the graph core in `Int C'_v`, the piercing
circle `Bd C'_v ∩ Bd C'_w` inside the splitting disk, the two compatible regular neighbourhoods
`T_e ⊆ Int S_e` of that circle with their solid torus structure, the annuli
`A_e = Bd C'_v ∩ T_e` and `B_e ⊆ Bd C'_w` with their designated boundary circles, the enlarged
cells `C''_v ⊇ C'_v ∪ ⋃_{e ∋ v} S_e`, one piecewise linear chart of `M₂` containing `h '' C''_v`
and one containing the carriers of the vertices of each triangle, and only then the tolerances
`ε_v`, which protect the graph core against both `Bd C'_v` and `Bd C''_v` and are below the
incident tube margins.  Taking `A_e` on `Bd C''_v` makes condition (3) contradictory as soon as
`T_e ⊆ C''_v` is recorded, because `G_v (Bd C''_v)` is then the frontier of `G_v (C''_v)`.

The vertex chart is what makes step 6 a theorem instead of a leaf: the piecewise linear
parametrisation of `C''_v` carries the problem to a polyhedral `3`-cell of `ℝ³` whose image
lies in one chart, which is the hypothesis of the proved chart local
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`, and the result is conjugated back
by `exists_isPLHomeomorphInto_of_isPLHomeomorphOn`.

`Section34PiercingConditions` is conditions (2)--(8).  Its general position clause is no longer
the containment of the intersection polygons in the two relative interiors, which the tangent
pair `{(θ, u, 0)}`, `{(θ, u, |u|)}` satisfies, but the local crossing model `HasPLCrossingAt`
read in a piecewise linear chart at every intersection point.  The target supports `S'_e`,
`T'_e` and the circle count are fields of the package, locally finite in the target, so that the
circle removal is a single step inside `Int S'_e` fixing the graph core and the data of the
other edges and strictly lowering one count.

The leaves, with content and review state.

`exists_section34CutFrame` (steps 1--5): reviewed 2026-09-21 OK, frozen pending the lead's
due-diligence pass; byte-identical.  It produces `𝒦'`, the cut frame, the regular neighbourhood
`N = ⋃ C_v` of the one skeleton inside `W`, the assignment `car` with finite fibres, the fine
carriers `Q v` and the carrier separation `hQsep`.

`exists_section34VertexPreparation` (preparation certificates, rewritten after review P): the
pierced cells, the tubes, the annuli, the enlarged cells, the charts and the tolerances.

`exists_section34PiercingPackage` (the piercing alteration and conditions (2)--(8), rewritten
after review P): the target supports, the circle count and the crossing model.

`exists_section34ProtectedCircleRemovalStep` (Lemmas 2 and 3, one step, new after review P):
one modification inside `Int S'_{e₀}` fixing the graph core, the target supports and the annuli
of the other edges, keeping the conditions and lowering one count.

`exists_section34ProtectedCircleRemoval` (new after review P): the same for all labels at once.
Its residual content is the locally finite parallel assembly only, the descent at one label
being the proved `exists_section34PiercingConditions_count_le_one`.

`exists_section34EdgeMatching` (the deletion and the three stage extension, rewritten after
review P): the joint producer.  It receives the carrier separation `hQsep` and the local
finiteness of the carriers, without which rim containment is false: a compactly supported
piecewise linear homeomorphism of `Int N` can carry an interior point of a non-incident `C_w`
onto a point of `h '' Bd σ`, and no incident carrier need then contain it.  It outputs the exact
meet, the marker clause, the rim containment and the nested torus certificate, whose `Φ` is the
restriction of the triangle chart fixed in the preparation.

Proved here, not leaves: `Moise341.exists_section34VertexApproximation`,
`exists_section34PiercingConditions_count_le_one`, and the assembly, which in particular proves
conditions (2) and (3) of Section 34 Lemma 1 from the carrier separation and the combinatorics
of the splitting disks, the `ψ` estimate, and the generator clause from the nested torus
certificate.
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
  {Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
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
    (hQint : ∀ w, h '' src (Section34Label.vertexBall w) ⊆ interior (Q w)) :
    ∃ (Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁)
      (ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
      (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
      (ε : Section34VertexIndex 𝒦 𝒦' → ℝ),
      Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
        Bb Bb₀ Bb₁ ε := by
  sorry

omit [FiniteDimensional ℝ Ea] in
theorem Moise341.exists_section34VertexApproximation (h341 : Moise341)
    [HasGroupoid M₂ (plGroupoid 3)] (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
        ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w := by
  classical
  obtain ⟨-, -, hcc, hsub, -, -, -, -, -, -, -, -, -, -, -, -, hεpos, -, -, -, -, -,
    hchart, -⟩ := hprep
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have key : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ F : M₁ → M₂,
      IsPLHomeomorphInto 3 F (Cc w) ∧ ∀ x ∈ Cc w, dist (F x) (h x) < ε w := by
    intro w
    obtain ⟨P, r, u, hr, hu, hCceq, -⟩ := hcc w
    obtain ⟨c, hc, hcsrc⟩ := hchart w
    have hPball : IsPLBall 3 P := ⟨r, hr⟩
    have hmem : ∀ x ∈ P, u x ∈ Cc w := by
      intro x hx
      rw [hCceq]
      exact ⟨x, hx, rfl⟩
    have hback : ∀ y ∈ Cc w, ∃ x ∈ P, u x = y := by
      intro y hy
      rw [hCceq] at hy
      exact hy
    have huP : MapsTo u P U := fun x hx => (hsub w).2.2 (hmem x hx)
    have hcont : ContinuousOn (h ∘ u) P := hcontU.comp hu.continuousOn huP
    have hinj : InjOn (h ∘ u) P := hinjU.comp hu.injOn huP
    have hmap : MapsTo (h ∘ u) P c.source := fun x hx => hcsrc ⟨u x, hmem x hx, rfl⟩
    obtain ⟨f, hf, -, hfd⟩ :=
      h341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart hPball hcont hinj c hc hmap
        (τ := fun _ => ε w) continuousOn_const fun _ _ => hεpos w
    refine ⟨f ∘ Function.invFunOn u P, ?_, ?_⟩
    · rw [hCceq]
      exact (exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hf
        hPball.isPolyhedron.isPLHomeomorphOn_id).1
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := hback x hx
      have hzz : Function.invFunOn u P (u z) = z := hu.injOn.leftInvOn_invFunOn hz
      have hd := hfd z hz
      simp only [Function.comp_apply, hzz] at hd ⊢
      exact hd
  choose G hG hGd using key
  exact ⟨G, hG, hGd⟩

theorem exists_section34PiercingPackage [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cc w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) :
    ∃ (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)
      (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G' := by
  sorry

theorem exists_section34ProtectedCircleRemovalStep
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (hlt : 1 < cnt e₀) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        (∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  sorry

theorem exists_section34PiercingConditions_count_le_one
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε)
    (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        cnt' e₀ ≤ 1 ∧ ∀ e, e ≠ e₀ → cnt' e = cnt e := by
  classical
  suffices H : ∀ n : ℕ, ∀ (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
      (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ) (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G → cnt e₀ ≤ n →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ ≤ 1 ∧ ∀ e, e ≠ e₀ → cnt' e = cnt e by
    exact H (cnt e₀) G cnt Pg hpack le_rfl
  intro n
  induction n with
  | zero =>
      intro G cnt Pg hp hle
      exact ⟨G, cnt, Pg, hp, by omega, fun _ _ => rfl⟩
  | succ n ih =>
      intro G cnt Pg hp hle
      by_cases h1 : cnt e₀ ≤ 1
      · exact ⟨G, cnt, Pg, hp, h1, fun _ _ => rfl⟩
      · obtain ⟨G₁, cnt₁, Pg₁, hp₁, hdrop, hfix, -, -, -⟩ :=
          exists_section34ProtectedCircleRemovalStep hprep hp e₀ (by omega)
        obtain ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, hfix₂⟩ := ih G₁ cnt₁ Pg₁ hp₁ (by omega)
        exact ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, fun e he => (hfix₂ e he).trans (hfix e he)⟩

theorem exists_section34ProtectedCircleRemoval
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        ∀ e, cnt' e = 1 := by
  sorry

theorem exists_section34EdgeMatching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (hone : ∀ e, cnt e = 1) :
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
          ∃ (c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
            (S₁ S₂ Te Je : Set (EuclideanSpace ℝ (Fin 3)))
            (Φ : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ≃ₜ Te),
            c ∈ (plGroupoid 3).maximalAtlas M₂ ∧
              section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ⊆ c.source ∧
              (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (Φ y : EuclideanSpace ℝ (Fin 3)) = c (y : M₂)) ∧
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
  have hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite := by
    refine exists_nhds_finite_of_subset_carriers (h '' U) Q H car hQH
      (fun w => hHsub _ (hcarF w)) hcarfib ?_
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  obtain ⟨Cp, CpBd, Cc, CcBd, ends, Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, ε, hprep⟩ :=
    exists_section34VertexPreparation hU hh hframe hN hQint
  obtain ⟨G₀, hG₀, hG₀dist⟩ := h341.exists_section34VertexApproximation hh hprep
  obtain ⟨Sp, Tp, cnt, Pg, G₁, hpack⟩ :=
    exists_section34PiercingPackage hU hh hframe hN hprep hG₀ hG₀dist
  obtain ⟨G₂, cnt₂, Pg₂, hpack₂, hone⟩ := exists_section34ProtectedCircleRemoval hprep hpack
  obtain ⟨G, hG, hGQ, hcompat, hmeet, hGnbhd, hmarker, hrim, hcert⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hQsep hQlf hprep hpack₂ hone
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
    obtain ⟨-, S₁, S₂, Te, Je, Φ, -, -, -, hΦ, hS₁, hS₂, hTe, h₁T, hT₂, hshell, hspine,
      hJe⟩ := hcert s
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
