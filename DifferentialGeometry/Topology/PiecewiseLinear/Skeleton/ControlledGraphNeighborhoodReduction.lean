/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedTubePiercingConditions

/-!
# Relative boundary matching and protected moves

The unreviewed leaves jointly choose compatible boundary maps, locate the original face rims
inside the fixed target family, and recognize the nested target tori. Cell extension and the
frozen edge-matching endpoint are proved from these lower-dimensional and geometric leaves.
Supported-homeomorphism transport is proved separately. The geometric cancellation-region
producer and the frozen one-step removal endpoint are not supplied by these transport lemmas.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.ControlledGraphNeighborhood

universe u

section RelativeCells

variable {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_extension_of_cell_boundary {d : ℕ} (hd : 0 < d)
    {P PB : Set M₁} {Q QB : Set M₂} (hP : IsPLCellOn d P PB) (hQ : IsPLCellOn d Q QB)
    {g : M₁ → M₂} (hg : IsPLHomeomorphInto 3 g PB) (himage : g '' PB = QB) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f P ∧ f '' P = Q ∧ EqOn f g PB := by
  obtain ⟨A, r, a, hr, ha, rfl, rfl⟩ := hP
  obtain ⟨B, s, b, hs, hb, rfl, rfl⟩ := hQ
  exact exists_isPLHomeomorphInto_extension_of_cell hd hr hs ha hb hg Subset.rfl himage

end RelativeCells
variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem vertex_inter_subset_boundary
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (w w' : Section34VertexIndex 𝒦 𝒦') (hne : w ≠ w') :
    src (.vertexBall w) ∩ src (.vertexBall w') ⊆ srcBd (.vertexBall w) := by
  obtain ⟨-, -, -, -, hboundary, hmeet, hstrict, -⟩ := hframe
  rw [hmeet, hboundary]
  refine iUnion₂_subset fun k hk => ?_
  have hkne : k ≠ .vertexBall w := by
    intro heq
    subst k
    rcases hstrict (.vertexBall w') (.vertexBall w) hk.2 with heq | hdim
    · exact hne (by cases heq; rfl)
    · simp [section34Dim] at hdim
  exact subset_iUnion₂_of_subset k ⟨hk.1, hkne⟩ Subset.rfl
theorem exists_joint_boundary_matching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∃ b : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (b w) (srcBd (.vertexBall w))) ∧
        (∀ w, b w '' srcBd (.vertexBall w) = DvBd w) ∧
        (∀ w w', w ≠ w' → EqOn (b w) (b w')
          (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        ∀ w w', w ≠ w' → b w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          Dv w ∩ Dv w' := by
  sorry
theorem face_rim_subset_interior_deleted_family [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∀ s : Section34SimplexIndex 𝒦 3,
      h '' simplexRim 𝒦 s.1 ⊆ interior (section34FaceTorus Dv s) := by
  sorry
theorem exists_nested_torus_of_deleted_family [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∀ s : Section34SimplexIndex 𝒦 3,
      ∃ (S₁ Te : Set (EuclideanSpace ℝ (Fin 3))) (Φ : section34FaceTorus Dv s ≃ₜ Te),
        section34FaceTorus Dv s ⊆ (ct s).source ∧
          (∀ y : section34FaceTorus Dv s, (Φ y : EuclideanSpace ℝ (Fin 3)) = ct s (y : M₂)) ∧
          (∀ y : section34FaceTorus Dv s, (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔
            (Φ y : EuclideanSpace ℝ (Fin 3)) ∈ ct s '' (h '' simplexRim 𝒦 s.1)) ∧
          IsTopologicalSolidTorus S₁ ∧ IsCombinatorialSolidTorus Te ∧
          S₁ ⊆ interior Te ∧ Te ⊆ interior (Sd s) ∧
          IsToroidalShell (closure (Sd s \ S₁)) (frontier S₁) (frontier (Sd s)) ∧
          IsSpine S₁ (ct s '' (h '' simplexRim 𝒦 s.1)) ∧
          ct s '' (h '' simplexRim 𝒦 s.1) ⊆ Te := by
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
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G' w) (src (.vertexBall w))) ∧
        (∀ w, G' w '' src (.vertexBall w) = Dv w) ∧
        (∀ w w', EqOn (G' w) (G' w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        (∀ w w', G' w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          G' w '' src (.vertexBall w) ∩ G' w' '' src (.vertexBall w')) ∧
        (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
          interior (section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s)) ∧
        ∀ s : Section34SimplexIndex 𝒦 3,
          ∃ (S₁ Te : Set (EuclideanSpace ℝ (Fin 3)))
            (Φ : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ≃ₜ Te),
            section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ⊆ (ct s).source ∧
              (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (Φ y : EuclideanSpace ℝ (Fin 3)) = ct s (y : M₂)) ∧
              (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔
                  (Φ y : EuclideanSpace ℝ (Fin 3)) ∈ ct s '' (h '' simplexRim 𝒦 s.1)) ∧
              IsTopologicalSolidTorus S₁ ∧ IsCombinatorialSolidTorus Te ∧
              S₁ ⊆ interior Te ∧ Te ⊆ interior (Sd s) ∧
              IsToroidalShell (closure (Sd s \ S₁)) (frontier S₁) (frontier (Sd s)) ∧
              IsSpine S₁ (ct s '' (h '' simplexRim 𝒦 s.1)) ∧
              ct s '' (h '' simplexRim 𝒦 s.1) ⊆ Te := by
  obtain ⟨b, hb, hbim, hbcompat, hbmeet⟩ :=
    exists_joint_boundary_matching hU hh hframe hN hQsep hQlf htor hprep hpack Dv DvBd Dd DdBd
      hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj hDvQ hDnbhd
  have hsrc : ∀ w, IsPLCellOn 3 (src (.vertexBall w)) (srcBd (.vertexBall w)) :=
    fun w => hframe.2.2.2.1 (.vertexBall w)
  choose f hf hfim hfb using fun w =>
    exists_extension_of_cell_boundary (by decide : 0 < 3) (hsrc w) (hDv w) (hb w) (hbim w)
  have himages : (fun w => f w '' src (.vertexBall w)) = Dv := funext hfim
  refine ⟨f, hf, hfim, ?_, ?_, ?_, ?_⟩
  · intro w w'
    by_cases hww' : w = w'
    · subst w'
      exact Set.eqOn_refl _ _
    · intro x hx
      exact (hfb w (vertex_inter_subset_boundary hframe w w' hww' hx)).trans
        ((hbcompat w w' hww' hx).trans
          (hfb w' (vertex_inter_subset_boundary hframe w' w (Ne.symm hww') ⟨hx.2, hx.1⟩)).symm)
  · intro w w'
    by_cases hww' : w = w'
    · subst w'
      simp only [inter_self]
    · rw [hfim, hfim]
      exact ((hfb w).mono (vertex_inter_subset_boundary hframe w w' hww')).image_eq.trans
        (hbmeet w w' hww')
  · rw [himages]
    exact face_rim_subset_interior_deleted_family hU hh hframe hN hQsep hQlf htor hprep hpack
      Dv DvBd Dd DdBd hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj hDvQ hDnbhd
  · rw [himages]
    exact exists_nested_torus_of_deleted_family hU hh hframe hN hQsep hQlf htor hprep hpack
      Dv DvBd Dd DdBd hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj hDvQ hDnbhd
namespace ProtectedMove

section Topological

variable {X Y : Type*} [TopologicalSpace Y]

theorem mapsTo_of_eqOn_compl (φ : Y ≃ₜ Y) {V : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) : Set.MapsTo φ V V := by
  intro y hy
  by_contra hφy
  have h : φ (φ y) = φ y := hfix hφy
  have heq : φ y = y := φ.injective h
  exact hφy (heq.symm ▸ hy)

theorem mapsTo_of_support_subset (φ : Y ≃ₜ Y) {V Q : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) (hVQ : V ⊆ Q) : Set.MapsTo φ Q Q := by
  intro y hy
  by_cases hyV : y ∈ V
  · exact hVQ (mapsTo_of_eqOn_compl φ hfix hyV)
  · rw [hfix hyV]
    exact hy

theorem image_comp_subset_of_support_subset (φ : Y ≃ₜ Y) {V Q : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) (hVQ : V ⊆ Q) {f : X → Y} {A : Set X}
    (hA : f '' A ⊆ Q) : (φ ∘ f) '' A ⊆ Q := by
  rintro _ ⟨x, hx, rfl⟩
  exact mapsTo_of_support_subset φ hfix hVQ (hA ⟨x, hx, rfl⟩)

theorem eqOn_comp_of_disjoint_image (φ : Y ≃ₜ Y) {V : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) {f : X → Y} {A : Set X}
    (hAV : Disjoint (f '' A) V) : Set.EqOn (φ ∘ f) f A := by
  intro x hx
  exact hfix (fun hfx => Set.disjoint_left.mp hAV ⟨x, hx, rfl⟩ hfx)

theorem eqOn_comp_of_disjoint_source (φ : Y ≃ₜ Y) {V : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) {f : X → Y} {A N C : Set X}
    (hf : Set.InjOn f C) (hAC : A ⊆ C) (hNC : N ⊆ C)
    (hAN : Disjoint A N) (hVN : V ⊆ f '' N) : Set.EqOn (φ ∘ f) f A := by
  apply eqOn_comp_of_disjoint_image φ hfix
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨x, hx, rfl⟩ hfx
  obtain ⟨y, hy, hxy⟩ := hVN hfx
  have heq : y = x := hf (hNC hy) (hAC hx) hxy
  exact Set.disjoint_left.mp hAN hx (heq ▸ hy)

theorem image_inter_eq_of_disjoint_support (φ : Y ≃ₜ Y) {V A F : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) (hVF : Disjoint V F) :
    (φ '' A) ∩ F = A ∩ F := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyF⟩
    have hyV : y ∉ V := fun hy => Set.disjoint_left.mp hVF hy hyF
    have hyfix : φ y = y := hfix hyV
    have hxeq : x = y := φ.injective (hxy.trans hyfix.symm)
    exact ⟨hxeq ▸ hx, hyF⟩
  · rintro ⟨hyA, hyF⟩
    have hyV : y ∉ V := fun hy => Set.disjoint_left.mp hVF hy hyF
    exact ⟨⟨y, hyA, hfix hyV⟩, hyF⟩

theorem disjoint_image_of_disjoint_support (φ : Y ≃ₜ Y) {V A F : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) (hVF : Disjoint V F) (hAF : Disjoint A F) :
    Disjoint (φ '' A) F := by
  rw [Set.disjoint_iff_inter_eq_empty,
    image_inter_eq_of_disjoint_support φ hfix hVF]
  exact Set.disjoint_iff_inter_eq_empty.mp hAF

theorem image_inter_disjoint_of_overlap_and_support (φ : Y ≃ₜ Y) {V A B F : Set Y}
    (hfix : Set.EqOn φ id Vᶜ) (hVF : Disjoint V F)
    (hABF : Disjoint (A ∩ B) F) : Disjoint ((φ '' A) ∩ B) F := by
  refine Set.disjoint_left.mpr ?_
  rintro y ⟨hyA, hyB⟩ hyF
  have hyAF : y ∈ A ∩ F := by
    rw [← image_inter_eq_of_disjoint_support φ hfix hVF]
    exact ⟨hyA, hyF⟩
  exact Set.disjoint_left.mp hABF ⟨hyAF.1, hyB⟩ hyF

end Topological

section Connected

variable {Y : Type*} [TopologicalSpace Y]

theorem disjoint_of_preconnected_of_anchor_outside {V F : Set Y} (hV : IsPreconnected V)
    (hVF : Disjoint V (frontier F)) {a : Y} (haV : a ∈ V) (haF : a ∉ F) :
    Disjoint V F := by
  refine Set.disjoint_left.mpr ?_
  intro y hyV hyF
  have hsub : V ⊆ F := IsPreconnected.subset_of_disjoint_frontier hV ⟨y, hyV, hyF⟩ hVF
  exact haF (hsub haV)

end Connected

end ProtectedMove

end DifferentialGeometry.Topology.PiecewiseLinear.ControlledGraphNeighborhood
