/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34JointCellMatching
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedDeletedTorus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

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
  let _ := hN
  let _ := (inferInstance : SecondCountableTopology M₁)
  let _ := (inferInstance : SecondCountableTopology M₂)
  obtain ⟨F, hF, hFim, hcompat, hinter, -⟩ := exists_section34_joint_cell_matching
    hU hh hframe htor hprep hpack hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj hDvQ hQlf hDnbhd
  have himages : (fun w => F w '' src (.vertexBall w)) = Dv := funext hFim
  refine ⟨F, hF, hFim, hcompat, ?_, ?_, ?_⟩
  · intro w w'
    rw [hFim w, hFim w']
    exact hinter w w'
  · rw [himages]
    exact face_rim_subset_interior_of_deleted_family hQsep hQlf htor hDv hDvQ hDnbhd
  · rw [himages]
    obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
    exact exists_nested_torus_of_deleted_family hframe.2.1 hframe.2.2.1
      (fun e => (hends e).2.1) hQsep hQlf htor hDv hDd hDmeet hDadj hDddisj hDvQ hDnbhd

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
