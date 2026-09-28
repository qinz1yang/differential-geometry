/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration
import DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308Nested
import DifferentialGeometry.Topology.PiecewiseLinear.RevolutionOfCellInteriorSubsetInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusGeneralPosition
import DifferentialGeometry.Topology.VanKampen.CellAttachmentFundamentalGroup
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.InnerSolidTorusToroidalShell
import DifferentialGeometry.Topology.PiecewiseLinear.CarriesGeneratorOrIsPLCellOfDisjointCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.ConsecutiveCellUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCarrierOfSpine
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonNullhomotopicBoundaryDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Revolution

theorem revolutionOf_union (X Y : Set (EuclideanSpace ℝ (Fin 3))) :
    revolutionOf (X ∪ Y) = revolutionOf X ∪ revolutionOf Y := by
  ext p
  simp only [revolutionOf, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨q, hq | hq, hrest⟩
    · exact Or.inl ⟨q, hq, hrest⟩
    · exact Or.inr ⟨q, hq, hrest⟩
  · rintro (⟨q, hq, hrest⟩ | ⟨q, hq, hrest⟩)
    · exact ⟨q, Or.inl hq, hrest⟩
    · exact ⟨q, Or.inr hq, hrest⟩

theorem revolutionOf_inter (X Y : Set (EuclideanSpace ℝ (Fin 3))) :
    revolutionOf X ∩ revolutionOf Y = revolutionOf (X ∩ Y) := by
  ext p
  constructor
  · rintro ⟨⟨q, hqX, hq2, hq0, hq1, hqsq⟩, ⟨q', hq'Y, hq'2, hq'0, hq'1, hq'sq⟩⟩
    have h0 : q 0 = q' 0 := (sq_eq_sq₀ hq0 hq'0).mp (hqsq.trans hq'sq.symm)
    have hqq' : q = q' := by
      refine PiLp.ext fun i => ?_
      fin_cases i
      · exact h0
      · exact hq1.trans hq'1.symm
      · exact hq2.trans hq'2.symm
    exact ⟨q, ⟨hqX, hqq' ▸ hq'Y⟩, hq2, hq0, hq1, hqsq⟩
  · rintro ⟨q, ⟨hqX, hqY⟩, hrest⟩
    exact ⟨⟨q, hqX, hrest⟩, ⟨q, hqY, hrest⟩⟩

theorem revolutionOf_empty : revolutionOf ∅ = ∅ := by
  ext p
  simp [revolutionOf]

theorem mem_revolutionOf_self {X : Set (EuclideanSpace ℝ (Fin 3))} {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ∈ X) (h2 : q 2 = 0) (h0 : 0 ≤ q 0) : q ∈ revolutionOf X :=
  ⟨q, hq, h2, h0, rfl, by rw [h2]; ring⟩

theorem isCompact_revolutionOf {X : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsCompact X) :
    IsCompact (revolutionOf X) := by
  obtain ⟨R, hR⟩ := hX.isBounded.subset_closedBall 0
  have hC : IsCompact ({z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | z.1 ∈ X} ∩
      ({z | z.1 2 = 0} ∩ ({z | 0 ≤ z.1 0} ∩
        ({z | z.1 1 = z.2 1} ∩ {z | z.1 0 ^ 2 = z.2 0 ^ 2 + z.2 2 ^ 2})))) := by
    refine (hX.prod (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R)).of_isClosed_subset
      ((hX.isClosed.preimage continuous_fst).inter
        ((isClosed_eq (by fun_prop) continuous_const).inter
          ((isClosed_le continuous_const (by fun_prop)).inter
            ((isClosed_eq (by fun_prop) (by fun_prop)).inter
              (isClosed_eq (by fun_prop) (by fun_prop)))))) ?_
    rintro ⟨q, p⟩ ⟨hqX, hq2, -, hq1, hqsq⟩
    have hq2' : q 2 = 0 := hq2
    have hq1' : q 1 = p 1 := hq1
    have hqsq' : q 0 ^ 2 = p 0 ^ 2 + p 2 ^ 2 := hqsq
    have hqR : ‖q‖ ≤ R := mem_closedBall_zero_iff.mp (hR hqX)
    refine ⟨hqX, mem_closedBall_zero_iff.mpr (le_trans ?_ hqR)⟩
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    change ‖p‖ ^ 2 ≤ ‖q‖ ^ 2
    have h1 := EuclideanSpace.real_norm_sq_eq p
    have h2 := EuclideanSpace.real_norm_sq_eq q
    rw [Fin.sum_univ_three] at h1 h2
    rw [hq2', hq1', hqsq', zero_pow two_ne_zero, add_zero] at h2
    linarith
  convert hC.image continuous_snd using 1
  ext p
  constructor
  · rintro ⟨q, hq, h2, h0, h1, hsq⟩
    exact ⟨(q, p), ⟨hq, h2, h0, h1, hsq⟩, rfl⟩
  · rintro ⟨⟨q, p'⟩, ⟨hq, h2, h0, h1, hsq⟩, rfl⟩
    exact ⟨q, hq, h2, h0, h1, hsq⟩

end Revolution

section Transport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isEmbedding_domRestrict_mono {f : X → Y} {N S : Set X}
    (hf : IsEmbedding (N.domRestrict f)) (hS : S ⊆ N) : IsEmbedding (S.domRestrict f) :=
  hf.comp (IsEmbedding.inclusion hS)

private noncomputable def domRestrictImageHomeomorph {f : X → Y} {S : Set X}
    (hf : IsEmbedding (S.domRestrict f)) : S ≃ₜ f '' S :=
  hf.toHomeomorph.trans (Homeomorph.setCongr (Set.range_domRestrict f S))

theorem isTopologicalSolidTorus_image_of_isEmbedding {f : X → Y} {S : Set X}
    (hf : IsEmbedding (S.domRestrict f)) (hS : IsTopologicalSolidTorus S) :
    IsTopologicalSolidTorus (f '' S) :=
  ⟨(domRestrictImageHomeomorph hf).symm.trans (Classical.choice hS)⟩

theorem isSpine_image_of_isEmbedding {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsEmbedding (S.domRestrict f))
    (hJ : IsSpine S J) : IsSpine (f '' S) (f '' J) := by
  obtain ⟨φ, p, hp, hJ⟩ := hJ
  refine ⟨φ.trans (domRestrictImageHomeomorph hf), p, hp, ?_⟩
  rw [hJ]
  simp only [image_image]
  rfl

end Transport

section FundamentalGroupTransfer

private theorem isClosed_of_isTopologicalSolidTorus {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsTopologicalSolidTorus S) : IsClosed S := by
  let φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := Classical.choice hS
  let _ : CompactSpace S := φ.symm.compactSpace
  exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed

private theorem pathConnectedSpace_of_isTopologicalSolidTorus
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) :
    PathConnectedSpace S := by
  let φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := Classical.choice hS
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have hD : PathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).isPathConnected
        ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  have hC : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous

theorem fundamentalGroup_map_inclusion_bijective_of_isSpine_of_subset_interior
    {S T J : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S)
    (hT : IsTopologicalSolidTorus T) (hST : S ⊆ interior T) (hJ : IsSpine T J) (hJS : J ⊆ S)
    (x : J) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion (hST.trans interior_subset),
        continuous_inclusion (hST.trans interior_subset)⟩ : C(S, T)) (Set.inclusion hJS x)) := by
  have hST' : S ⊆ T := hST.trans interior_subset
  let iJS : C(J, S) := ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let iST : C(S, T) := ⟨Set.inclusion hST', continuous_inclusion hST'⟩
  have hJT : Function.Bijective (FundamentalGroup.map (iST.comp iJS) x) := by
    have hbij := fundamentalGroup_map_inclusion_bijective_of_isSpine hJ (hJS.trans hST') x
    have heq : (⟨Set.inclusion (hJS.trans hST'), continuous_inclusion (hJS.trans hST')⟩ :
        C(J, T)) = iST.comp iJS := ContinuousMap.ext fun _ => rfl
    rw [heq] at hbij
    exact hbij
  have hJS' : Function.Bijective (FundamentalGroup.map iJS x) :=
    fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus hS hT hST hJ
      hJS x
  rw [fundamentalGroup_map_continuousMap_comp, MonoidHom.coe_comp] at hJT
  exact (Function.Bijective.of_comp_iff _ hJS').mp hJT

theorem fundamentalGroup_map_inclusion_transfer {G S U : Set (EuclideanSpace ℝ (Fin 3))}
    (hGS : G ⊆ S) (hSU : S ⊆ U) (x : G)
    (hbij : Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSU, continuous_inclusion hSU⟩ : C(S, U)) (Set.inclusion hGS x))) :
    (Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hGS, continuous_inclusion hGS⟩ : C(G, S)) x) ↔
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion (hGS.trans hSU), continuous_inclusion (hGS.trans hSU)⟩ : C(G, U)) x)) ∧
    ((∀ g, FundamentalGroup.map
        (⟨Set.inclusion hGS, continuous_inclusion hGS⟩ : C(G, S)) x g = 1) ↔
      ∀ g, FundamentalGroup.map
        (⟨Set.inclusion (hGS.trans hSU), continuous_inclusion (hGS.trans hSU)⟩ : C(G, U)) x g
          = 1) := by
  let iGS : C(G, S) := ⟨Set.inclusion hGS, continuous_inclusion hGS⟩
  let iSU : C(S, U) := ⟨Set.inclusion hSU, continuous_inclusion hSU⟩
  have heq : (⟨Set.inclusion (hGS.trans hSU), continuous_inclusion (hGS.trans hSU)⟩ :
      C(G, U)) = iSU.comp iGS := ContinuousMap.ext fun _ => rfl
  rw [heq, fundamentalGroup_map_continuousMap_comp]
  refine ⟨?_, ?_⟩
  · rw [MonoidHom.coe_comp]
    exact (Function.Surjective.of_comp_iff' hbij _).symm
  · constructor
    · intro hone g
      rw [MonoidHom.comp_apply, hone g, map_one]
    · intro hone g
      apply hbij.1
      rw [map_one, ← MonoidHom.comp_apply]
      exact hone g

theorem fundamentalGroup_map_inclusion_transfer_pair
    {G Sa Sb U : Set (EuclideanSpace ℝ (Fin 3))} (hGa : G ⊆ Sa) (hGb : G ⊆ Sb)
    (hSaU : Sa ⊆ U) (hSbU : Sb ⊆ U) (x : G)
    (hbija : Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSaU, continuous_inclusion hSaU⟩ : C(Sa, U)) (Set.inclusion hGa x)))
    (hbijb : Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSbU, continuous_inclusion hSbU⟩ : C(Sb, U)) (Set.inclusion hGb x))) :
    (Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hGa, continuous_inclusion hGa⟩ : C(G, Sa)) x) ↔
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hGb, continuous_inclusion hGb⟩ : C(G, Sb)) x)) ∧
    ((∀ g, FundamentalGroup.map
        (⟨Set.inclusion hGa, continuous_inclusion hGa⟩ : C(G, Sa)) x g = 1) ↔
      ∀ g, FundamentalGroup.map
        (⟨Set.inclusion hGb, continuous_inclusion hGb⟩ : C(G, Sb)) x g = 1) := by
  obtain ⟨h1a, h2a⟩ := fundamentalGroup_map_inclusion_transfer hGa hSaU x hbija
  obtain ⟨h1b, h2b⟩ := fundamentalGroup_map_inclusion_transfer hGb hSbU x hbijb
  exact ⟨h1a.trans h1b.symm, h2a.trans h2b.symm⟩

end FundamentalGroupTransfer

section Leaves

theorem exists_generalPosition_solidTorus_triple
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))} {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {N : Set (EuclideanSpace ℝ (Fin 3))} {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hc : IsRevolvedTorusChain P D Dint J A S T) (hN : N = ⋃ j, S j)
    (hh : IsEmbedding (N.domRestrict h)) (S' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (hS' : ∀ j, IsCombinatorialSolidTorus (S' j) ∧ h '' A j ⊆ interior (S' j) ∧
      S' j ⊆ interior (h '' S j)) :
    ∃ S'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ j, IsCombinatorialSolidTorus (S'' j) ∧ h '' A j ⊆ interior (S'' j) ∧
        S'' j ⊆ interior (h '' S j)) ∧
      (∀ j : Fin 2, ∀ x ∈ frontier (S'' j.castSucc) ∩ frontier (S'' j.succ),
        HasPLCrossingAt (frontier (S'' j.castSucc)) (frontier (S'' j.succ)) x) ∧
      ∀ j : Fin 2, ∃ (ι : Type) (_ : Finite ι) (G : ι → Set (EuclideanSpace ℝ (Fin 3))),
        (∀ i, IsPLSphere 1 (G i)) ∧ (Pairwise fun i i' => Disjoint (G i) (G i')) ∧
          frontier (S'' j.castSucc) ∩ frontier (S'' j.succ) = ⋃ i, G i := by
  have hSN : ∀ j, S j ⊆ N := fun j => by
    rw [hN]
    exact subset_iUnion S j
  have hA : ∀ j, IsCompact (h '' A j) := fun j => by
    have hseg : IsCompact (A j) := by
      rw [hc.annulusEq j, segment_eq_image ℝ]
      exact isCompact_revolutionOf (isCompact_Icc.image (by fun_prop))
    refine hseg.image_of_continuousOn ?_
    exact (continuousOn_iff_continuous_domRestrict.mpr hh.continuous).mono
      ((hc.annulusSubset j).trans (interior_subset.trans (hSN j)))
  obtain ⟨S₁, hS₁, hGP₁⟩ := exists_generalPosition_solidTorus_relative (hA 1) isOpen_interior
    (hS' 1) ![S' 0] (fun i => by fin_cases i; exact (hS' 0).1)
  obtain ⟨S₂, hS₂, hGP₂⟩ := exists_generalPosition_solidTorus_relative (hA 2) isOpen_interior
    (hS' 2) ![S' 0, S₁] (fun i => by
      fin_cases i
      · exact (hS' 0).1
      · exact hS₁.1)
  have h01 : PairGP (S' 0) S₁ := (hGP₁ 0).symm
  have h12 : PairGP S₁ S₂ := (hGP₂ 1).symm
  refine ⟨![S' 0, S₁, S₂], fun j => ?_, fun j => ?_, fun j => ?_⟩
  · fin_cases j
    · exact hS' 0
    · exact hS₁
    · exact hS₂
  · fin_cases j
    · exact h01.1
    · exact h12.1
  · fin_cases j
    · exact h01.2
    · exact h12.2

end Leaves

section Inhabitants

theorem isRevolvedTorusChain_of_isPlanarCellChain {P : Fin 4 → EuclideanSpace ℝ (Fin 3)}
    {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))} (hc : IsPlanarCellChain P D Dint) :
    IsRevolvedTorusChain P D Dint (fun j => revolutionOf {P j})
      (fun j => revolutionOf (segment ℝ (P j.castSucc) (P j.succ)))
      (fun j => revolutionOf (D j)) (fun j => frontier (revolutionOf (D j))) := by
  refine ⟨hc, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun j => ?_, fun _ => rfl, fun j => ?_⟩
  · obtain ⟨φ, -, -, -⟩ := isSpine_revolutionOf_of_mem_cellInterior (hc.cell j) (hc.halfPlane j)
      (hc.segmentSubset j (left_mem_segment ℝ _ _))
    exact ⟨φ.symm⟩
  · exact (revolutionOf_mono (hc.segmentSubset j)).trans
      (revolutionOf_cellInterior_subset_interior (hc.cell j) (hc.halfPlane j))

theorem isRevolvedTorusChain_standard :
    IsRevolvedTorusChain standardChainPoint standardChainCell standardChainCellInterior
      (fun j => revolutionOf {standardChainPoint j})
      (fun j => revolutionOf (segment ℝ (standardChainPoint j.castSucc)
        (standardChainPoint j.succ)))
      (fun j => revolutionOf (standardChainCell j))
      (fun j => frontier (revolutionOf (standardChainCell j))) :=
  isRevolvedTorusChain_of_isPlanarCellChain isPlanarCellChain_standard

end Inhabitants

section Assemblies

theorem moise313 : Moise313 := by
  intro P D Dint J A S T N h S'' T'' hc
  have hinj : InjOn h N := Set.injOn_iff_injective.mpr hc.isEmbedding.injective
  have hSN : ∀ j, S j ⊆ N := fun j => by
    rw [hc.unionEq]
    exact subset_iUnion S j
  have hS02 : S 0 ∩ S 2 = ∅ := by
    rw [hc.base.solidEq 0, hc.base.solidEq 2, revolutionOf_inter, hc.base.chain.apart,
      revolutionOf_empty]
  have himg : h '' S 0 ∩ h '' S 2 = ∅ := by
    rw [← hinj.image_inter (hSN 0) (hSN 2), hS02, image_empty]
  refine subset_empty_iff.mp ?_
  calc S'' 0 ∩ S'' 2 ⊆ h '' S 0 ∩ h '' S 2 :=
        inter_subset_inter ((hc.innerSubset 0).trans interior_subset)
          ((hc.innerSubset 2).trans interior_subset)
    _ = ∅ := himg

theorem moise312 : Moise312 := by
  intro P D Dint J A S T N h S'' T'' hc j k hk hsub x
  have hSN : S j ⊆ N := by
    rw [hc.unionEq]
    exact subset_iUnion S j
  have hemb : IsEmbedding ((S j).domRestrict h) := isEmbedding_domRestrict_mono hc.isEmbedding hSN
  have hPk : P k ∈ Dint j := by
    rcases hk with rfl | rfl
    · exact hc.base.chain.segmentSubset j (left_mem_segment ℝ _ _)
    · exact hc.base.chain.segmentSubset j (right_mem_segment ℝ _ _)
  have hspine : IsSpine (S j) (J k) := by
    rw [hc.base.solidEq j, hc.base.circleEq k]
    exact isSpine_revolutionOf_of_mem_cellInterior (hc.base.chain.cell j)
      (hc.base.chain.halfPlane j) hPk
  have hT : IsTopologicalSolidTorus (h '' S j) :=
    isTopologicalSolidTorus_image_of_isEmbedding hemb (hc.base.isSolidTorus j)
  exact (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
    (hc.isPolyhedralSolidTorus j).1 hT (hc.innerSubset j)
    (isSpine_image_of_isEmbedding hemb hspine) hsub x).2

theorem moise311 (h307 : Moise307) : Moise311 := by
  intro P D Dint J A S T N h hc hN hh
  have hSN : ∀ j, S j ⊆ N := fun j => by
    rw [hN]
    exact subset_iUnion S j
  have hT : ∀ j, IsTopologicalSolidTorus (h '' S j) := fun j =>
    isTopologicalSolidTorus_image_of_isEmbedding (isEmbedding_domRestrict_mono hh (hSN j))
      (hc.isSolidTorus j)
  have hstep : ∀ j, ∃ S' : Set (EuclideanSpace ℝ (Fin 3)), IsCombinatorialSolidTorus S' ∧
      h '' A j ⊆ interior S' ∧ S' ⊆ interior (h '' S j) := by
    intro j
    obtain ⟨S₁, hS₁, hAS₁, hS₁S, hshell⟩ :=
      exists_innerSolidTorus_toroidalShell_of_annulusImage hc hN hh j
    obtain ⟨S', hcyl, hS₁S', hS'S⟩ := h307 S₁ (h '' S j) hS₁ (hT j) hS₁S hshell
    exact ⟨S', isCombinatorialSolidTorus_of_hasCylindricalDiagram hcyl,
      hAS₁.trans (interior_subset.trans hS₁S'), hS'S⟩
  choose S' hS' using hstep
  obtain ⟨S'', hS'', hcross, hpoly⟩ := exists_generalPosition_solidTorus_triple hc hN hh S' hS'
  exact ⟨S'', fun j => frontier (S'' j),
    { base := hc
      unionEq := hN
      isEmbedding := hh
      isPolyhedralSolidTorus := fun j => (hS'' j).1
      boundaryEq := fun _ => rfl
      annulusImageSubset := fun j => (hS'' j).2.1
      innerSubset := fun j => (hS'' j).2.2
      crossing := hcross
      polygons := hpoly }⟩

theorem exists_isCanonicalConfiguration_standard (h307 : Moise307) :
    ∃ S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)),
      IsCanonicalConfiguration standardChainPoint standardChainCell standardChainCellInterior
        (fun j => revolutionOf {standardChainPoint j})
        (fun j => revolutionOf (segment ℝ (standardChainPoint j.castSucc)
          (standardChainPoint j.succ)))
        (fun j => revolutionOf (standardChainCell j))
        (fun j => frontier (revolutionOf (standardChainCell j)))
        (⋃ j, revolutionOf (standardChainCell j)) id S'' T'' :=
  moise311 h307 _ _ _ _ _ _ _ _ id isRevolvedTorusChain_standard rfl IsEmbedding.subtypeVal

theorem polygon_dichotomy_of_carrier {Sa Sb U K Z G : Set (EuclideanSpace ℝ (Fin 3))}
    (hSa : IsCombinatorialSolidTorus Sa) (hSb : IsCombinatorialSolidTorus Sb)
    (hSaU : Sa ⊆ U) (hSbU : Sb ⊆ U)
    (hUa : ∀ x : Sa, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSaU, continuous_inclusion hSaU⟩ : C(Sa, U)) x))
    (hUb : ∀ x : Sb, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSbU, continuous_inclusion hSbU⟩ : C(Sb, U)) x))
    (hK : IsPLSphere 1 K) (hKa : K ⊆ frontier Sa) (hKb : K ⊆ interior Sb)
    (hKgen : CarriesFundamentalGroupOnto K Sa) (hZ : Z.Nonempty) (hZa : Z ⊆ interior Sa)
    (hZb : Z ⊆ interior Sb) (hZgen : CarriesFundamentalGroupOnto Z Sb)
    (hG : IsPLSphere 1 G) (hGa : G ⊆ frontier Sa) (hGb : G ⊆ frontier Sb) :
    ((∀ hsub : G ⊆ Sa, ∀ x : G, Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, Sa)) x)) ∧
      ∀ hsub : G ⊆ Sb, ∀ x : G, Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, Sb)) x)) ∨
    ((∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier Sa ∧
          G = r '' stdSimplexBoundary 2) ∧
      ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier Sb ∧
          G = r '' stdSimplexBoundary 2) := by
  have hGK : Disjoint G K := (disjoint_interior_frontier (s := Sb)).symm.mono hGb hKb
  have hGSa : G ⊆ Sa := hGa.trans (isClosed_of_isTopologicalSolidTorus hSa.1).frontier_subset
  have hGSb : G ⊆ Sb := hGb.trans (isClosed_of_isTopologicalSolidTorus hSb.1).frontier_subset
  have htransfer := fun x : G =>
    fundamentalGroup_map_inclusion_transfer_pair hGSa hGSb hSaU hSbU x (hUa _) (hUb _)
  rcases carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier hSa hK hKa hKgen hG hGa
    hGK with hgen | ⟨Δ, r, hr, hΔ, hGΔ⟩
  · left
    exact ⟨fun hsub x => hgen.2 hsub x, fun hsub x => (htransfer x).1.mp (hgen.2 hGSa x)⟩
  · right
    refine ⟨⟨Δ, r, hr, hΔ, hGΔ⟩, ?_⟩
    have hGΔ' : G ⊆ Δ := by
      rw [hGΔ, ← hr.1.image_eq]
      exact image_mono fun y hy => hy.1
    have hΔSa : Δ ⊆ Sa := hΔ.trans (isClosed_of_isTopologicalSolidTorus hSa.1).frontier_subset
    have hnull : ∀ (x : G) (g : FundamentalGroup G x), FundamentalGroup.map
        (⟨Set.inclusion hGSa, continuous_inclusion hGSa⟩ : C(G, Sa)) x g = 1 := fun x g =>
      DifferentialGeometry.Topology.fundamentalGroup_map_eq_one_of_nullhomotopic _
        (IsPLBall.nullhomotopic_inclusion (⟨r, hr⟩ : IsPLBall 2 Δ) hGΔ' hΔSa) x g
    have hΔZ : Disjoint Δ Z := (disjoint_interior_frontier (s := Sa)).symm.mono hΔ hZa
    exact exists_isPLCell_frontier_of_polygon_nullhomotopic hSb hGb hr hGΔ hΔZ hZ hZb hZgen
      fun _ x g => (htransfer x).2.mp (hnull x) g

theorem moise314_pair {P : Fin 4 → EuclideanSpace ℝ (Fin 3)}
    {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))} {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))} {N : Set (EuclideanSpace ℝ (Fin 3))}
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsCanonicalConfiguration P D Dint J A S T N h S'' T'') (a b : Fin 3) (m o : Fin 4)
    (hma : m = a.castSucc ∨ m = a.succ) (hmb : m = b.castSucc ∨ m = b.succ)
    (hob : o = b.castSucc ∨ o = b.succ) (hPo : P o ∉ D a)
    (hunion : ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (D a ∪ D b) Eint ∧ P m ∈ Eint)
    {G : Set (EuclideanSpace ℝ (Fin 3))} (hG : IsPLSphere 1 G) (hGa : G ⊆ T'' a)
    (hGb : G ⊆ T'' b) :
    ((∀ hsub : G ⊆ S'' a, ∀ x : G, Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' a)) x)) ∧
      ∀ hsub : G ⊆ S'' b, ∀ x : G, Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' b)) x)) ∨
    ((∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' a ∧
          G = r '' stdSimplexBoundary 2) ∧
      ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' b ∧
          G = r '' stdSimplexBoundary 2) := by
  have hSN : ∀ j, S j ⊆ N := fun j => by
    rw [hc.unionEq]
    exact subset_iUnion S j
  have hJN : ∀ (j : Fin 3) (k : Fin 4), (k = j.castSucc ∨ k = j.succ) → J k ⊆ N :=
    fun j k hk => ((hc.base.circle_subset_annulus j k hk).trans (hc.base.annulusSubset j)).trans
      (interior_subset.trans (hSN j))
  have hinj : InjOn h N := Set.injOn_iff_injective.mpr hc.isEmbedding.injective
  have hPmem : ∀ (j : Fin 3) (k : Fin 4), (k = j.castSucc ∨ k = j.succ) → P k ∈ Dint j := by
    intro j k hk
    rcases hk with rfl | rfl
    · exact hc.base.chain.segmentSubset j (left_mem_segment ℝ _ _)
    · exact hc.base.chain.segmentSubset j (right_mem_segment ℝ _ _)
  have hT : ∀ j, IsTopologicalSolidTorus (h '' S j) := fun j =>
    isTopologicalSolidTorus_image_of_isEmbedding
      (isEmbedding_domRestrict_mono hc.isEmbedding (hSN j)) (hc.base.isSolidTorus j)
  have hspine : ∀ (j : Fin 3) (k : Fin 4), (k = j.castSucc ∨ k = j.succ) →
      IsSpine (h '' S j) (h '' J k) := by
    intro j k hk
    refine isSpine_image_of_isEmbedding (isEmbedding_domRestrict_mono hc.isEmbedding (hSN j)) ?_
    rw [hc.base.solidEq j, hc.base.circleEq k]
    exact isSpine_revolutionOf_of_mem_cellInterior (hc.base.chain.cell j)
      (hc.base.chain.halfPlane j) (hPmem j k hk)
  have hgen : ∀ (j : Fin 3) (k : Fin 4), (k = j.castSucc ∨ k = j.succ) →
      CarriesFundamentalGroupOnto (h '' J k) (S'' j) := fun j k hk =>
    ⟨hc.image_circle_subset j k hk, fun hsub x =>
      (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
        (hc.isPolyhedralSolidTorus j).1 (hT j) (hc.innerSubset j) (hspine j k hk) hsub x).2⟩
  have hZa : h '' J m ⊆ interior (S'' a) :=
    (image_mono (hc.base.circle_subset_annulus a m hma)).trans (hc.annulusImageSubset a)
  have hZb : h '' J m ⊆ interior (S'' b) :=
    (image_mono (hc.base.circle_subset_annulus b m hmb)).trans (hc.annulusImageSubset b)
  have hZne : (h '' J m).Nonempty := by
    obtain ⟨h2, h0⟩ := hc.base.chain.halfPlane a (P m)
      (hc.base.chain.interiorSubset a (hPmem a m hma))
    refine ⟨h (P m), P m, ?_, rfl⟩
    rw [hc.base.circleEq m]
    exact mem_revolutionOf_self (mem_singleton _) h2 h0.le
  have hZ₀ne : (h '' J o).Nonempty := by
    obtain ⟨h2, h0⟩ := hc.base.chain.halfPlane b (P o)
      (hc.base.chain.interiorSubset b (hPmem b o hob))
    refine ⟨h (P o), P o, ?_, rfl⟩
    rw [hc.base.circleEq o]
    exact mem_revolutionOf_self (mem_singleton _) h2 h0.le
  have hZ₀b : h '' J o ⊆ interior (S'' b) :=
    (image_mono (hc.base.circle_subset_annulus b o hob)).trans (hc.annulusImageSubset b)
  have hZ₀a : Disjoint (h '' J o) (S'' a) := by
    have hJS : J o ∩ S a = ∅ := by
      rw [hc.base.circleEq o, hc.base.solidEq a, revolutionOf_inter,
        singleton_inter_eq_empty.mpr hPo, revolutionOf_empty]
    have himg : h '' J o ∩ h '' S a = ∅ := by
      rw [← hinj.image_inter (hJN b o hob) (hSN a), hJS, image_empty]
    exact Set.disjoint_of_subset_right ((hc.innerSubset a).trans interior_subset)
      (Set.disjoint_iff_inter_eq_empty.mpr himg)
  obtain ⟨K, hK, hKsub, hKgen⟩ := exists_polygon_carrier_of_spine (hc.isPolyhedralSolidTorus b)
    (hc.isPolyhedralSolidTorus a) (hT b) (hT a) (hc.innerSubset b) (hc.innerSubset a)
    (hspine b m hmb) (hspine a m hma) hZb hZa hZ₀ne hZ₀b hZ₀a (hgen b o hob)
  obtain ⟨Eint, hE, hPmE⟩ := hunion
  have hUspine : IsSpine (h '' (S a ∪ S b)) (h '' J m) := by
    have hhalf : ∀ q ∈ D a ∪ D b, q 2 = 0 ∧ 0 < q 0 := fun q hq =>
      hq.elim (hc.base.chain.halfPlane a q) (hc.base.chain.halfPlane b q)
    have hrev := isSpine_revolutionOf_of_mem_cellInterior hE hhalf hPmE
    rw [revolutionOf_union, ← hc.base.solidEq a, ← hc.base.solidEq b, ← hc.base.circleEq m]
      at hrev
    exact isSpine_image_of_isEmbedding
      (isEmbedding_domRestrict_mono hc.isEmbedding (union_subset (hSN a) (hSN b))) hrev
  have hUtorus : IsTopologicalSolidTorus (h '' (S a ∪ S b)) := by
    obtain ⟨φ, -, -, -⟩ := hUspine
    exact ⟨φ.symm⟩
  have hSaU' : S'' a ⊆ interior (h '' (S a ∪ S b)) :=
    (hc.innerSubset a).trans (interior_mono (image_mono subset_union_left))
  have hSbU' : S'' b ⊆ interior (h '' (S a ∪ S b)) :=
    (hc.innerSubset b).trans (interior_mono (image_mono subset_union_right))
  have hSaU : S'' a ⊆ h '' (S a ∪ S b) := hSaU'.trans interior_subset
  have hSbU : S'' b ⊆ h '' (S a ∪ S b) := hSbU'.trans interior_subset
  obtain ⟨y, hy⟩ := hZne
  have hUa : ∀ x : S'' a, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSaU, continuous_inclusion hSaU⟩ : C(S'' a, h '' (S a ∪ S b))) x) := by
    intro x
    let _ : PathConnectedSpace (S'' a) :=
      pathConnectedSpace_of_isTopologicalSolidTorus (hc.isPolyhedralSolidTorus a).1
    exact DifferentialGeometry.Topology.fundamentalGroup_map_bijective_of_pathConnected _ x
      (Set.inclusion (hc.image_circle_subset a m hma) ⟨y, hy⟩)
      (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_subset_interior
        (hc.isPolyhedralSolidTorus a).1 hUtorus hSaU' hUspine (hc.image_circle_subset a m hma)
        ⟨y, hy⟩)
  have hUb : ∀ x : S'' b, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hSbU, continuous_inclusion hSbU⟩ : C(S'' b, h '' (S a ∪ S b))) x) := by
    intro x
    let _ : PathConnectedSpace (S'' b) :=
      pathConnectedSpace_of_isTopologicalSolidTorus (hc.isPolyhedralSolidTorus b).1
    exact DifferentialGeometry.Topology.fundamentalGroup_map_bijective_of_pathConnected _ x
      (Set.inclusion (hc.image_circle_subset b m hmb) ⟨y, hy⟩)
      (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_subset_interior
        (hc.isPolyhedralSolidTorus b).1 hUtorus hSbU' hUspine (hc.image_circle_subset b m hmb)
        ⟨y, hy⟩)
  rw [hc.boundaryEq a] at hGa
  rw [hc.boundaryEq b] at hGb
  rw [hc.boundaryEq a, hc.boundaryEq b]
  exact polygon_dichotomy_of_carrier (hc.isPolyhedralSolidTorus a) (hc.isPolyhedralSolidTorus b)
    hSaU hSbU hUa hUb hK (hKsub.trans inter_subset_left) (hKsub.trans inter_subset_right) hKgen
    ⟨y, hy⟩ hZa hZb (hgen b m hmb) hG hGa hGb

theorem moise314 : Moise314 := by
  intro P D Dint J A S T N h S'' T'' hc j G hG hGsub
  have hP1 : P 1 ∈ D 0 :=
    hc.base.chain.interiorSubset 0 (hc.base.chain.segmentSubset 0 (right_mem_segment ℝ _ _))
  have hP2 : P 2 ∈ D 2 :=
    hc.base.chain.interiorSubset 2 (hc.base.chain.segmentSubset 2 (left_mem_segment ℝ _ _))
  have hP2not : P 2 ∉ D 0 := fun hP => by
    have hmem : P 2 ∈ D 0 ∩ D 2 := ⟨hP, hP2⟩
    rw [hc.base.chain.apart] at hmem
    exact hmem
  have hP1not : P 1 ∉ D 2 := fun hP => by
    have hmem : P 1 ∈ D 0 ∩ D 2 := ⟨hP1, hP⟩
    rw [hc.base.chain.apart] at hmem
    exact hmem
  fin_cases j
  · obtain ⟨Eint, hE, hE0, -⟩ :=
      exists_isTopologicalCellWithInterior_union_consecutive hc.base.chain 0
    have hunion : ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
        IsTopologicalCellWithInterior 2 (D 0 ∪ D 1) Eint ∧ P 1 ∈ Eint :=
      ⟨Eint, hE, hE0 (hc.base.chain.segmentSubset 0 (right_mem_segment ℝ _ _))⟩
    rcases moise314_pair hc 0 1 1 2 (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) hP2not hunion hG
      (hGsub.trans inter_subset_left) (hGsub.trans inter_subset_right) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      intro k hk
      rcases hk with rfl | rfl
      · exact h1
      · exact h2
    · right
      intro k hk
      rcases hk with rfl | rfl
      · exact h1
      · exact h2
  · obtain ⟨Eint, hE, hE1, -⟩ :=
      exists_isTopologicalCellWithInterior_union_consecutive hc.base.chain 1
    have hunion : ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
        IsTopologicalCellWithInterior 2 (D 2 ∪ D 1) Eint ∧ P 2 ∈ Eint := by
      rw [union_comm]
      exact ⟨Eint, hE, hE1 (hc.base.chain.segmentSubset 1 (right_mem_segment ℝ _ _))⟩
    rcases moise314_pair hc 2 1 2 1 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) hP1not hunion hG
      (hGsub.trans inter_subset_right) (hGsub.trans inter_subset_left) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      intro k hk
      rcases hk with rfl | rfl
      · exact h2
      · exact h1
    · right
      intro k hk
      rcases hk with rfl | rfl
      · exact h2
      · exact h1

end Assemblies

end DifferentialGeometry.Topology.PiecewiseLinear
