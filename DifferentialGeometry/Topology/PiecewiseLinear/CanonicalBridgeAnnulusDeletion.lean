/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCyclePatchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningAnnulusDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.bridge_component_inter_even
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (c : ConnectedComponents (X i).space) {J₀ J₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (h₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i)))
    (h₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1)))) :
    (connectedComponentComplex (X i) c).space ∩ T'' (2 * i) = J₀ ∧
      (connectedComponentComplex (X i) c).space ∩ T'' (2 * (i + 1)) = J₁ := by
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let L := connectedComponentComplex (X i) c
  let _ : Finite L.faces := (connectedComponentComplex_faces_finite (X i) c).to_subtype
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hLb : (boundaryComplex 2 L).space = J₀ ∪ J₁ := hC.boundaryComplex_space L
  have hTdis : Disjoint (T'' (2 * i)) (T'' (2 * (i + 1))) :=
    (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) (htw.boundary_subset_outer _)
  have hmem {x : E3} (hxL : x ∈ L.space) (k : ℤ) (hxT : x ∈ T'' (2 * k)) :
      x ∈ J₀ ∪ J₁ :=
    hLb.subset ((boundaryComplex_space_connectedComponentComplex 2 (X i) c).symm.subset
      ⟨hX.inter_even_subset_boundary htw i k ⟨hLX hxL, hxT⟩, hxL⟩)
  constructor
  · apply Subset.antisymm
    · rintro x ⟨hxL, hxT⟩
      rcases hmem hxL i hxT with hx | hx
      · exact hx
      · exact (disjoint_left.mp hTdis hxT (traceCircles_subset h₁ hx).2).elim
    · exact traceCircles_subset h₀
  · apply Subset.antisymm
    · rintro x ⟨hxL, hxT⟩
      rcases hmem hxL (i + 1) hxT with hx | hx
      · exact (disjoint_left.mp hTdis (traceCircles_subset h₀ hx).2 hxT).elim
      · exact hx
    · exact traceCircles_subset h₁

theorem IsCanonicalSurface.isSeparatorIn_after_delete_bridge_component
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (i : ℤ) (c d : ConnectedComponents (X i).space) (hcd : c ≠ d)
    {J₀ J₁ K₀ K₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (hD : IsPLAnnulusWithEnds (connectedComponentComplex (X i) d).space K₀ K₁)
    (hJ₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i)))
    (hJ₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1))))
    (hK₀ : K₀ ∈ traceCircles (connectedComponentComplex (X i) d).space (T'' (2 * i)))
    (hK₁ : K₁ ∈ traceCircles (connectedComponentComplex (X i) d).space (T'' (2 * (i + 1))))
    (hJess₀ : ¬ boundsDiskIn J₀ (T'' (2 * i + 1)))
    (hJess₁ : ¬ boundsDiskIn J₁ (T'' (2 * i + 1)))
    (hKess₀ : ¬ boundsDiskIn K₀ (T'' (2 * i + 1)))
    (hKess₁ : ¬ boundsDiskIn K₁ (T'' (2 * i + 1)))
    (hR : IsClosed (((↑) : I → E3) ⁻¹'
      (towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))))) :
    IsSeparatorIn I
      (towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))) {a} {b} := by
  let L := connectedComponentComplex (X i) c
  let R := connectedComponentComplex (X i) d
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun q => (connectedComponentComplex (X i) q).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hRX : R.space ⊆ (X i).space :=
    (subset_iUnion (fun q => (connectedComponentComplex (X i) q).space) d).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hLR : Disjoint L.space R.space :=
    pairwise_disjoint_connectedComponentComplex_space (X i) hcd
  have hsolid (k : ℤ) : IsCombinatorialSolidTorus (S'' (2 * k)) := by
    simpa using (htw.config (2 * k)).isPolyhedralSolidTorus 0
  have hJlo : ¬ boundsDiskIn J₀ (T'' (2 * i)) :=
    fun hd => hJess₀ ((hX.lower_component_boundsDiskIn_iff htw h314 i c hJ₀).mp hd)
  have hJhi : ¬ boundsDiskIn J₁ (T'' (2 * (i + 1))) :=
    fun hd => hJess₁ ((hX.upper_component_boundsDiskIn_iff htw h314 i c hJ₁).mp hd)
  have hKlo : ¬ boundsDiskIn K₀ (T'' (2 * i)) :=
    fun hd => hKess₀ ((hX.lower_component_boundsDiskIn_iff htw h314 i d hK₀).mp hd)
  have hKhi : ¬ boundsDiskIn K₁ (T'' (2 * (i + 1))) :=
    fun hd => hKess₁ ((hX.upper_component_boundsDiskIn_iff htw h314 i d hK₁).mp hd)
  have hdislo : Disjoint J₀ K₀ := hLR.mono
    ((traceCircles_subset hJ₀).trans inter_subset_left)
    ((traceCircles_subset hK₀).trans inter_subset_left)
  have hdishi : Disjoint J₁ K₁ := hLR.mono
    ((traceCircles_subset hJ₁).trans inter_subset_left)
    ((traceCircles_subset hK₁).trans inter_subset_left)
  have hfront {k : ℤ} {G C : Set E3} (hG : G ∈ traceCircles C (T'' (2 * k))) :
      G ⊆ frontier (S'' (2 * k)) :=
    fun _ hx => (htw.boundary_eq _).subset (traceCircles_subset hG hx).2
  obtain ⟨B₀, B₀', hB₀, -, hB₀union, hB₀meet⟩ :=
    (hsolid i).exists_annulus_pair_of_essential_circles (traceCircles_isPLSphere hJ₀)
      (traceCircles_isPLSphere hK₀) (hfront hJ₀) (hfront hK₀) hdislo
      (by simpa only [← htw.boundary_eq] using hJlo)
      (by simpa only [← htw.boundary_eq] using hKlo)
  obtain ⟨B₁, B₁', hB₁, -, hB₁union, hB₁meet⟩ :=
    (hsolid (i + 1)).exists_annulus_pair_of_essential_circles (traceCircles_isPLSphere hJ₁)
      (traceCircles_isPLSphere hK₁) (hfront hJ₁) (hfront hK₁) hdishi
      (by simpa only [← htw.boundary_eq] using hJhi)
      (by simpa only [← htw.boundary_eq] using hKhi)
  have hB₀T : B₀ ⊆ T'' (2 * i) :=
    subset_union_left.trans (hB₀union.trans (htw.boundary_eq _).symm).subset
  have hB₁T : B₁ ⊆ T'' (2 * (i + 1)) :=
    subset_union_left.trans (hB₁union.trans (htw.boundary_eq _).symm).subset
  have hBB : Disjoint B₀ B₁ :=
    (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega)).mono
      (hB₀T.trans (htw.boundary_subset_outer _))
      (hB₁T.trans (htw.boundary_subset_outer _))
  obtain ⟨hClo, hChi⟩ := hX.bridge_component_inter_even htw i c hC hJ₀ hJ₁
  obtain ⟨hDlo, hDhi⟩ := hX.bridge_component_inter_even htw i d hD hK₀ hK₁
  have hinter {C B T G : Set E3} (hCT : C ∩ T = G) (hBT : B ⊆ T) (hGB : G ⊆ B) :
      C ∩ B = G :=
    Subset.antisymm ((inter_subset_inter_right _ hBT).trans hCT.subset)
      (fun _ hx => ⟨(hCT.symm.subset hx).1, hGB hx⟩)
  have h₀₀ : L.space ∩ B₀ = J₀ := hinter hClo hB₀T
    (fun _ hx => (hB₀meet.symm.subset (Or.inl hx)).1)
  have h₀₁ : L.space ∩ B₁ = J₁ := hinter hChi hB₁T
    (fun _ hx => (hB₁meet.symm.subset (Or.inl hx)).1)
  have h₁₀ : R.space ∩ B₀ = K₀ := hinter hDlo hB₀T
    (fun _ hx => (hB₀meet.symm.subset (Or.inr hx)).1)
  have h₁₁ : R.space ∩ B₁ = K₁ := hinter hDhi hB₁T
    (fun _ hx => (hB₁meet.symm.subset (Or.inr hx)).1)
  let V := (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪ φ '' S (2 * (i + 1))
  have hV : IsTopologicalSolidTorus V := by
    simpa only [V, show 2 * (i + 1) = 2 * i + 2 by omega] using
      htw.outer_triple_isTopologicalSolidTorus (2 * i)
  have hVI : V ⊆ I :=
    union_subset (union_subset (htw.subsetInterior _) (htw.subsetInterior _))
      (htw.subsetInterior _)
  have hTV (k : ℤ) (hk : φ '' S (2 * k) ⊆ V) : T'' (2 * k) ⊆ interior V := by
    have hinner : S'' (2 * k) ⊆ interior (φ '' S (2 * k)) := by
      simpa using (htw.config (2 * k)).innerSubset 0
    exact (htw.boundary_subset_solid _).trans (hinner.trans (interior_mono hk))
  have hQsub : (L.space ∪ R.space) ∪ (B₀ ∪ B₁) ⊆ interior V :=
    union_subset (union_subset (hLX.trans (hX.interiorCarrier i))
      (hRX.trans (hX.interiorCarrier i)))
      (union_subset (hB₀T.trans (hTV i (subset_union_left.trans subset_union_left)))
        (hB₁T.trans (hTV (i + 1) subset_union_right)))
  have hrowM : (X i).space ⊆ towerSurface T'' (fun j => (X j).space) P' :=
    fun _ hx => Or.inl (mem_iUnion.mpr ⟨i, Or.inr hx⟩)
  have htorusM (k : ℤ) : T'' (2 * k) ⊆ towerSurface T'' (fun j => (X j).space) P' :=
    fun _ hx => Or.inl (mem_iUnion.mpr ⟨k, Or.inl hx⟩)
  have hQM : (L.space ∪ R.space) ∪ (B₀ ∪ B₁) ⊆
      towerSurface T'' (fun j => (X j).space) P' :=
    union_subset (union_subset (hLX.trans hrowM) (hRX.trans hrowM))
      (union_subset (hB₀T.trans (htorusM i)) (hB₁T.trans (htorusM (i + 1))))
  have hVavoid : Disjoint V ({a, b} : Set E3) :=
    ((havoid (2 * i)).union_left (havoid (2 * i + 1))).union_left
      (havoid (2 * (i + 1)))
  exact ⟨hR, hC.separates_after_delete_annulus_cycle_patch hD hB₀ hB₁ hLR hBB
    h₀₀ h₀₁ h₁₀ h₁₁ hI hV hVI hQsub hQM hR
    (fun hx => disjoint_left.mp hVavoid hx (Or.inl rfl))
    (fun hx => disjoint_left.mp hVavoid hx (Or.inr rfl)) hX.separator.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
