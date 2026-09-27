/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerPolygonCarriers
import DifferentialGeometry.Topology.PiecewiseLinear.TorusTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem not_boundsDiskIn_of_carriesFundamentalGroupOnto {S G : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hG : G.Nonempty)
    (hgen : CarriesFundamentalGroupOnto G S) : ¬ boundsDiskIn G (frontier S) := by
  rintro ⟨D, r, hr, hD, hrG⟩
  have hGD : G ⊆ D := by
    rw [hrG, ← hr.image_eq]
    exact image_mono fun x hx => hx.1
  exact hS.1.not_carriesFundamentalGroupOnto_of_subset_isPLBall ⟨r, hr⟩
    (hD.trans hS.isPolyhedron.isClosed.frontier_subset) hG hGD hgen

private theorem exists_carrying_trace_circle {ι : Type*} [Finite ι]
    {S R K₀ K₁ : Set E3} {C : ι → Set E3}
    (hS : IsCombinatorialSolidTorus S) (hR : IsClosed R)
    (hK₀ : K₀.Nonempty) (h₀ : K₀ ⊆ frontier S ∩ R)
    (hgen₀ : CarriesFundamentalGroupOnto K₀ S)
    (hK₁ : IsPLSphere 1 K₁) (h₁ : K₁ ⊆ frontier S)
    (hgen₁ : CarriesFundamentalGroupOnto K₁ S) (hdis : Disjoint R K₁)
    (hC : ∀ k, IsPLSphere 1 (C k)) (hCd : Pairwise fun k l => Disjoint (C k) (C l))
    (hcover : frontier S ∩ frontier R = ⋃ k, C k) :
    ∃ k, ¬ boundsDiskIn (C k) (frontier S) ∧ CarriesFundamentalGroupOnto (C k) S := by
  have hΘ := hS.isPLTorus_frontier
  have hTS : frontier S ⊆ S := hS.isPolyhedron.isClosed.frontier_subset
  have hKsep : IsPreconnected (frontier S \ K₁) := by
    by_contra hsep
    exact not_boundsDiskIn_of_carriesFundamentalGroupOnto hS hK₁.nonempty hgen₁
      (hΘ.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hK₁ h₁ hsep)
  have hCΘ : ∀ k, C k ⊆ frontier S := fun k =>
    (subset_iUnion C k).trans (hcover.symm.subset.trans inter_subset_left)
  have hCR : ∀ k, C k ⊆ R := fun k =>
    (subset_iUnion C k).trans
      (hcover.symm.subset.trans (inter_subset_right.trans hR.frontier_subset))
  have hCK : ∀ k, Disjoint (C k) K₁ := fun k => hdis.mono (hCR k) Subset.rfl
  let W := frontier S ∩ R
  have hWfr : W ∩ closure (frontier S \ W) ⊆ ⋃ k, C k := by
    have hcl : closure (frontier S \ W) ⊆ (interior R)ᶜ :=
      closure_minimal (fun x hx hxi => hx.2 ⟨hx.1, interior_subset hxi⟩)
        isOpen_interior.isClosed_compl
    intro x hx
    rw [← hcover]
    exact ⟨hx.1.1, subset_closure hx.1.2, hcl hx.2⟩
  have hWS : CarriesFirstHomologyOnto W S :=
    (hgen₀.carriesFirstHomologyOnto hK₀ hS.1.isPathConnected).mono h₀
      (inter_subset_left.trans hTS)
  have hcarry : CarriesFirstHomologyOnto (⋃ k, C k) S := by
    have ht := hΘ.carriesFirstHomologyOnto_iUnion_of_disjoint
      hK₁ h₁ hKsep hC hCΘ hCd hCK inter_subset_left (isClosed_frontier.inter hR)
      (hdis.mono inter_subset_right Subset.rfl) hWfr
      continuous_id.continuousOn (fun _ _ _ _ heq => heq)
      (by simpa only [image_id] using hTS)
      (by simpa only [image_id] using hWS)
    simpa only [image_id] using ht
  obtain ⟨k, hk, -⟩ := exists_surjective_trace_circle hS hC hCΘ hCd hcarry
  have hgen := hS.carriesFundamentalGroupOnto_of_isPreconnected_sdiff
    hK₁ h₁ hgen₁ (hC k) (hCΘ k) (hCK k) hk
  exact ⟨k, not_boundsDiskIn_of_carriesFundamentalGroupOnto hS (hC k).nonempty hgen, hgen⟩

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.exists_essential_seam_lower
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ G ∈ traceCircles (T'' (i - 1)) (T'' i), ¬ boundsDiskIn G (T'' i) ∧
      CarriesFundamentalGroupOnto G (S'' i) := by
  obtain ⟨Klo, Khi, hlo, hhi, hlosub, hhisub, -, hlogen, hhigen⟩ :=
    htw.exists_disjoint_polygon_carriers i
  obtain ⟨ι, hι, G, hG, hGdis, hcover⟩ := (htw.config (i - 1)).polygons 0
  let _ := hι
  have hcover' : T'' (i - 1) ∩ T'' i = ⋃ k, G k := by simpa using hcover
  have hcover'' : frontier (S'' i) ∩ frontier (S'' (i - 1)) = ⋃ k, G k := by
    rw [← htw.boundary_eq, ← htw.boundary_eq, inter_comm]
    exact hcover'
  have hsolid : IsCombinatorialSolidTorus (S'' i) := by
    simpa using (htw.config i).isPolyhedralSolidTorus 0
  have hlo' : Klo ⊆ frontier (S'' i) ∩ S'' (i - 1) := by
    rw [← htw.boundary_eq]
    exact hlosub.trans (inter_subset_inter_right _ interior_subset)
  have hhi' : Khi ⊆ frontier (S'' i) := by
    rw [← htw.boundary_eq]
    exact hhisub.trans inter_subset_left
  have hdis : Disjoint (S'' (i - 1)) Khi :=
    (htw.solid_disjoint (i := i - 1) (k := i + 1) (by rw [le_abs]; omega)).mono
      Subset.rfl (hhisub.trans (inter_subset_right.trans interior_subset))
  obtain ⟨k, hk, hgen⟩ := exists_carrying_trace_circle hsolid
    (htw.solid_isPolyhedron (i - 1)).isClosed hlo.nonempty hlo' hlogen
    hhi hhi' hhigen hdis hG hGdis hcover''
  refine ⟨G k, ?_, ?_, hgen⟩
  · rw [traceCircles_eq_range_of_finite_circle_union hG hGdis hcover']
    exact mem_range_self k
  · rwa [htw.boundary_eq]

theorem IsCanonicalTower.exists_essential_seam_upper
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ G ∈ traceCircles (T'' i) (T'' (i + 1)), ¬ boundsDiskIn G (T'' i) ∧
      CarriesFundamentalGroupOnto G (S'' i) := by
  obtain ⟨Klo, Khi, hlo, hhi, hlosub, hhisub, -, hlogen, hhigen⟩ :=
    htw.exists_disjoint_polygon_carriers i
  obtain ⟨ι, hι, G, hG, hGdis, hcover⟩ := (htw.config i).polygons 0
  let _ := hι
  have hcover' : T'' i ∩ T'' (i + 1) = ⋃ k, G k := by simpa using hcover
  have hcover'' : frontier (S'' i) ∩ frontier (S'' (i + 1)) = ⋃ k, G k := by
    rw [← htw.boundary_eq, ← htw.boundary_eq]
    exact hcover'
  have hsolid : IsCombinatorialSolidTorus (S'' i) := by
    simpa using (htw.config i).isPolyhedralSolidTorus 0
  have hhi' : Khi ⊆ frontier (S'' i) ∩ S'' (i + 1) := by
    rw [← htw.boundary_eq]
    exact hhisub.trans (inter_subset_inter_right _ interior_subset)
  have hlo' : Klo ⊆ frontier (S'' i) := by
    rw [← htw.boundary_eq]
    exact hlosub.trans inter_subset_left
  have hdis : Disjoint (S'' (i + 1)) Klo :=
    (htw.solid_disjoint (i := i + 1) (k := i - 1) (by rw [le_abs]; omega)).mono
      Subset.rfl (hlosub.trans (inter_subset_right.trans interior_subset))
  obtain ⟨k, hk, hgen⟩ := exists_carrying_trace_circle hsolid
    (htw.solid_isPolyhedron (i + 1)).isClosed hhi.nonempty hhi' hhigen
    hlo hlo' hlogen hdis hG hGdis hcover''
  refine ⟨G k, ?_, ?_, hgen⟩
  · rw [traceCircles_eq_range_of_finite_circle_union hG hGdis hcover']
    exact mem_range_self k
  · rwa [htw.boundary_eq]

theorem IsCanonicalTower.exists_essential_oddPiece_seams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ Glo Ghi : Set E3,
      Glo ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i)) ∧
      Ghi ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn Glo (T'' (2 * i + 1)) ∧
      ¬ boundsDiskIn Ghi (T'' (2 * i + 1)) ∧ Disjoint Glo Ghi ∧
      CarriesFundamentalGroupOnto Glo (S'' (2 * i + 1)) ∧
      CarriesFundamentalGroupOnto Ghi (S'' (2 * i + 1)) := by
  obtain ⟨Glo, hlo, hloe, hlogen⟩ := htw.exists_essential_seam_lower (2 * i + 1)
  obtain ⟨Ghi, hhi, hhie, hhigen⟩ := htw.exists_essential_seam_upper (2 * i + 1)
  have hlo' : Glo ∈ traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) := by simpa using hlo
  have hhi' : Ghi ∈ traceCircles (T'' (2 * i + 1)) (T'' (2 * (i + 1))) := by
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using hhi
  refine ⟨Glo, Ghi, ?_, ?_, hloe, hhie, ?_, hlogen, hhigen⟩
  · simpa only [traceCircles, htw.oddPiece_inter_even, inter_comm] using hlo'
  · simpa only [traceCircles, htw.oddPiece_inter_even] using hhi'
  · apply (htw.solid_disjoint (i := 2 * i) (k := 2 * (i + 1))
      (by rw [le_abs]; omega)).mono
    · exact (traceCircles_subset hlo').trans
        (inter_subset_left.trans (htw.boundary_subset_solid _))
    · exact (traceCircles_subset hhi').trans
        (inter_subset_right.trans (htw.boundary_subset_solid _))

end DifferentialGeometry.Topology.PiecewiseLinear
