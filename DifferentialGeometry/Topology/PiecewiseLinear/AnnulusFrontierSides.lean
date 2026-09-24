/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusOnPolyhedralCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderFrontierSides

/-! # Annulus Frontier Sides -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isAnnulusOn_with_frontier_sides
    {X : Type*} [TopologicalSpace X] {A D : Set X} (hD : IsClosed D)
    (φ : (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ A) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hfront : A ∩ frontier D = Subtype.val '' (φ '' {p | p.1.2 = t}))
    (hin : (A ∩ interior D).Nonempty) (hout : (A \ D).Nonempty) :
    ∃ A₀ A₁ : Set X, IsAnnulusOn A A₀ A₁ ∧ A₀ ⊆ interior D ∧ A₁ ∩ D = ∅ ∧
      IsConnected (A ∩ D) ∧ IsConnected (A \ D) := by
  have : ConnectedSpace (stdSimplexBoundary 2) :=
    isConnected_iff_connectedSpace.mp (isConnected_stdSimplexBoundary 0)
  let e := (Homeomorph.Set.prod (stdSimplexBoundary 2) (Icc (0 : ℝ) 1)).symm
  let θ := e.trans φ
  let f : stdSimplexBoundary 2 × Icc (0 : ℝ) 1 → X := fun p => θ p
  have hf : Continuous f := continuous_subtype_val.comp θ.continuous
  have hrange : range f = A := by
    apply Subset.antisymm
    · rintro x ⟨p, rfl⟩
      exact (θ p).2
    · intro x hx
      exact ⟨θ.symm ⟨x, hx⟩, congrArg Subtype.val (θ.apply_symm_apply ⟨x, hx⟩)⟩
  have hfFront (p) : f p ∈ frontier D ↔ (p.2 : ℝ) = t := by
    constructor
    · intro hp
      obtain ⟨y, ⟨q, hq, rfl⟩, hqp⟩ := hfront.subset ⟨(θ p).2, hp⟩
      have heq : q = e p := φ.injective (Subtype.ext hqp)
      rw [heq] at hq
      exact hq
    · intro hp
      exact (hfront.symm.subset ⟨φ (e p), ⟨e p, hp, rfl⟩, rfl⟩).2
  have hfi : ∃ p, f p ∈ interior D := by
    obtain ⟨x, hxA, hxD⟩ := hin
    obtain ⟨p, rfl⟩ := hrange.symm.subset hxA
    exact ⟨p, hxD⟩
  have hfo : ∃ p, f p ∉ D := by
    obtain ⟨x, hxA, hxD⟩ := hout
    obtain ⟨p, rfl⟩ := hrange.symm.subset hxA
    exact ⟨p, hxD⟩
  have hconn := isConnected_range_inter_and_sdiff_of_frontier_level hf hD ht hfFront hfi hfo
  rw [hrange] at hconn
  let A₀ := Subtype.val '' (φ '' {p | p.1.2 = 0})
  let A₁ := Subtype.val '' (φ '' {p | p.1.2 = 1})
  have hA : IsAnnulusOn A A₀ A₁ := isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod φ
  have hval (q : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) : f (e.symm q) = (φ q : X) :=
    congrArg (fun z => (φ z : X)) (e.apply_symm_apply q)
  rcases continuous_cylinder_frontier_sides hf hD ht hfFront hfi hfo with
    ⟨hlow, hlowD⟩ | ⟨hupp, huppD⟩
  · refine ⟨A₀, A₁, hA, ?_, ?_, hconn⟩
    · rintro x ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      rw [← hval q, hlow]
      change q.1.2 < t
      rw [hq]
      exact ht.1
    · apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨y, ⟨q, hq, rfl⟩, rfl⟩, hxD⟩
      rw [← hval q, hlowD] at hxD
      change q.1.2 ≤ t at hxD
      rw [hq] at hxD
      exact ht.2.not_ge hxD
  · refine ⟨A₁, A₀, hA.symm, ?_, ?_, hconn⟩
    · rintro x ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      rw [← hval q, hupp]
      change t < q.1.2
      rw [hq]
      exact ht.2
    · apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨y, ⟨q, hq, rfl⟩, rfl⟩, hxD⟩
      rw [← hval q, huppD] at hxD
      change t ≤ q.1.2 at hxD
      rw [hq] at hxD
      exact ht.1.not_ge hxD

theorem exists_isAnnulusOn_of_crossing_trace
    {X : Type*} [TopologicalSpace X] {C D F V : Set X} (hD : IsClosed D)
    (hC : C.Nonempty) (hCV : C ⊆ interior V) (hfront : F ∩ frontier D = C)
    (hin : C ⊆ closure (F ∩ interior D)) (hout : C ⊆ closure (F \ D))
    (φ : (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ ↥(V ∩ F))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hlevel : Subtype.val '' (φ '' {p | p.1.2 = t}) = C) :
    ∃ A₀ A₁ : Set X, IsAnnulusOn (V ∩ F) A₀ A₁ ∧
      C ⊆ (V ∩ F) \ (A₀ ∪ A₁) ∧ A₀ ⊆ interior D ∧ A₁ ∩ D = ∅ ∧
      IsConnected ((V ∩ F) ∩ D) ∧ IsConnected ((V ∩ F) \ D) := by
  obtain ⟨x, hx⟩ := hC
  have htrace : (V ∩ F) ∩ frontier D = Subtype.val '' (φ '' {p | p.1.2 = t}) := by
    rw [hlevel, inter_assoc, hfront]
    exact inter_eq_right.mpr (hCV.trans interior_subset)
  have hti : ((V ∩ F) ∩ interior D).Nonempty := by
    obtain ⟨y, hyV, hyF, hyD⟩ :=
      mem_closure_iff.mp (hin hx) (interior V) isOpen_interior (hCV hx)
    exact ⟨y, ⟨interior_subset hyV, hyF⟩, hyD⟩
  have hto : ((V ∩ F) \ D).Nonempty := by
    obtain ⟨y, hyV, hyF, hyD⟩ :=
      mem_closure_iff.mp (hout hx) (interior V) isOpen_interior (hCV hx)
    exact ⟨y, ⟨interior_subset hyV, hyF⟩, hyD⟩
  obtain ⟨A₀, A₁, hA, hA₀, hA₁, hconn⟩ :=
    exists_isAnnulusOn_with_frontier_sides hD φ ht htrace hti hto
  refine ⟨A₀, A₁, hA, ?_, hA₀, hA₁, hconn⟩
  intro y hy
  have hyF := hfront.symm.subset hy
  refine ⟨⟨interior_subset (hCV hy), hyF.1⟩, ?_⟩
  rintro (hy₀ | hy₁)
  · exact hyF.2.2 (hA₀ hy₀)
  · exact notMem_empty y (hA₁.subset ⟨hy₁, hD.frontier_subset hyF.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
