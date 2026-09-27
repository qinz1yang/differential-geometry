/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskFamilyMove
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarHoledCollars

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem isPLCirclePositive_of_eqOn {S : Set Plane} {u v : Plane → Plane}
    (hu : IsPLCirclePositive S u) (hvu : EqOn v u S) : IsPLCirclePositive S v := by
  obtain ⟨c, hc, hcb, hcu⟩ := hu
  refine ⟨c, hc, hcb, hcu.congr fun t => ?_⟩
  change Function.invFunOn c univ (v (c t)) = Function.invFunOn c univ (u (c t))
  rw [hvu (hcb.mapsTo (mem_univ t))]

private theorem invFunOn_eqOn_image_of_subset {D A : Set Plane} {f : Plane → Plane}
    (hf : InjOn f D) (hAD : A ⊆ D) :
    EqOn (Function.invFunOn f D) (Function.invFunOn f A) (f '' A) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hf.leftInvOn_invFunOn (hAD hx), (hf.mono hAD).leftInvOn_invFunOn hx]

theorem IsPLHomeomorphOn.exists_holed_disk_extension_of_positive_boundary_corrections
    {ι : Type*} [Finite ι] {D D' : Set Plane} {A B : ι → Set Plane}
    {f : Plane → Plane} {ψ : ι → Plane → Plane}
    (hf : IsPLHomeomorphOn f D D') (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hAD : ∀ i, A i ⊆ D) (hBD : ∀ i, B i ⊆ interior D')
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hmatch : ∀ i, f '' A i = B i)
    (hψ : ∀ i, IsPLHomeomorphOn (ψ i) (frontier (A i)) (frontier (B i)))
    (hpos : ∀ i, IsPLCirclePositive (frontier (B i)) (ψ i ∘ Function.invFunOn f D)) :
    ∃ g : Plane → Plane,
      IsPLHomeomorphOn g (D \ ⋃ i, interior (A i)) (D' \ ⋃ i, interior (B i)) ∧
      EqOn g f (frontier D) ∧ ∀ i, EqOn g (ψ i) (frontier (A i)) := by
  have hfi (i : ι) : IsPLHomeomorphOn f (A i) (B i) := by
    rw [← hmatch i]
    exact hf.restrict (hA i).isPolyhedron (hAD i)
  have hfront (i : ι) : f '' frontier (A i) = frontier (B i) :=
    (hfi i).image_frontier rfl (hA i).isPolyhedron.isClosed (hB i).isPolyhedron.isClosed
  have hfinv (i : ι) :
      IsPLHomeomorphOn (Function.invFunOn f D) (frontier (B i)) (frontier (A i)) := by
    have himage : Function.invFunOn f D '' frontier (B i) = frontier (A i) := by
      rw [← hfront i]
      exact hf.bijOn.injOn.invFunOn_image ((hA i).isPolyhedron.isClosed.frontier_subset.trans
        (hAD i))
    have h := hf.symm.restrict (hB i).isPLSphere_frontier.isPolyhedron
      ((hB i).isPolyhedron.isClosed.frontier_subset.trans ((hBD i).trans interior_subset))
    rwa [himage] at h
  let u : Option ι → Plane → Plane :=
    fun i => Option.elim i id (fun j => ψ j ∘ Function.invFunOn f D)
  have hu : ∀ i, IsPLHomeomorphOn (u i)
      (Option.elim i (frontier D') (fun j => frontier (B j)))
      (Option.elim i (frontier D') (fun j => frontier (B j))) := by
    rintro (_ | i)
    · exact hD'.isPLSphere_frontier.isPolyhedron.isPLHomeomorphOn_id
    · exact (hfinv i).trans (hψ i)
  have hupos : ∀ i, IsPLCirclePositive
      (Option.elim i (frontier D') (fun j => frontier (B j))) (u i) := by
    rintro (_ | i)
    · exact isPLCirclePositive_id hD'.isPLSphere_frontier
    · exact hpos i
  obtain ⟨q, hq, hqbd⟩ :=
    exists_isPLHomeomorphOn_holed_disk_of_positive_boundary_maps hD' hB hBD hBdis hu hupos
  have hinner : f '' (⋃ i, interior (A i)) = ⋃ i, interior (B i) := by
    rw [image_iUnion]
    congr 1
    funext i
    exact (hfi i).image_interior rfl
  have himage : f '' (D \ ⋃ i, interior (A i)) = D' \ ⋃ i, interior (B i) := by
    rw [hf.bijOn.injOn.image_sdiff_subset
      (iUnion_subset fun i => interior_subset.trans (hAD i)), hf.image_eq, hinner]
  have hholes := hf.restrict
    (hD.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hA) sdiff_subset
  rw [himage] at hholes
  refine ⟨q ∘ f, hholes.trans hq, ?_, ?_⟩
  · intro x hx
    have hfx : f x ∈ frontier D' :=
      (hf.image_frontier rfl hD.isPolyhedron.isClosed hD'.isPolyhedron.isClosed).subset
        ⟨x, hx, rfl⟩
    exact hqbd none hfx
  · intro i x hx
    change q (f x) = ψ i x
    rw [hqbd (some i) ((hfront i).subset ⟨x, hx, rfl⟩)]
    change ψ i (Function.invFunOn f D (f x)) = ψ i x
    rw [hf.bijOn.invOn_invFunOn.1 (hAD i ((hA i).isPolyhedron.isClosed.frontier_subset hx))]

theorem exists_isPLHomeomorphOn_holed_disk_with_boundary_extension
    {ι : Type*} [Finite ι] {D D' : Set Plane} {A B : ι → Set Plane} {φ : Plane → Plane}
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hAD : ∀ i, A i ⊆ interior D) (hBD : ∀ i, B i ⊆ interior D')
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hφ : IsPLHomeomorphOn φ (frontier D) (frontier D')) :
    ∃ f : Plane → Plane, IsPLHomeomorphOn f D D' ∧ EqOn f φ (frontier D) ∧
      (∀ i, f '' A i = B i) ∧
      ∀ ψ : ι → Plane → Plane,
        (∀ i, IsPLHomeomorphOn (ψ i) (frontier (A i)) (frontier (B i))) →
        (∀ i, IsPLCirclePositive (frontier (B i))
          (ψ i ∘ Function.invFunOn f (frontier (A i)))) →
        ∃ g : Plane → Plane,
          IsPLHomeomorphOn g (D \ ⋃ i, interior (A i)) (D' \ ⋃ i, interior (B i)) ∧
          EqOn g φ (frontier D) ∧ ∀ i, EqOn g (ψ i) (frontier (A i)) := by
  obtain ⟨f, hf, -, hfφ, hmatch⟩ :=
    exists_isPLHomeomorphOn_holed_disk_eqOn_outer_boundary
      hD hD' hA hB hAD hBD hAdis hBdis hφ
  refine ⟨f, hf, hfφ, fun i => (hmatch i).1, ?_⟩
  intro ψ hψ hpos
  have hcorrection (i : ι) :
      IsPLCirclePositive (frontier (B i)) (ψ i ∘ Function.invFunOn f D) := by
    apply isPLCirclePositive_of_eqOn (hpos i)
    intro y hy
    have hsub : frontier (A i) ⊆ D :=
      (hA i).isPolyhedron.isClosed.frontier_subset.trans ((hAD i).trans interior_subset)
    have hinv := invFunOn_eqOn_image_of_subset hf.bijOn.injOn hsub
    change ψ i (Function.invFunOn f D y) = ψ i (Function.invFunOn f (frontier (A i)) y)
    rw [hinv ((hmatch i).2.symm ▸ hy)]
  obtain ⟨g, hg, hgf, hgψ⟩ := hf.exists_holed_disk_extension_of_positive_boundary_corrections
    hD hD' hA hB (fun i => (hAD i).trans interior_subset) hBD hBdis
    (fun i => (hmatch i).1) hψ hcorrection
  exact ⟨g, hg, hgf.trans hfφ, hgψ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
