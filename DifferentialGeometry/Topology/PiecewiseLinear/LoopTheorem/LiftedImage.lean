/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoubleCoverProjection
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_isPLHomeomorphOn_image_of_complexity_eq
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (heq : T.complexity = S.complexity) :
    ∃ s : E → F, IsPLHomeomorphOn s S.imageComplex.space T.imageComplex.space ∧
      (∀ x ∈ S.imageComplex.space, R.projection (s x) = x) ∧
      EqOn (s ∘ S.singularMap) T.singularMap S.sourceComplex.space := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  let _ : Finite T.sourceComplex.faces := T.finite_source.to_subtype
  let _ : Finite S.imageComplex.faces :=
    (S.finite_ambient.subset S.image_faces_subset_ambient).to_subtype
  have hfactor : ∀ v ∈ S.sourceComplex.vertices,
      R.projection (T.vertexMap v) = S.vertexMap v := by
    intro v hv
    have hvT : v ∈ T.sourceComplex.vertices := R.sourceComplex_eq.symm ▸ hv
    have h := R.source_lift (S.sourceComplex.vertices_subset_space hv)
    change R.projection (simplicialMap T.sourceComplex T.vertexMap v) =
      simplicialMap S.sourceComplex S.vertexMap v at h
    rwa [simplicialMap_vertex T.sourceComplex T.vertexMap hvT,
      simplicialMap_vertex S.sourceComplex S.vertexMap hv] at h
  have hcomp : simplicialComplexity S.sourceComplex T.vertexMap =
      simplicialComplexity S.sourceComplex S.vertexMap := by
    change simplicialComplexity T.sourceComplex T.vertexMap =
      simplicialComplexity S.sourceComplex S.vertexMap at heq
    simpa only [R.sourceComplex_eq] using heq
  let fV : S.sourceComplex.vertices → E := fun v => S.vertexMap v
  let gV : S.sourceComplex.vertices → F := fun v => T.vertexMap v
  have hthrough : gV.FactorsThrough fV := fun {v w} hvw =>
    eq_vertexMap_of_eq_simplicialComplexity_of_factorization S.sourceComplex
      S.vertexMap T.vertexMap R.projection hfactor hcomp v.2 w.2 hvw
  let ψ : E → F := Function.extend fV gV (fun _ => 0)
  have hψ : ∀ v ∈ S.sourceComplex.vertices, ψ (S.vertexMap v) = T.vertexMap v :=
    fun v hv => hthrough.extend_apply (fun _ => 0) ⟨v, hv⟩
  let s := simplicialMap S.imageComplex ψ
  have hpl : IsPiecewiseAffineOn s S.imageComplex.space :=
    isPiecewiseAffineOn_simplicialMap S.imageComplex ψ
  have hlift : EqOn (s ∘ S.singularMap) T.singularMap S.sourceComplex.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := S.sourceComplex.mem_space_iff.mp hx
    have htimage := S.source_faces_map t ht
    obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap S.imageComplex ψ htimage
    have hsum : A (S.singularMap x) =
        ∑ v ∈ t, weights t x v • T.vertexMap v := by
      change A (simplicialMap S.sourceComplex S.vertexMap x) = _
      rw [simplicialMap_eq_of_mem S.sourceComplex S.vertexMap ht hxt,
        affineMap_apply_sum_smul_comp A S.vertexMap (sum_weights hxt)]
      apply Finset.sum_congr rfl
      intro v hv
      have hvS : v ∈ S.sourceComplex.vertices :=
        S.sourceComplex.down_closed ht (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)
      have hvimage : S.vertexMap v ∈ t.image S.vertexMap := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hvI : S.vertexMap v ∈ S.imageComplex.vertices :=
        S.imageComplex.down_closed htimage (Finset.singleton_subset_iff.mpr hvimage)
          (Finset.singleton_nonempty _)
      have hav : A (S.vertexMap v) = T.vertexMap v := by
        rw [← hA (subset_convexHull ℝ _ hvimage), simplicialMap_vertex _ _ hvI, hψ v hvS]
      rw [hav]
    calc
      s (S.singularMap x) = A (S.singularMap x) :=
        hA (simplicialMap_mem_convexHull_image S.sourceComplex S.vertexMap ht hxt)
      _ = ∑ v ∈ t, weights t x v • T.vertexMap v := hsum
      _ = T.singularMap x := by
        change _ = simplicialMap T.sourceComplex T.vertexMap x
        rw [R.sourceComplex_eq, simplicialMap_eq_of_mem S.sourceComplex T.vertexMap ht hxt]
  have hsmap : s '' S.imageComplex.space = T.imageComplex.space := by
    rw [S.image_space, image_image]
    change (s ∘ S.singularMap) '' S.sourceComplex.space = T.imageComplex.space
    rw [hlift.image_eq]
    calc
      T.singularMap '' S.sourceComplex.space = T.singularMap '' T.sourceComplex.space := by
        rw [R.sourceComplex_eq]
      _ = T.imageComplex.space := T.image_space.symm
  have hsection : ∀ x ∈ S.imageComplex.space, R.projection (s x) = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := S.image_space.subset hx
    change R.projection (s (S.singularMap y)) = S.singularMap y
    rw [show s (S.singularMap y) = T.singularMap y from hlift hy]
    exact R.source_lift hy
  have hinj : InjOn s S.imageComplex.space := by
    intro x hx y hy hxy
    exact (hsection x hx).symm.trans ((congrArg R.projection hxy).trans (hsection y hy))
  exact ⟨s, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_space S.imageComplex)
    hpl ⟨fun x hx => hsmap.subset ⟨x, hx, rfl⟩, hinj,
      fun x hx => hsmap.symm.subset hx⟩, hsection, hlift⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
