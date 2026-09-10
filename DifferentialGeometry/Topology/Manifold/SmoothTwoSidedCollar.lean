/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology

def symmetricOpenInterval (a : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (-a) a, isOpen_Ioo⟩

structure SmoothTwoSidedCollar
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    (e : S → M) where
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : TopologicalSpace.Opens M
  toDiffeomorph :
    Diffeomorph (I.prod (modelWithCornersSelf ℝ ℝ)) J
      (S × symmetricOpenInterval radius) neighborhood ∞
  zero_eq : ∀ s,
    (toDiffeomorph (s, ⟨0, neg_lt_zero.mpr radius_pos, radius_pos⟩) : M) = e s

namespace SmoothTwoSidedCollar

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)

instance transContinuousLinearEquiv_boundaryless
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [J.Boundaryless] (L : F ≃L[ℝ] F') :
    (J.transContinuousLinearEquiv L).Boundaryless where
  range_eq_univ := by
    rw [J.transContinuousLinearEquiv_range, J.range_eq_univ]
    exact Set.image_univ_of_surjective L.surjective

def toFun : S × symmetricOpenInterval h.radius → M :=
  fun p => h.toDiffeomorph p

theorem isOpenEmbedding_toFun : IsOpenEmbedding h.toFun :=
  h.neighborhood.2.isOpenEmbedding_subtypeVal.comp
    h.toDiffeomorph.toHomeomorph.isOpenEmbedding

@[simp]
theorem toFun_zero (s : S) :
    h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) = e s :=
  h.zero_eq s

noncomputable def transAmbientModel {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') : SmoothTwoSidedCollar I (J.transContinuousLinearEquiv L) e where
  radius := h.radius
  radius_pos := h.radius_pos
  neighborhood := h.neighborhood
  toDiffeomorph := h.toDiffeomorph.trans
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv J h.neighborhood L)
  zero_eq := h.zero_eq

@[simp]
theorem transAmbientModel_radius {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') :
    (h.transAmbientModel L).radius = h.radius :=
  rfl

@[simp]
theorem transAmbientModel_toFun {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') (p : S × symmetricOpenInterval h.radius) :
    (h.transAmbientModel L).toFun p = h.toFun p :=
  by
    simp only [toFun, transAmbientModel]
    apply congrArg Subtype.val
    change (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞)
      J h.neighborhood L)
      (h.toDiffeomorph p) = h.toDiffeomorph p
    rfl

end SmoothTwoSidedCollar

end DifferentialGeometry.Topology
