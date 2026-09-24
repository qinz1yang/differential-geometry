/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
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

theorem contMDiff (h : SmoothTwoSidedCollar I J e) : ContMDiff I J ∞ e := by
  have he : e = fun s => h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) :=
    funext fun s => (h.toFun_zero s).symm
  rw [he]
  exact (contMDiff_subtype_val.comp h.toDiffeomorph.contMDiff).comp
    (contMDiff_id.prodMk contMDiff_const)

theorem isEmbedding (h : SmoothTwoSidedCollar I J e) : IsEmbedding e := by
  have he : e = fun s => h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) :=
    funext fun s => (h.toFun_zero s).symm
  rw [he]
  exact h.isOpenEmbedding_toFun.isEmbedding.comp (isEmbedding_prodMkLeft _)

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

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {S' : Type*} [TopologicalSpace S'] [ChartedSpace H' S']

def reparametrize (d : Diffeomorph I' I S' S ∞) :
    SmoothTwoSidedCollar I' J (e ∘ d) where
  radius := h.radius
  radius_pos := h.radius_pos
  neighborhood := h.neighborhood
  toDiffeomorph :=
    (d.prodCongr (Diffeomorph.refl 𝓘(ℝ) (symmetricOpenInterval h.radius) ∞)).trans
      h.toDiffeomorph
  zero_eq := fun s ↦ h.zero_eq (d s)

@[simp] theorem reparametrize_radius (d : Diffeomorph I' I S' S ∞) :
    (h.reparametrize d).radius = h.radius := rfl

@[simp] theorem reparametrize_neighborhood (d : Diffeomorph I' I S' S ∞) :
    (h.reparametrize d).neighborhood = h.neighborhood := rfl

@[simp] theorem reparametrize_toFun (d : Diffeomorph I' I S' S ∞)
    (p : S' × symmetricOpenInterval h.radius) :
    (h.reparametrize d).toFun p = h.toFun (d p.1, p.2) := rfl

end SmoothTwoSidedCollar

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable
    {E H F G S M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace S] [ChartedSpace H S] [Nonempty S]
    [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (d : SmoothTwoSidedCollar I J e)

private def intervalInclusion :
    _root_.PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (S × symmetricOpenInterval d.radius) (S × ℝ) ∞ :=
  PartialDiffeomorph.prod (Diffeomorph.refl I S ∞).toPartialDiffeomorph
    (PartialDiffeomorph.subtypeVal (symmetricOpenInterval d.radius)
      ⟨⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩⟩)

def toPartialDiffeomorph :
    _root_.PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) M ∞ :=
  ((d.intervalInclusion.symm.trans d.toDiffeomorph.toPartialDiffeomorph).trans
    (PartialDiffeomorph.subtypeVal d.neighborhood
      ⟨d.toDiffeomorph (Classical.choice inferInstance,
        ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)⟩))

@[simp] theorem toPartialDiffeomorph_apply (p : S × symmetricOpenInterval d.radius) :
    d.toPartialDiffeomorph (p.1, p.2.val) = d.toFun p := by
  change ((d.toDiffeomorph (d.intervalInclusion.symm (d.intervalInclusion p))) : M) = _
  exact congrArg (fun q : S × symmetricOpenInterval d.radius => (d.toDiffeomorph q : M))
    (d.intervalInclusion.toPartialEquiv.left_inv (show p ∈ d.intervalInclusion.source from ⟨trivial, trivial⟩))

theorem toPartialDiffeomorph_symm_apply (p : d.neighborhood) :
    d.toPartialDiffeomorph.symm p.val =
      ((d.toDiffeomorph.symm p).1, (d.toDiffeomorph.symm p).2.val) := by
  let hN : Nonempty d.neighborhood := ⟨d.toDiffeomorph (Classical.choice inferInstance,
    ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)⟩
  let j := PartialDiffeomorph.subtypeVal (I := J) d.neighborhood hN
  change d.intervalInclusion (d.toDiffeomorph.symm (j.symm (j p))) = _
  exact congrArg (fun q : d.neighborhood => d.intervalInclusion (d.toDiffeomorph.symm q))
    (j.toPartialEquiv.left_inv (show p ∈ j.source from trivial))

@[simp] theorem toPartialDiffeomorph_source :
    d.toPartialDiffeomorph.source = univ ×ˢ Ioo (-d.radius) d.radius := by
  ext q
  change q ∈ (((d.intervalInclusion.symm.toOpenPartialHomeomorph.trans
    d.toDiffeomorph.toPartialDiffeomorph.toOpenPartialHomeomorph).trans
    (PartialDiffeomorph.subtypeVal (I := J) d.neighborhood _).toOpenPartialHomeomorph).source) ↔ _
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
  change ((q ∈ d.intervalInclusion.target ∧ True) ∧ True) ↔ _
  simp only [intervalInclusion, PartialDiffeomorph.prod, PartialDiffeomorph.subtypeVal,
    Diffeomorph.toPartialDiffeomorph, symmetricOpenInterval, and_true, mem_prod, mem_univ, mem_Ioo, true_and]
  erw [OpenPartialHomeomorph.prod_target]
  simp only [mem_prod]
  erw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  change (True ∧ (-d.radius < q.2 ∧ q.2 < d.radius)) ↔ _
  exact ⟨And.right, fun h => ⟨trivial, h⟩⟩

@[simp] theorem toPartialDiffeomorph_target : d.toPartialDiffeomorph.target = d.neighborhood := by
  ext x
  simp [toPartialDiffeomorph, intervalInclusion, PartialDiffeomorph.prod,
    PartialDiffeomorph.subtypeVal, Diffeomorph.toPartialDiffeomorph,
    _root_.PartialDiffeomorph.trans]

omit [Nonempty S]

private def reverseInterval :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (symmetricOpenInterval d.radius) (symmetricOpenInterval d.radius) ∞ where
  toFun t := ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := Subtype.ext (neg_neg t.val)
  right_inv t := Subtype.ext (neg_neg t.val)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval d.radius) _).mp
    contMDiff_subtype_val.neg
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval d.radius) _).mp
    contMDiff_subtype_val.neg

def reverse : SmoothTwoSidedCollar I J e where
  radius := d.radius
  radius_pos := d.radius_pos
  neighborhood := d.neighborhood
  toDiffeomorph := ((Diffeomorph.refl I S ∞).prodCongr d.reverseInterval).trans d.toDiffeomorph
  zero_eq s := by
    change d.toFun (s, ⟨-(0 : ℝ), _⟩) = e s
    exact (congrArg (fun t : symmetricOpenInterval d.radius => d.toFun (s, t))
      (Subtype.ext (neg_zero : -(0 : ℝ) = 0))).trans (d.toFun_zero s)

@[simp] theorem reverse_radius : d.reverse.radius = d.radius := rfl

@[simp] theorem reverse_neighborhood : d.reverse.neighborhood = d.neighborhood := rfl

@[simp] theorem reverse_toFun (p : S × symmetricOpenInterval d.radius) :
    d.reverse.toFun p = d.toFun (p.1, ⟨-p.2.val, by
      constructor <;> linarith [p.2.property.1, p.2.property.2]⟩) := rfl

theorem reverse_symm_toDiffeomorph (p : d.neighborhood) :
    d.reverse.toDiffeomorph.symm p =
      ((d.toDiffeomorph.symm p).1, ⟨-(d.toDiffeomorph.symm p).2.val, by
        change -(d.radius) < -(d.toDiffeomorph.symm p).2.val ∧ -(d.toDiffeomorph.symm p).2.val < d.radius
        constructor <;> linarith [(d.toDiffeomorph.symm p).2.property.1,
          (d.toDiffeomorph.symm p).2.property.2]⟩) := rfl

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
