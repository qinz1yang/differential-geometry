import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Torsor
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section

open Topology (IsEmbedding)

namespace LinearIsometryEquiv

section Topology

variable {k E F : Type*} [NontriviallyNormedField k]
  [SeminormedAddCommGroup E] [NormedSpace k E] [NormedAddCommGroup F] [NormedSpace k F]

instance instMetricSpace : MetricSpace (E ≃ₗᵢ[k] F) where
  __ := PseudoMetricSpace.induced (fun e : E ≃ₗᵢ[k] F => (e : E →L[k] F)) inferInstance
  eq_of_dist_eq_zero := by
    intro e f h
    change dist (e : E →L[k] F) (f : E →L[k] F) = 0 at h
    rw [dist_eq_norm] at h
    ext v
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hv := ((e : E →L[k] F) - (f : E →L[k] F)).le_opNorm v
    rw [h, zero_mul] at hv
    exact le_antisymm hv (norm_nonneg _)

theorem isometry_toContinuousLinearMap :
    Isometry (fun e : E ≃ₗᵢ[k] F => (e : E →L[k] F)) := fun _ _ => rfl

theorem isEmbedding_toContinuousLinearMap :
    IsEmbedding (fun e : E ≃ₗᵢ[k] F => (e : E →L[k] F)) :=
  isometry_toContinuousLinearMap.isEmbedding

theorem continuous_toContinuousLinearMap :
    Continuous (fun e : E ≃ₗᵢ[k] F => (e : E →L[k] F)) :=
  isometry_toContinuousLinearMap.continuous

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → E ≃ₗᵢ[k] F} :
    Continuous f ↔ Continuous (fun x => (f x : E →L[k] F)) :=
  isEmbedding_toContinuousLinearMap.isInducing.continuous_iff

theorem continuous_apply : Continuous (fun z : (E ≃ₗᵢ[k] F) × E => z.1 z.2) :=
  (continuous_toContinuousLinearMap.comp continuous_fst).clm_apply continuous_snd

variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace k E']

def precompHomeomorph (e : E ≃ₗᵢ[k] E') : (E' ≃ₗᵢ[k] F) ≃ₜ (E ≃ₗᵢ[k] F) where
  toFun p := e.trans p
  invFun p := e.symm.trans p
  left_inv p := by ext v; exact congrArg p (e.apply_symm_apply v)
  right_inv p := by ext v; exact congrArg p (e.symm_apply_apply v)
  continuous_toFun := continuous_iff.mpr
    (continuous_toContinuousLinearMap.clm_comp (continuous_const (y := (e : E →L[k] E'))))
  continuous_invFun := continuous_iff.mpr
    (continuous_toContinuousLinearMap.clm_comp (continuous_const (y := (e.symm : E' →L[k] E))))

@[simp]
theorem precompHomeomorph_apply (e : E ≃ₗᵢ[k] E') (p : E' ≃ₗᵢ[k] F) :
    e.precompHomeomorph p = e.trans p := rfl

@[simp]
theorem precompHomeomorph_symm_apply (e : E ≃ₗᵢ[k] E') (p : E ≃ₗᵢ[k] F) :
    e.precompHomeomorph.symm p = e.symm.trans p := rfl

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace k G]

theorem continuous_trans :
    Continuous (fun z : (E ≃ₗᵢ[k] F) × (F ≃ₗᵢ[k] G) => z.1.trans z.2) :=
  continuous_iff.mpr
    ((continuous_toContinuousLinearMap.comp continuous_snd).clm_comp
      (continuous_toContinuousLinearMap.comp continuous_fst))

instance instContinuousIsometrySMul : ContinuousSMul (F ≃ₗᵢ[k] F) (E ≃ₗᵢ[k] F) where
  continuous_smul := (continuous_trans.comp continuous_swap).congr (fun _ => rfl)

end Topology

section Inverse

variable {k E F : Type*} [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E] [NormedAddCommGroup F] [NormedSpace k F]

theorem dist_symm (e f : E ≃ₗᵢ[k] F) : dist e.symm f.symm = dist e f := by
  rw [← isometry_toContinuousLinearMap.dist_eq e.symm f.symm,
    ← isometry_toContinuousLinearMap.dist_eq e f, dist_eq_norm, dist_eq_norm]
  have h : (e.symm : F →L[k] E) - (f.symm : F →L[k] E) =
      (e.symm : F →L[k] E).comp
        (((f : E →L[k] F) - (e : E →L[k] F)).comp (f.symm : F →L[k] E)) := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, coe_toContinuousLinearEquiv,
      map_sub, apply_symm_apply, symm_apply_apply]
  rw [h, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_sub_rev]

theorem isometry_symm : Isometry (fun e : E ≃ₗᵢ[k] F => e.symm) :=
  Isometry.of_dist_eq dist_symm

theorem continuous_symm : Continuous (fun e : E ≃ₗᵢ[k] F => e.symm) :=
  isometry_symm.continuous

instance instIsTopologicalGroup : IsTopologicalGroup (E ≃ₗᵢ[k] E) where
  continuous_mul := (continuous_trans.comp continuous_swap).congr (fun _ => rfl)
  continuous_inv := continuous_symm

end Inverse

end LinearIsometryEquiv
