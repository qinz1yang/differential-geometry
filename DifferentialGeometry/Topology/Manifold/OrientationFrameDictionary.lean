import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open Function Module

namespace DifferentialGeometry.Topology.Manifold

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem basisDet_comp_orientation (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (v : Fin 3 → V) :
    (o.someBasis h).det (L ∘ v) = ((o.someBasis h).det (L ∘ b)) * b.det v := by
  have hφ : ((o.someBasis h).det.compLinearMap (L : V →ₗ[ℝ] W)) =
      (((o.someBasis h).det.compLinearMap (L : V →ₗ[ℝ] W)) ⇑b) • b.det :=
    AlternatingMap.eq_smul_basis_det b _
  have hv : ((o.someBasis h).det.compLinearMap (L : V →ₗ[ℝ] W)) v =
      (((o.someBasis h).det.compLinearMap (L : V →ₗ[ℝ] W)) ⇑b) * b.det v := by
    simpa only [AlternatingMap.smul_apply, smul_eq_mul] using congrArg (fun φ => φ v) hφ
  exact hv

theorem basisDet_pos_iff_orientation_map_eq (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W) :
    0 < (o.someBasis h).det (L ∘ b) ↔ Orientation.map (Fin 3) L b.orientation = o := by
  have hfun : ⇑(b.map L) = L ∘ b := funext fun i => Basis.map_apply b L i
  rw [← hfun, ← Basis.orientation_eq_iff_det_pos (o.someBasis h) (b.map L),
    Orientation.someBasis_orientation, Basis.orientation_map]
  exact ⟨Eq.symm, Eq.symm⟩

theorem basisDet_neg_iff_orientation_map_eq_neg (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W) :
    (o.someBasis h).det (L ∘ b) < 0 ↔ Orientation.map (Fin 3) L b.orientation = -o := by
  have hne : (o.someBasis h).det (L ∘ b) ≠ 0 := by
    have hfun : ⇑(b.map L) = L ∘ b := funext fun i => Basis.map_apply b L i
    rw [← hfun]
    exact ((o.someBasis h).isUnit_det (b.map L)).ne_zero
  have hlt : (o.someBasis h).det (L ∘ b) < 0 ↔ ¬ 0 < (o.someBasis h).det (L ∘ b) :=
    ⟨fun hc h0 => absurd (hc.trans h0) (lt_irrefl _),
      fun h0 => lt_of_le_of_ne (le_of_not_gt h0) hne⟩
  rw [hlt, basisDet_pos_iff_orientation_map_eq L b o h]
  exact Orientation.ne_iff_eq_neg _ _ h

theorem basisDet_pos_iff_of_orientation_map_eq (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (hm : Orientation.map (Fin 3) L b.orientation = o) (v : Fin 3 → V) :
    0 < (o.someBasis h).det (L ∘ v) ↔ 0 < b.det v := by
  rw [basisDet_comp_orientation L b o h v]
  exact mul_pos_iff_of_pos_left ((basisDet_pos_iff_orientation_map_eq L b o h).mpr hm)

theorem basisDet_pos_iff_of_orientation_map_eq_neg (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (hm : Orientation.map (Fin 3) L b.orientation = -o) (v : Fin 3 → V) :
    0 < (o.someBasis h).det (L ∘ v) ↔ b.det v < 0 := by
  rw [basisDet_comp_orientation L b o h v]
  have hc : (o.someBasis h).det (L ∘ b) < 0 :=
    (basisDet_neg_iff_orientation_map_eq_neg L b o h).mpr hm
  constructor
  · intro hv
    rcases lt_trichotomy (b.det v) 0 with hneg | hzero | hpos
    · exact hneg
    · rw [hzero, mul_zero] at hv
      exact absurd hv (lt_irrefl 0)
    · exact absurd (mul_neg_of_neg_of_pos hc hpos) (not_lt.mpr hv.le)
  · intro hv
    exact mul_pos_of_neg_of_neg hc hv

theorem exists_basisOrientationFrameSign_pos_and_neg :
    ∃ (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
      (L₀ L₁ : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
      (h : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
      0 < (b.orientation.someBasis h).det (L₀ ∘ b) ∧
        ¬ 0 < (b.orientation.someBasis h).det (L₁ ∘ b) ∧
        LinearMap.det (L₁ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) < 0 := by
  classical
  let b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let σ : Fin 3 → Units ℝ := Function.update (1 : Fin 3 → Units ℝ) 0 (-1)
  let L₁ : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    b.equiv (b.unitsSMul σ) (Equiv.refl (Fin 3))
  have hb : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  have hmapL₁ : b.map L₁ = b.unitsSMul σ := by
    ext1 i
    change b.equiv (b.unitsSMul σ) (Equiv.refl (Fin 3)) (b i) = (b.unitsSMul σ) i
    rw [Basis.equiv_apply, Equiv.refl_apply]
  have hm0 : Orientation.map (Fin 3) (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
      b.orientation = b.orientation := by
    rw [Orientation.map_refl]
    rfl
  have hm1 : Orientation.map (Fin 3) L₁ b.orientation = -b.orientation := by
    rw [← Basis.orientation_map b L₁, hmapL₁, Basis.orientation_neg_single]
  have hdet₁ : LinearMap.det (L₁ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
      < 0 :=
    (Orientation.map_eq_neg_iff_det_neg b.orientation L₁ hb).mp hm1
  refine ⟨b, LinearEquiv.refl ℝ _, L₁, hb, ?_, ?_, hdet₁⟩
  · exact (basisDet_pos_iff_of_orientation_map_eq _ b b.orientation hb hm0 b).mpr
      (by rw [Basis.det_self]; norm_num)
  · exact fun hpos => absurd
      ((basisDet_pos_iff_of_orientation_map_eq_neg _ b b.orientation hb hm1 b).mp hpos)
      (by rw [Basis.det_self]; norm_num)

end DifferentialGeometry.Topology.Manifold
