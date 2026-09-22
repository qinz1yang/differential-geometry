import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation

section

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

end

end

section

noncomputable section

open Module

namespace DifferentialGeometry.Topology.Manifold

private theorem orientation_map_units_smul
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E ≃ₗ[ℝ] F)
    (σ : ℝˣ) (o : Orientation ℝ E ι) :
    Orientation.map ι L (σ • o) = σ • Orientation.map ι L o := by
  rcases lt_or_gt_of_ne σ.ne_zero with hσ | hσ
  · rw [Module.Ray.units_smul_of_neg σ hσ, Orientation.map_neg,
      Module.Ray.units_smul_of_neg σ hσ]
  · rw [Module.Ray.units_smul_of_pos σ hσ, Module.Ray.units_smul_of_pos σ hσ]

theorem orientation_map_eq_of_matched_pullbacks
    {C E F ι : Type*} [AddCommGroup C] [Module ℝ C]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (R : C ≃ₗ[ℝ] E) (K : C ≃ₗ[ℝ] F)
    (oE : Orientation ℝ E ι) (oF : Orientation ℝ F ι)
    (hmatch : Orientation.map ι R.symm oE = Orientation.map ι K.symm oF) :
    Orientation.map ι (R.symm.trans K) oE = oF := by
  rw [DifferentialGeometry.orientation_map_trans, hmatch, ← Orientation.map_symm]
  exact (Orientation.map ι K).apply_symm_apply oF

theorem orientation_map_units_smul_of_matched_pullbacks
    {V C E F ι : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (A : V ≃ₗ[ℝ] E) (R : C ≃ₗ[ℝ] E) (K : C ≃ₗ[ℝ] F)
    (oV : Orientation ℝ V ι) (oE : Orientation ℝ E ι) (oF : Orientation ℝ F ι)
    (σ : ℝˣ)
    (hmatch : Orientation.map ι R.symm oE = Orientation.map ι K.symm oF)
    (hA : Orientation.map ι A oV = σ • oE) :
    Orientation.map ι (A.trans (R.symm.trans K)) oV = σ • oF := by
  rw [DifferentialGeometry.orientation_map_trans, hA, orientation_map_units_smul,
    orientation_map_eq_of_matched_pullbacks R K oE oF hmatch]

theorem basisDet_pos_iff_of_orientation_map_eq_units_smul
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (σ : ℝˣ) (hm : Orientation.map (Fin 3) L b.orientation = σ • o)
    (v : Fin 3 → V) :
    0 < (o.someBasis h).det (L ∘ v) ↔ 0 < (σ : ℝ) * b.det v := by
  rcases lt_or_gt_of_ne σ.ne_zero with hσ | hσ
  · rw [Module.Ray.units_smul_of_neg σ hσ] at hm
    rw [basisDet_pos_iff_of_orientation_map_eq_neg L b o h hm v]
    constructor
    · exact mul_pos_of_neg_of_neg hσ
    · intro hv
      exact ((mul_pos_iff.mp hv).resolve_left (fun hh => not_lt_of_gt hσ hh.1)).2
  · rw [Module.Ray.units_smul_of_pos σ hσ] at hm
    rw [basisDet_pos_iff_of_orientation_map_eq L b o h hm v]
    exact (mul_pos_iff_of_pos_left hσ).symm

theorem basisDet_boundary_pos_iff_signed
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (σ : ℝˣ) (hm : Orientation.map (Fin 3) L b.orientation = σ • o)
    (n v w : V) :
    0 < (o.someBasis h).det ![-L n, L v, L w] ↔
      (σ : ℝ) * b.det ![n, v, w] < 0 := by
  have hframe : L ∘ ![-n, v, w] = ![-L n, L v, L w] := by
    funext i
    fin_cases i <;> simp
  rw [← hframe, basisDet_pos_iff_of_orientation_map_eq_units_smul L b o h σ hm]
  have hneg : b.det ![-n, v, w] = -b.det ![n, v, w] := by
    simpa only [neg_one_smul, neg_one_mul] using
      b.det.map_vecCons_smul ![v, w] (-1 : ℝ) n
  rw [hneg, mul_neg, neg_pos]

theorem basisDet_boundary_pos_iff_signed_of_matched_pullbacks
    {V C E F : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (A : V ≃ₗ[ℝ] E) (R : C ≃ₗ[ℝ] E) (K : C ≃ₗ[ℝ] F)
    (b : Basis (Fin 3) ℝ V) (oE : Orientation ℝ E (Fin 3))
    (oF : Orientation ℝ F (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ F)
    (σ : ℝˣ)
    (hmatch : Orientation.map (Fin 3) R.symm oE = Orientation.map (Fin 3) K.symm oF)
    (hA : Orientation.map (Fin 3) A b.orientation = σ • oE) (n v w : V) :
    0 < (oF.someBasis h).det
      ![-K (R.symm (A n)), K (R.symm (A v)), K (R.symm (A w))] ↔
        (σ : ℝ) * b.det ![n, v, w] < 0 := by
  exact basisDet_boundary_pos_iff_signed (A.trans (R.symm.trans K)) b oF h σ
    (orientation_map_units_smul_of_matched_pullbacks A R K b.orientation oE oF σ hmatch hA)
    n v w

end DifferentialGeometry.Topology.Manifold

end

end

section

noncomputable section

open Module

namespace DifferentialGeometry.Topology.Manifold

theorem basisDet_smul_two_tangents
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis (Fin 3) ℝ V) (n v w : V) (r s : ℝ) :
    b.det ![n, r • v, s • w] = (r * s) * b.det ![n, v, w] := by
  have hframe : (fun i : Fin 3 => (![1, r, s] : Fin 3 → ℝ) i •
      (![n, v, w] : Fin 3 → V) i) = ![n, r • v, s • w] := by
    funext i
    fin_cases i <;> simp
  rw [← hframe, AlternatingMap.map_smul_univ]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, one_mul, smul_eq_mul]
  rfl

theorem basisDet_boundary_pos_iff_signed_smul_tangents
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (T : V ≃ₗ[ℝ] W) (b : Basis (Fin 3) ℝ V)
    (o : Orientation ℝ W (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ W)
    (σ : ℝˣ) (hT : Orientation.map (Fin 3) T b.orientation = σ • o)
    (n v w : V) {r s : ℝ} (hrs : 0 < r * s) :
    0 < (o.someBasis h).det ![-T n, T (r • v), T (s • w)] ↔
      (σ : ℝ) * b.det ![n, v, w] < 0 := by
  rw [basisDet_boundary_pos_iff_signed T b o h σ hT,
    basisDet_smul_two_tangents,
    show (σ : ℝ) * ((r * s) * b.det ![n, v, w]) =
      (r * s) * ((σ : ℝ) * b.det ![n, v, w]) by ring]
  constructor
  · intro hprod
    by_contra hnot
    exact not_lt_of_ge (mul_nonneg hrs.le (le_of_not_gt hnot)) hprod
  · exact mul_neg_of_pos_of_neg hrs

theorem basisDet_boundary_pos_iff_signed_of_radial_frame
    {V C E F : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (A : V ≃ₗ[ℝ] E) (R : C ≃ₗ[ℝ] E) (K : C ≃ₗ[ℝ] F)
    (b : Basis (Fin 3) ℝ V) (oE : Orientation ℝ E (Fin 3))
    (oF : Orientation ℝ F (Fin 3)) (h : Fintype.card (Fin 3) = Module.finrank ℝ F)
    (σ : ℝˣ) {L : ℝ} (hL : L ≠ 0)
    (hratio : Orientation.map (Fin 3) (R.symm.trans K) oE = oF)
    (hA : Orientation.map (Fin 3) A b.orientation = σ • oE)
    (n v w : V) (nC vC wC : C)
    (hn : R nC = A n) (hv : R vC = L • A v) (hw : R wC = L • A w) :
    0 < (oF.someBasis h).det ![-K nC, K vC, K wC] ↔
      (σ : ℝ) * b.det ![n, v, w] < 0 := by
  have hmatch : Orientation.map (Fin 3) R.symm oE =
      Orientation.map (Fin 3) K.symm oF := by
    apply (Orientation.map (Fin 3) K).injective
    rw [← DifferentialGeometry.orientation_map_trans, hratio, ← Orientation.map_symm]
    exact ((Orientation.map (Fin 3) K).apply_symm_apply oF).symm
  let T := A.trans (R.symm.trans K)
  have hT : Orientation.map (Fin 3) T b.orientation = σ • oF :=
    orientation_map_units_smul_of_matched_pullbacks A R K b.orientation oE oF σ hmatch hA
  have hn' : K nC = T n := by
    change K nC = K (R.symm (A n))
    rw [← hn, R.symm_apply_apply]
  have hv' : K vC = T (L • v) := by
    change K vC = K (R.symm (A (L • v)))
    rw [map_smul, ← hv, R.symm_apply_apply]
  have hw' : K wC = T (L • w) := by
    change K wC = K (R.symm (A (L • w)))
    rw [map_smul, ← hw, R.symm_apply_apply]
  rw [hn', hv', hw']
  exact basisDet_boundary_pos_iff_signed_smul_tangents T b oF h σ hT n v w
    (by simpa only [pow_two] using sq_pos_of_ne_zero hL)

end DifferentialGeometry.Topology.Manifold

end

end
