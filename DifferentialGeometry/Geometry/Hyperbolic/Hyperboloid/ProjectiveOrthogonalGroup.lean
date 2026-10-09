import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.UpperSheet
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryTopology
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.ContinuousAction
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.MobiusTransformations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.ContinuousMonoidHom

noncomputable section

open scoped Matrix

namespace DifferentialGeometry.Hyperboloid

open DifferentialGeometry.ProjectiveOrthogonalGroup
open DifferentialGeometry.Hyperbolic (LorVec HUpper lorB tc)
open DifferentialGeometry.HyperbolicAction (LorGrp matOf poPermHom poMulAction)

private def lorentzCoordinates (n : ℕ) :
    LorVec n ≃ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin n) where
  toFun z := (tc z, WithLp.toLp 2 (fun i => z (Sum.inl i)))
  invFun z := Sum.elim (fun i => z.2 i) (fun _ : Fin 1 => z.1)
  left_inv z := by
    funext i
    rcases i with i | i
    · rfl
    · have hi : i = 0 := Subsingleton.elim i 0
      subst i
      rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro i
      rfl
  map_add' z w := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro i
      rfl
  map_smul' a z := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro i
      rfl

private theorem lorentzCoordinates_form (n : ℕ) (z w : LorVec n) :
    lorentzForm (EuclideanSpace ℝ (Fin n)) (lorentzCoordinates n z) (lorentzCoordinates n w) =
      lorB z w := by
  change inner ℝ (WithLp.toLp 2 (fun i : Fin n => z (Sum.inl i)))
      (WithLp.toLp 2 (fun i : Fin n => w (Sum.inl i))) - tc z * tc w = lorB z w
  simp [PiLp.inner_apply, DifferentialGeometry.Hyperbolic.lorB,
    DifferentialGeometry.Hyperbolic.sdot, mul_comm]

private theorem lorentzCoordinates_upper (n : ℕ) (x : HUpper n) :
    lorentzCoordinates n x.val = ((hUpperIsometryEquiv n x).time, (hUpperIsometryEquiv n x).space) := by
  apply Prod.ext
  · exact (hUpperIsometryEquiv_time n x).symm
  · apply PiLp.ext
    intro i
    exact (hUpperIsometryEquiv_space_apply n x i).symm

private def projectiveUpperIsometry (n : ℕ) (q : PO (n + 1) 1) :
    HUpper (n + 1) ≃ᵢ HUpper (n + 1) where
  toEquiv := poPermHom (by omega : 1 ≤ n + 1) q
  isometry_toFun := Isometry.of_dist_eq
    (DifferentialGeometry.HyperbolicAction.po_dist_smul (by omega : 1 ≤ n + 1) q)

private def projectiveIsometryHom (n : ℕ) : PO (n + 1) 1 →*
    (Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) where
  toFun q := ((hUpperIsometryEquiv (n + 1)).symm.trans
    (projectiveUpperIsometry n q)).trans (hUpperIsometryEquiv (n + 1))
  map_one' := by
    apply IsometryEquiv.ext
    intro x
    change hUpperIsometryEquiv (n + 1)
      (poPermHom (by omega : 1 ≤ n + 1) 1 ((hUpperIsometryEquiv (n + 1)).symm x)) = x
    rw [map_one]
    exact (hUpperIsometryEquiv (n + 1)).apply_symm_apply x
  map_mul' q r := by
    apply IsometryEquiv.ext
    intro x
    change hUpperIsometryEquiv (n + 1)
      (poPermHom (by omega : 1 ≤ n + 1) (q * r) ((hUpperIsometryEquiv (n + 1)).symm x)) =
      hUpperIsometryEquiv (n + 1) (poPermHom (by omega : 1 ≤ n + 1) q
        ((hUpperIsometryEquiv (n + 1)).symm (hUpperIsometryEquiv (n + 1)
          (poPermHom (by omega : 1 ≤ n + 1) r ((hUpperIsometryEquiv (n + 1)).symm x)))))
    rw [map_mul, (hUpperIsometryEquiv (n + 1)).symm_apply_apply]
    rfl

private theorem projectiveIsometryHom_apply (n : ℕ) (q : PO (n + 1) 1) (x : HUpper (n + 1)) :
    projectiveIsometryHom n q (hUpperIsometryEquiv (n + 1) x) =
      hUpperIsometryEquiv (n + 1) ((poMulAction (by omega : 1 ≤ n + 1)).smul q x) := by
  change hUpperIsometryEquiv (n + 1) (poPermHom (by omega : 1 ≤ n + 1) q
    ((hUpperIsometryEquiv (n + 1)).symm (hUpperIsometryEquiv (n + 1) x))) = _
  rw [(hUpperIsometryEquiv (n + 1)).symm_apply_apply]
  rfl

private theorem projectiveIsometryHom_injective (n : ℕ) :
    Function.Injective (projectiveIsometryHom n) := by
  apply (injective_iff_map_eq_one (projectiveIsometryHom n)).mpr
  intro q hq
  apply DifferentialGeometry.HyperbolicFaithful.po_smul_eq_one (by omega : 1 ≤ n + 1)
  intro x
  apply (hUpperIsometryEquiv (n + 1)).injective
  have h := congrArg (fun F => F (hUpperIsometryEquiv (n + 1) x)) hq
  rw [projectiveIsometryHom_apply] at h
  exact h

private theorem continuous_projectiveIsometryHom (n : ℕ) : Continuous (projectiveIsometryHom n) := by
  apply IsometryEquiv.continuous_iff.mpr
  intro x
  have hpair : Continuous (fun q : PO (n + 1) 1 =>
      (q, (hUpperIsometryEquiv (n + 1)).symm x)) := continuous_id.prodMk continuous_const
  have h := (DifferentialGeometry.ContinuousAction.continuous_po_smul (by omega : 1 ≤ n + 1)).comp hpair
  exact (hUpperIsometryEquiv (n + 1)).continuous.comp h

private def projectiveLorentzLinear (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) :
    LorVec (n + 1) →ₗ[ℝ] LorVec (n + 1) :=
  (((lorentzCoordinates (n + 1)).trans (lorentzExtension F).toLinearEquiv).trans
    (lorentzCoordinates (n + 1)).symm).toLinearMap

private def projectiveLorentzMatrix (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) :
    Matrix (Fin (n + 1) ⊕ Fin 1) (Fin (n + 1) ⊕ Fin 1) ℝ :=
  LinearMap.toMatrix' (projectiveLorentzLinear n F)

private theorem projectiveLorentzMatrix_apply (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) (z : LorVec (n + 1)) :
    lorentzCoordinates (n + 1) (projectiveLorentzMatrix n F *ᵥ z) =
      lorentzExtension F (lorentzCoordinates (n + 1) z) := by
  rw [projectiveLorentzMatrix, LinearMap.toMatrix'_mulVec]
  exact (lorentzCoordinates (n + 1)).apply_symm_apply _

private theorem projectiveLorentzMatrix_preserves (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) (z w : LorVec (n + 1)) :
    lorB (projectiveLorentzMatrix n F *ᵥ z) (projectiveLorentzMatrix n F *ᵥ w) = lorB z w := by
  rw [← lorentzCoordinates_form, projectiveLorentzMatrix_apply, projectiveLorentzMatrix_apply,
    (lorentzExtension F).map_app, lorentzCoordinates_form]

private theorem projectiveLorentzMatrix_mem (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) :
    MatrixSum.ofMatrix (projectiveLorentzMatrix n F) ∈
      unitary (MatrixSum (Fin (n + 1)) (Fin 1) ℝ) := by
  obtain ⟨g, hg⟩ := DifferentialGeometry.MobiusBoundary.exists_lorGrp_of_lorB_preserving
    (projectiveLorentzMatrix n F) (projectiveLorentzMatrix_preserves n F)
  rw [← hg]
  exact g.property

private def projectiveLorentzLift (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) : LorGrp (n + 1) :=
  ⟨MatrixSum.ofMatrix (projectiveLorentzMatrix n F), projectiveLorentzMatrix_mem n F⟩

private def projectiveRepresentative (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) : PO (n + 1) 1 :=
  QuotientGroup.mk' (Subgroup.center (LorGrp (n + 1))) (projectiveLorentzLift n F)

private theorem projectiveLorentzMatrix_upper (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) (x : HUpper (n + 1)) :
    projectiveLorentzMatrix n F *ᵥ x.val =
      ((hUpperIsometryEquiv (n + 1)).symm (F (hUpperIsometryEquiv (n + 1) x))).val := by
  apply (lorentzCoordinates (n + 1)).injective
  rw [projectiveLorentzMatrix_apply, lorentzCoordinates_upper, lorentzExtension_apply,
    lorentzCoordinates_upper, (hUpperIsometryEquiv (n + 1)).apply_symm_apply]

private theorem projectiveRepresentative_action (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) (x : HUpper (n + 1)) :
    (poMulAction (by omega : 1 ≤ n + 1)).smul (projectiveRepresentative n F) x =
      (hUpperIsometryEquiv (n + 1)).symm (F (hUpperIsometryEquiv (n + 1) x)) := by
  have h := DifferentialGeometry.HyperbolicAction.po_smul_mk
    (by omega : 1 ≤ n + 1) (projectiveLorentzLift n F) x
  change (poMulAction (by omega : 1 ≤ n + 1)).smul (projectiveRepresentative n F) x = _ at h
  rw [h]
  apply DifferentialGeometry.Hyperbolic.HUpper.ext
  rw [DifferentialGeometry.HyperbolicAction.smul_val]
  change DifferentialGeometry.HyperbolicAction.upperize (projectiveLorentzMatrix n F *ᵥ x.val) = _
  rw [projectiveLorentzMatrix_upper, DifferentialGeometry.HyperbolicAction.upperize,
    ite_eq_left ((hUpperIsometryEquiv (n + 1)).symm (F (hUpperIsometryEquiv (n + 1) x))).future]

private theorem projectiveIsometryHom_representative (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) :
    projectiveIsometryHom n (projectiveRepresentative n F) = F := by
  apply IsometryEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (hUpperIsometryEquiv (n + 1)).surjective y
  rw [projectiveIsometryHom_apply, projectiveRepresentative_action,
    (hUpperIsometryEquiv (n + 1)).apply_symm_apply]

private theorem projectiveRepresentative_isometryHom (n : ℕ) (q : PO (n + 1) 1) :
    projectiveRepresentative n (projectiveIsometryHom n q) = q :=
  projectiveIsometryHom_injective n (projectiveIsometryHom_representative n _)

private theorem continuous_projectiveLorentzMatrix (n : ℕ) :
    Continuous (projectiveLorentzMatrix n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hpair : Continuous (fun F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) =>
      (F, lorentzCoordinates (n + 1) (Pi.single j (1 : ℝ)))) :=
    continuous_id.prodMk continuous_const
  have h := (continuous_lorentzExtension_apply
    (E := EuclideanSpace ℝ (Fin (n + 1))) (F := EuclideanSpace ℝ (Fin (n + 1)))).comp hpair
  rcases i with i | i
  · change Continuous (fun F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) =>
      (lorentzExtension F (lorentzCoordinates (n + 1) (Pi.single j (1 : ℝ)))).2 i)
    exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp h.snd
  · change Continuous (fun F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) =>
      (lorentzExtension F (lorentzCoordinates (n + 1) (Pi.single j (1 : ℝ)))).1)
    exact h.fst

private theorem continuous_projectiveRepresentative (n : ℕ) :
    Continuous (projectiveRepresentative n) := by
  have hM := (MatrixSum.continuous_ofMatrix (Fin (n + 1)) (Fin 1) ℝ).comp
    (continuous_projectiveLorentzMatrix n)
  have hL : Continuous (projectiveLorentzLift n) := hM.subtype_mk _
  exact (DifferentialGeometry.StabilizerCompact.continuous_mk'_to_PO (n := n + 1)).comp hL

def projectiveOrthogonalGroupEquiv (n : ℕ) :
    (Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₜ* PO (n + 1) 1 where
  toFun := projectiveRepresentative n
  invFun := projectiveIsometryHom n
  left_inv := projectiveIsometryHom_representative n
  right_inv := projectiveRepresentative_isometryHom n
  map_mul' F G := by
    apply projectiveIsometryHom_injective n
    rw [(projectiveIsometryHom n).map_mul, projectiveIsometryHom_representative,
      projectiveIsometryHom_representative, projectiveIsometryHom_representative]
  continuous_toFun := continuous_projectiveRepresentative n
  continuous_invFun := continuous_projectiveIsometryHom n

theorem projectiveOrthogonalGroupEquiv_smul (n : ℕ)
    (F : Hyperboloid (EuclideanSpace ℝ (Fin (n + 1))) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin (n + 1)))) (x : HUpper (n + 1)) :
    hUpperIsometryEquiv (n + 1)
        ((poMulAction (by omega : 1 ≤ n + 1)).smul (projectiveOrthogonalGroupEquiv n F) x) =
      F (hUpperIsometryEquiv (n + 1) x) := by
  change hUpperIsometryEquiv (n + 1) ((poMulAction (by omega : 1 ≤ n + 1)).smul
    (projectiveRepresentative n F) x) = _
  rw [projectiveRepresentative_action, (hUpperIsometryEquiv (n + 1)).apply_symm_apply]

theorem projectiveOrthogonalGroupEquiv_symm_apply (n : ℕ) (q : PO (n + 1) 1)
    (x : HUpper (n + 1)) :
    (projectiveOrthogonalGroupEquiv n).symm q (hUpperIsometryEquiv (n + 1) x) =
      hUpperIsometryEquiv (n + 1) ((poMulAction (by omega : 1 ≤ n + 1)).smul q x) :=
  projectiveIsometryHom_apply n q x

end DifferentialGeometry.Hyperboloid
