import DifferentialGeometry.Topology.Handle.Attachment
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

open scoped unitInterval

namespace DifferentialGeometry.Topology.Handle

private theorem one_cell_boundary_circle_eq_zero (u : CellBoundary 1) :
    (((u.1 0 + 1) / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have hsq : (u.1 0) ^ 2 = 1 := by
    simpa [u.property] using (EuclideanSpace.real_norm_sq_eq u.1).symm
  rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h, AddCircle.coe_period]

private noncomputable def oneHandleCircleMap {X : Type*} [TopologicalSpace X] {l : ℕ}
    (φ : AttachingRegion 1 l → X) : C(AdjunctionSpace 1 l φ, AddCircle (1 : ℝ)) := by
  let F : StandardHandle 1 l ⊕ X → AddCircle (1 : ℝ) :=
    Sum.elim (fun z => (((z.1.1 0 + 1) / 2 : ℝ) : AddCircle (1 : ℝ))) (fun _ => 0)
  have hrel : ∀ a b, adjunctionRel (attachingInclusion 1 l) φ a b → F a = F b := by
    rintro a b ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact one_cell_boundary_circle_eq_zero u.1
    · exact (one_cell_boundary_circle_eq_zero u.1).symm
  refine ⟨Quot.lift F hrel, continuous_adjunction_lift _ _ hrel ?_⟩
  apply Continuous.sumElim
  · exact continuous_quotient_mk'.comp
      (((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
        (continuous_subtype_val.comp continuous_fst)).add continuous_const |>.div_const 2)
  · exact continuous_const

private theorem oneHandleCircleMap_cell {X : Type*} [TopologicalSpace X] {l : ℕ}
    (φ : AttachingRegion 1 l → X) (z : StandardHandle 1 l) :
    oneHandleCircleMap φ (cell φ z) = (((z.1.1 0 + 1) / 2 : ℝ) : AddCircle (1 : ℝ)) := rfl

private theorem oneHandleCircleMap_lower {X : Type*} [TopologicalSpace X] {l : ℕ}
    (φ : AttachingRegion 1 l → X) (x : X) : oneHandleCircleMap φ (lower φ x) = 0 := rfl

theorem not_simplyConnectedSpace_adjunction_of_joined_feet {X : Type*} [TopologicalSpace X]
    {l : ℕ} (φ : AttachingRegion 1 l → X) {u v : CellBoundary 1} (huv : u ≠ v)
    (hjoined : Joined (φ (u, closedCellCenter l)) (φ (v, closedCellCenter l))) :
    ¬ SimplyConnectedSpace (AdjunctionSpace 1 l φ) := by
  classical
  intro hsimply
  let _ := hsimply
  let _ : PathConnectedSpace (ClosedCell 1) := by
    have heq : {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    have hpc : IsPathConnected {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 1} := by
      rw [heq]
      exact Metric.isPathConnected_closedBall zero_le_one
    exact isPathConnected_iff_pathConnectedSpace.mp hpc
  let η : Path (cellBoundaryInclusion 1 u) (cellBoundaryInclusion 1 v) :=
    PathConnectedSpace.somePath _ _
  let γ : Path (lower φ (φ (u, closedCellCenter l))) (lower φ (φ (v, closedCellCenter l))) :=
    (η.map ((continuous_cell φ).comp (continuous_coreDiskInclusion 1 l))).cast
      (adjunction_coherence φ (u, closedCellCenter l)).symm
      (adjunction_coherence φ (v, closedCellCenter l)).symm
  let β := hjoined.somePath.map (continuous_lower φ)
  let a : C(I, ℝ) := ⟨fun t => ((η t).1 0 + 1) / 2, by
    exact (((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp η.continuous)).add continuous_const).div_const 2⟩
  let b : C(I, ℝ) := ContinuousMap.const I ((u.1 0 + 1) / 2)
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  have ha : (⟨((↑) : ℝ → AddCircle (1 : ℝ)), cov.continuous⟩ : C(ℝ, AddCircle (1 : ℝ))).comp a =
      (oneHandleCircleMap φ).comp γ.toContinuousMap := by
    ext t
    exact (oneHandleCircleMap_cell φ (coreDiskInclusion 1 l (η t))).symm
  have hb : (⟨((↑) : ℝ → AddCircle (1 : ℝ)), cov.continuous⟩ : C(ℝ, AddCircle (1 : ℝ))).comp b =
      (oneHandleCircleMap φ).comp β.toContinuousMap := by
    ext t
    exact (one_cell_boundary_circle_eq_zero u).trans
      (oneHandleCircleMap_lower φ (hjoined.somePath t)).symm
  have hmaps := ContinuousMap.HomotopicRel.comp_continuousMap
    (SimplyConnectedSpace.paths_homotopic γ β) (oneHandleCircleMap φ)
  rw [← ha, ← hb] at hmaps
  have hlift : a.HomotopicRel b {0, 1} := (cov.homotopicRel_iff_comp (f₀ := a) (f₁ := b)
    (S := ({0, 1} : Set I))
    ⟨0, Or.inl rfl, by
      change ((η 0).1 0 + 1) / 2 = (u.1 0 + 1) / 2
      rw [η.source]
      rfl⟩).mpr hmaps
  have hend := hlift.fst_eq_snd (x := 1) (Or.inr rfl)
  have hcoord : v.1 0 = u.1 0 := by
    change ((η 1).1 0 + 1) / 2 = (u.1 0 + 1) / 2 at hend
    rw [η.target] at hend
    change (v.1 0 + 1) / 2 = (u.1 0 + 1) / 2 at hend
    linarith
  apply huv
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using hcoord.symm

end DifferentialGeometry.Topology.Handle
