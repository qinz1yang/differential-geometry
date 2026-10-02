import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingIsotopy
import DifferentialGeometry.Topology.Manifold.DiffeomorphFamily

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

theorem BallMarking.isotopic_of_supportFamily (B B' : BallMarking M I)
    (J : I → ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
    (U : I → Set M.Carrier)
    (hJ : ∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier ↦ J i q.1 q.2))
    (hJi : ∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier ↦ (J i q.1).symm q.2))
    (hJ0 : ∀ i, J i 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i t x, x ∉ U i → J i t x = x ∧ (J i t).symm x = x)
    (hU : ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2, (B.ball i).chart x ∉ U j)
    (hJ1 : ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      J i 1 ((B.ball i).chart x) = (B'.ball i).chart x) :
    B.Isotopic B' := by
  refine ⟨fun t ↦ Manifold.diffeomorphList J (Finset.univ : Finset I).toList (fun _ ↦ t),
    Manifold.contMDiff_diffeomorphList_univ_diagonal J hJ,
    Manifold.contMDiff_diffeomorphList_univ_diagonal_symm J hJi,
    Manifold.diffeomorphList_univ_diagonal_zero J hJ0, ?_⟩
  intro i x hx
  have hmem : i ∈ (Finset.univ : Finset I).toList := Finset.mem_toList.mpr (Finset.mem_univ i)
  have hy : ∀ j ∈ (Finset.univ : Finset I).toList, j ≠ i → (B.ball i).chart x ∉ U j :=
    fun j _ hji ↦ hU i j (Ne.symm hji) x hx
  rw [Manifold.diffeomorphList_diagonal_one_apply_eq_of_disjoint_support J U hdisj hfix _
    (Finset.nodup_toList _) hmem hy]
  exact hJ1 i x hx

theorem BallMarking.transport_of_supportDiffeomorphFamily (B B' : BallMarking M I)
    (F : I → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞) (U : I → Set M.Carrier)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i x, x ∉ U i → F i x = x ∧ (F i).symm x = x)
    (hU : ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2, (B.ball i).chart x ∉ U j)
    (hF1 : ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      F i ((B.ball i).chart x) = (B'.ball i).chart x) :
    B.Transport B' := by
  refine ⟨Manifold.diffeomorphList (fun i _ ↦ F i) (Finset.univ : Finset I).toList
    (fun _ ↦ (1 : ℝ)), ?_⟩
  intro i x hx
  have hmem : i ∈ (Finset.univ : Finset I).toList := Finset.mem_toList.mpr (Finset.mem_univ i)
  have hy : ∀ j ∈ (Finset.univ : Finset I).toList, j ≠ i → (B.ball i).chart x ∉ U j :=
    fun j _ hji ↦ hU i j (Ne.symm hji) x hx
  rw [Manifold.diffeomorphList_diagonal_one_apply_eq_of_disjoint_support (fun i _ ↦ F i) U hdisj
    (fun i t x hx ↦ hfix i x hx) _ (Finset.nodup_toList _) hmem hy]
  exact hF1 i x hx

theorem BallMarking.transport_of_supportDiffeomorphFamily_refl (B : BallMarking M I) :
    B.Transport B :=
  B.transport_of_supportDiffeomorphFamily B (fun _ ↦ Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (fun _ ↦ ∅) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ ⟨rfl, rfl⟩)
    (fun _ _ _ _ _ ↦ by simp) (fun _ _ _ ↦ rfl)

theorem connectedBallMarkingIsotopy_of_supportFamily
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u) [Fintype I]
      (B B' : BallMarking M I),
      ∃ (J : I → ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
        (U : I → Set M.Carrier),
        (∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : ℝ × M.Carrier ↦ J i q.1 q.2)) ∧
        (∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : ℝ × M.Carrier ↦ (J i q.1).symm q.2)) ∧
        (∀ i, J i 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
        (∀ i t x, x ∉ U i → J i t x = x ∧ (J i t).symm x = x) ∧
        (∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2,
          (B.ball i).chart x ∉ U j) ∧
        (∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
          J i 1 ((B.ball i).chart x) = (B'.ball i).chart x)) :
    connectedBallMarkingIsotopy.{u} := by
  intro M _ I _ B B'
  obtain ⟨J, U, hJ, hJi, hJ0, hdisj, hfix, hU, hJ1⟩ := h M I B B'
  exact B.isotopic_of_supportFamily B' J U hJ hJi hJ0 hdisj hfix hU hJ1

theorem BallMarking.isotopic_of_supportFamily_refl (B : BallMarking M I) : B.Isotopic B :=
  B.isotopic_of_supportFamily B (fun _ _ ↦ Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (fun _ ↦ ∅)
    (fun _ ↦ contMDiff_snd) (fun _ ↦ contMDiff_snd) (fun _ ↦ rfl)
    (fun _ _ _ ↦ by simp) (fun _ _ _ _ ↦ ⟨rfl, rfl⟩) (fun _ _ _ _ _ ↦ by simp)
    (fun _ _ _ ↦ rfl)

end DifferentialGeometry.Topology
