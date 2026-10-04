import DifferentialGeometry.Topology.Manifold.OneManifold.BoundaryCount
import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceRecognition
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.Decomposition

/-! # Disk incidence degree from actual one-manifold boundaries -/

set_option autoImplicit false

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

section Degree

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]
  (side : ι → κ) (C : κ → Type*) [∀ j, TopologicalSpace (C j)]
  [∀ j, T2Space (C j)] [∀ j, CompactSpace (C j)] [∀ j, ConnectedSpace (C j)]
  [∀ j, ChartedSpace (EuclideanHalfSpace 1) (C j)] [∀ j, IsManifold (𝓡∂ 1) ∞ (C j)]

theorem hdeg_of_boundary_equiv
    (e : ∀ j, {i // side i = j} ≃ (𝓡∂ 1).boundary (C j)) :
    ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2 := by
  classical
  intro j
  have he : (Finset.univ.filter (fun i => side i = j)).card =
      ((𝓡∂ 1).boundary (C j)).ncard := by
    let q : {i // i ∈ Finset.univ.filter (fun i => side i = j)} ≃ {i // side i = j} :=
      Equiv.subtypeEquivRight (fun i => by simp)
    calc
      _ = Nat.card {i // i ∈ Finset.univ.filter (fun i => side i = j)} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = Nat.card ((𝓡∂ 1).boundary (C j)) := Nat.card_congr (q.trans (e j))
      _ = _ := rfl
  rw [he]
  exact Manifold.OneManifold.ncard_boundary_eq_zero_or_two

variable {Y : Type*} [TopologicalSpace Y] [Fintype κ]
  (D : ι → Set Y) (B : κ → Set Y)
  (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
  (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
  (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
  (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
  (e : ∀ j, {i // side i = j} ≃ (𝓡∂ 1).boundary (C j))

include D B hD hB hBne hcover hDD hBB hDB C e in
theorem disk_face_count_sphere_of_boundary_equiv (φ : Y ≃ₜ SphereTwo)
    (hbase : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
      ∃ p : B j → Circle, Continuous p ∧ IsOpenMap p) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 2 :=
  Surface.disk_face_count_sphereTwo φ D B hD hB hBne hcover hDD hBB side hDB
    (hdeg_of_boundary_equiv side C e) hbase

include hD hB hBne hcover hDD hBB hDB C e in
theorem disk_face_count_torus_of_boundary_equiv (φ : Y ≃ₜ Circle × Circle)
    (hdisk : ∀ i, ∃ h : Disk 2 → Y, Continuous h ∧ Injective h ∧ range h = D i ∧
      h '' diskSphere 2 = D i ∩ B (side i))
    (hann : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 2 →
      ∃ a : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y,
        Continuous a ∧ Injective a ∧ range a = B j ∧
        ∀ i, side i = j → D i ∩ B j = a '' {q | (q.2 : ℝ) = 0} ∨
          D i ∩ B j = a '' {q | (q.2 : ℝ) = 1}) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 0 :=
  Surface.disk_face_count_torus φ D B hD hB hBne hcover hDD hBB side hDB
    (hdeg_of_boundary_equiv side C e) hdisk hann

end Degree

namespace Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]

theorem fdc02_base_components :
    Finite (ConnectedComponents M) ∧ ∀ x : M,
      Nonempty (componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨
        Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens x) :=
  finite_connectedComponents_and_Icc_or_circle

end Manifold.OneManifold

theorem bcf03_internal_torus_subset {N : Type*} {H P R : Set N}
    (hH : H ⊆ P ∪ R) (hHP : H ∩ P = ∅) : H ⊆ R :=
  DifferentialGeometry.Geometry.Collapse.BoundaryCloud.subset_of_inter_eq_empty hH hHP

end DifferentialGeometry.Topology
