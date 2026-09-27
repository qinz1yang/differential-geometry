/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Attachment.Homeomorph
import DifferentialGeometry.Topology.Homeomorph.SphereExtension

open Metric Set

namespace DifferentialGeometry.Topology

noncomputable def closedCellHomeomorphExtension {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) : ClosedCell n ≃ₜ ClosedCell m := by
  let e₁ : CellBoundary n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.setCongr (by ext x; exact mem_sphere_zero_iff_norm.symm)
  let e₂ : CellBoundary m ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin m)) 1 :=
    Homeomorph.setCongr (by ext x; exact mem_sphere_zero_iff_norm.symm)
  exact (sphereRadialHomeomorph ((e₁.symm.trans f).trans e₂)).subtype fun x => by
    rw [norm_sphereRadialHomeomorph]

@[simp]
theorem norm_closedCellHomeomorphExtension {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) (x : ClosedCell n) :
    ‖(closedCellHomeomorphExtension f x : EuclideanSpace ℝ (Fin m))‖ = ‖x.val‖ :=
  norm_sphereRadialHomeomorph _ _

@[simp]
theorem closedCellHomeomorphExtension_boundary {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) (x : CellBoundary n) :
    closedCellHomeomorphExtension f (cellBoundaryInclusion n x) =
      cellBoundaryInclusion m (f x) := by
  apply Subtype.ext
  exact sphereRadialHomeomorph_apply_sphere _
    ⟨x.val, mem_sphere_zero_iff_norm.mpr x.property⟩

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def cellAdjunctionHomeomorph {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) :
    CellAdjunctionSpace n φ ≃ₜ CellAdjunctionSpace m ψ :=
  adjunctionHomeomorph (cellBoundaryInclusion n) φ (cellBoundaryInclusion m) ψ
    a.toEquiv (closedCellHomeomorphExtension a) f
    (closedCellHomeomorphExtension_boundary a) hφ

@[simp]
theorem cellAdjunctionHomeomorph_lower {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) (x : X) :
    cellAdjunctionHomeomorph φ ψ a f hφ (adjunctionLower φ x) =
      adjunctionLower ψ (f x) := rfl

@[simp]
theorem cellAdjunctionHomeomorph_cell {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) (x : ClosedCell n) :
    cellAdjunctionHomeomorph φ ψ a f hφ (adjunctionCell (cellBoundaryInclusion n) φ x) =
      adjunctionCell (cellBoundaryInclusion m) ψ (closedCellHomeomorphExtension a x) := rfl

end DifferentialGeometry.Topology
