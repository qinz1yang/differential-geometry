/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FieldPathCones

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X]

noncomputable abbrev fieldSingularCycles (n : ℕ) :=
  LinearMap.ker ((fieldSingularChains (k := k) (X := X)).d (n + 1) n).hom

noncomputable def fieldSingularBoundaryToCycles (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).X (n + 2) →ₗ[k]
      fieldSingularCycles (k := k) (X := X) n :=
  ((fieldSingularChains (k := k) (X := X)).sc' (n + 2) (n + 1) n).moduleCatToCycles

noncomputable def fieldSingularHomologyCycleEquiv (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).homology (n + 1) ≃ₗ[k]
      (fieldSingularCycles (k := k) (X := X) n ⧸
        LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) n)) :=
  (CategoryTheory.ShortComplex.homologyMapIso
      ((fieldSingularChains (k := k) (X := X)).isoSc'
        (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    ((fieldSingularChains (k := k) (X := X)).sc'
      (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv

end DifferentialGeometry.Topology
