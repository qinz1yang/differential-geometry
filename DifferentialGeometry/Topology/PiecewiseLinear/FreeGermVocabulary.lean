/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

/-!
# Free source germs and the region-glued map

Hoisted verbatim from `Skeleton/GeneralPositionInDouble.lean`, so that the leaves of general
position in the double can be stated in real modules.  `FreeSourceGerm R Ac g S y` asks of every
point `x` of the fibre of `g` over `y` in `S` that `R.space` be a neighbourhood of `x` in `S` and
that no simplex of `R` containing `x` have a vertex in the frozen collar `Ac.space`;
`IsFreeDoubleGerm`, `IsFreeBoundaryDoubleGerm` and `IsFreeInteriorDoubleGerm` add `y ∉ BdM`,
`y ∈ BdM`, and that every fibre point lie in the interior of a triangle of `R`.
`regionGluedMap D ec Rs φ Rc` is `ec.symm ∘ simplicialMap Rs φ` on `Rc.space` and `D` elsewhere.
When wiring, the skeleton's copies of these five definitions are to be deleted and this module
imported.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def FreeSourceGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (y : M) : Prop :=
  ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x ∧ ∀ σ ∈ R.faces,
    x ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) → ∀ v ∈ σ, v ∉ Ac.space

def IsFreeDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∉ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeBoundaryDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∈ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeInteriorDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  IsFreeDoubleGerm R Ac g S BdM y ∧
    ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open Classical in
noncomputable def regionGluedMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) → M :=
  fun x => if x ∈ Rc.space then ec.symm (simplicialMap Rs φ x) else D x

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
