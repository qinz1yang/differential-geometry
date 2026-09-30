/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import DifferentialGeometry.Topology.SimplicialComplex.GeometricLink
import DifferentialGeometry.Topology.Simplex.Coordinates
import Mathlib.Analysis.Convex.StdSimplex

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsPLHomeomorphOn (f : E → F) (P : Set E) (Q : Set F) : Prop :=
  BijOn f P Q ∧ IsPiecewiseAffineOn f P ∧ IsPiecewiseAffineOn (Function.invFunOn f P) Q

theorem isHPolytope_stdSimplex (ι : Type) [Fintype ι] : IsHPolytope (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  refine ⟨Convexity.StdSimplex.isCompact_coordinateSet ℝ ι, ι ⊕ Bool, inferInstance,
    Sum.elim (fun i => -(LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ))
      (fun b => if b then ∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
        else -∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)),
    Sum.elim (fun _ => 0) (fun b => if b then 1 else -1), ?_⟩
  ext x
  simp only [Convexity.StdSimplex.coordinateSet, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    LinearMap.neg_apply, LinearMap.proj_apply, Bool.forall_bool, Bool.false_eq_true, ite_false,
    ite_true, LinearMap.sum_apply, neg_le_neg_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => by linarith [h0 i], h1.ge, h1.le⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨fun i => by linarith [h0 i], le_antisymm h2 h1⟩

theorem isPLHomeomorphOn_id_of_isHPolytope {P : Set E} (hP : IsHPolytope P) :
    IsPLHomeomorphOn (id : E → E) P P :=
  ⟨bijOn_id P, isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.id ℝ E) hP,
    (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.id ℝ E) hP).congr
      fun _ hy => (bijOn_id P).invOn_invFunOn.1 hy⟩

def stdSimplexBoundary (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) ∧ ∃ i, x i = 0}

def IsPLBall (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 1) → ℝ) → E, IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) P

def IsPLSphere (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn f (stdSimplexBoundary (n + 1)) P

theorem IsPLBall.nonempty {n : ℕ} {P : Set E} (hP : IsPLBall n P) : P.Nonempty := by
  obtain ⟨f, hf⟩ := hP
  exact ⟨f (Pi.single (0 : Fin (n + 1)) 1), hf.1.mapsTo (Convexity.StdSimplex.single_mem_coordinateSet ℝ _)⟩

theorem IsPLSphere.nonempty {n : ℕ} {P : Set E} (hP : IsPLSphere n P) : P.Nonempty := by
  obtain ⟨f, hf⟩ := hP
  refine ⟨f (Pi.single (0 : Fin (n + 2)) 1), hf.1.mapsTo ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ _, 1, ?_⟩⟩
  simp

theorem isPLBall_stdSimplex (n : ℕ) : IsPLBall n (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) :=
  ⟨id, isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)⟩

open Classical in
def IsCombinatorialManifold : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (SimplicialComplex.geometricLink K {v}).space

universe u

open Classical in
def CombinatorialManifoldPLStructure (n : ℕ) : Prop :=
  ∀ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))), Finite K.faces →
    IsCombinatorialManifold n K →
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) K.space,
      letI := C
      HasGroupoid K.space (plGroupoid n) ∧
      ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) K.space,
        IsPiecewiseAffineOn (fun p => if h : p ∈ K.space then e ⟨p, h⟩ else 0)
          (Subtype.val '' e.source) ∧
        IsPiecewiseAffineOn (fun y => ((e.symm y : K.space) : EuclideanSpace ℝ (Fin N))) e.target

structure PLTriangulation (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] where
  ambientDim : ℕ
  complex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDim))
  finite_faces : Finite complex.faces
  map : EuclideanSpace ℝ (Fin ambientDim) → X
  bijOn : BijOn map complex.space univ
  continuousOn : ContinuousOn map complex.space
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm) e.target

def PLManifoldTriangulation (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [Nonempty X] (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    letI := C
    ∃ T : PLTriangulation n X, IsCombinatorialManifold n T.complex

end DifferentialGeometry.Topology.PiecewiseLinear
