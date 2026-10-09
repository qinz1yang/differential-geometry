/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import Mathlib.Geometry.Manifold.LocalInvariantProperties

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

def piecewiseAffineProperty (n m : ℕ) :
    (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) → Set (EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) → Prop :=
  fun g t y => IsPiecewiseAffineWithinAt g t y

variable {n m : ℕ}

theorem piecewiseAffineProperty_id (y : EuclideanSpace ℝ (Fin n)) :
    piecewiseAffineProperty n n id univ y :=
  isPiecewiseAffineOn_id isOpen_univ y (mem_univ y)

theorem piecewiseAffineProperty_localInvariantProp :
    (plGroupoid n).LocalInvariantProp (plGroupoid m) (piecewiseAffineProperty n m) where
  is_local hu hx :=
    ⟨fun h => IsPiecewiseAffineWithinAt.inter_of_mem_nhds h (hu.mem_nhds hx),
      fun h => IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds h (hu.mem_nhds hx)⟩
  right_invariance' := by
    intro s x f e he hx hf
    have hsymm : IsPiecewiseAffineWithinAt e.symm e.target (e x) :=
      (mem_plGroupoid_iff.mp he).2 (e x) (e.map_source hx)
    have hf' : IsPiecewiseAffineWithinAt f s (e.symm (e x)) := by
      rw [e.left_inv hx]
      exact hf
    have hcomp := hf'.comp hsymm
    rw [inter_comm] at hcomp
    exact hcomp.of_inter_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))
  congr_of_forall := by
    intro s x f g hfg _ hf
    exact IsPiecewiseAffineWithinAt.congr hf fun y hy => (hfg y hy).symm
  left_invariance' := by
    intro s x f e' he' hs hx hf
    have he'' : IsPiecewiseAffineWithinAt e' e'.source (f x) :=
      (mem_plGroupoid_iff.mp he').1 (f x) hx
    have hcomp := he''.comp hf
    rw [inter_eq_left.mpr hs] at hcomp
    exact hcomp

variable (n m) {M N : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

def IsPLWithinAt (f : M → N) (s : Set M) (x : M) : Prop :=
  ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n m) f s x

def IsPLAt (f : M → N) (x : M) : Prop :=
  ChartedSpace.LiftPropAt (piecewiseAffineProperty n m) f x

def IsPLOn (f : M → N) (s : Set M) : Prop :=
  ChartedSpace.LiftPropOn (piecewiseAffineProperty n m) f s

def IsPL (f : M → N) : Prop :=
  ChartedSpace.LiftProp (piecewiseAffineProperty n m) f

variable {n m}

theorem isPL_id : IsPL n n (id : M → M) :=
  piecewiseAffineProperty_localInvariantProp.liftProp_id piecewiseAffineProperty_id

theorem isPLOn_chart [HasGroupoid M (plGroupoid n)] (x : M) :
    IsPLOn n n (chartAt (EuclideanSpace ℝ (Fin n)) x)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
  piecewiseAffineProperty_localInvariantProp.liftPropOn_chart piecewiseAffineProperty_id

theorem isPLOn_chart_symm [HasGroupoid M (plGroupoid n)] (x : M) :
    IsPLOn n n (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
      (chartAt (EuclideanSpace ℝ (Fin n)) x).target :=
  piecewiseAffineProperty_localInvariantProp.liftPropOn_chart_symm piecewiseAffineProperty_id

theorem isPLWithinAt_iff_of_mem_maximalAtlas
    {f : M → N} {s : Set M} {x : M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ (plGroupoid n).maximalAtlas M) (hx : x ∈ e.source)
    {e' : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))}
    (he' : e' ∈ (plGroupoid m).maximalAtlas N) (hfx : f x ∈ e'.source) :
    IsPLWithinAt n m f s x ↔
      ContinuousWithinAt f s x ∧
        IsPiecewiseAffineWithinAt (e' ∘ f ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hfx

theorem isPLAt_iff_of_mem_maximalAtlas
    {f : M → N} {x : M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ (plGroupoid n).maximalAtlas M) (hx : x ∈ e.source)
    {e' : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))}
    (he' : e' ∈ (plGroupoid m).maximalAtlas N) (hfx : f x ∈ e'.source) :
    IsPLAt n m f x ↔
      ContinuousAt f x ∧ IsPiecewiseAffineWithinAt (e' ∘ f ∘ e.symm) univ (e x) := by
  have h := isPLWithinAt_iff_of_mem_maximalAtlas (s := univ) he hx he' hfx
  rw [continuousWithinAt_univ, preimage_univ] at h
  exact h

theorem isPL_symm_of_homeomorph [HasGroupoid M (plGroupoid n)] {P : Type*} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [HasGroupoid P (plGroupoid n)]
    {f : M ≃ₜ P} (hf : IsPL n n f) : IsPL n n f.symm := by
  intro y
  set x := f.symm y with hx_def
  have hfx : f x = y := f.apply_symm_apply y
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x with he_def
  set e' := chartAt (EuclideanSpace ℝ (Fin n)) y with he'_def
  have hmax₁ : e ∈ (plGroupoid n).maximalAtlas M :=
    StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) x
  have hmax₂ : e' ∈ (plGroupoid n).maximalAtlas P :=
    StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) y
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hye : y ∈ e'.source := mem_chart_source _ y
  let F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    e.symm ≫ₕ f.toOpenPartialHomeomorph ≫ₕ e'
  have hFsrc : ∀ z, z ∈ F.source ↔ z ∈ e.target ∧ f (e.symm z) ∈ e'.source := by
    intro z
    constructor
    · rintro ⟨hz, -, hz'⟩
      exact ⟨hz, hz'⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, trivial, hz'⟩
  have hF : IsPiecewiseAffineOn F F.source := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := (hFsrc z).mp hz
    have hz1' : e.symm z ∈ e.source := e.map_target hz1
    obtain ⟨-, hPA⟩ := (isPLAt_iff_of_mem_maximalAtlas hmax₁ hz1' hmax₂ hz2).mp (hf (e.symm z))
    rw [e.right_inv hz1] at hPA
    have hPA' := hPA.inter_of_mem_nhds (F.open_source.mem_nhds hz)
    rw [univ_inter] at hPA'
    exact hPA'.congr fun _ _ => rfl
  have hFsymm : IsPiecewiseAffineOn F.symm F.target := hF.symm
  have hyF : e' y ∈ F.target := by
    have hxF : e x ∈ F.source := (hFsrc (e x)).mpr ⟨e.map_source hxe, by
      rw [e.left_inv hxe, hfx]
      exact hye⟩
    have hFx : F (e x) = e' y := by
      change e' (f (e.symm (e x))) = e' y
      rw [e.left_inv hxe, hfx]
    rw [← hFx]
    exact F.map_source hxF
  change IsPLAt n n f.symm y
  rw [isPLAt_iff_of_mem_maximalAtlas (f := ⇑f.symm) hmax₂ hye hmax₁ hxe]
  refine ⟨f.symm.continuous.continuousAt, ?_⟩
  have hPA := (hFsymm (e' y) hyF).congr (g := e ∘ f.symm ∘ e'.symm) fun _ _ => rfl
  have hPA' : IsPiecewiseAffineWithinAt (e ∘ f.symm ∘ e'.symm) (univ ∩ F.target) (e' y) := by
    rwa [univ_inter]
  exact hPA'.of_inter_of_mem_nhds (F.open_target.mem_nhds hyF)

universe u

def PLApproximationManifold (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)] (h : M₁ ≃ₜ M₂)
    (φ : M₁ → ℝ), Continuous φ → (∀ x, 0 < φ x) →
    ∃ f : M₁ ≃ₜ M₂, IsPL n n f ∧ ∀ x, dist (f x) (h x) < φ x

end DifferentialGeometry.Topology.PiecewiseLinear
