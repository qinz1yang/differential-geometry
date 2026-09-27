import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem slab_boundary_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (F : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) M ∞) {a b : ℝ} (hab : a < b)
    (hsrc : univ ×ˢ Icc a b ⊆ F.source) (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    ∃ c : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞,
      F (p, b) ∈ c.source ∧ (c (F (p, b))) 0 = 0 ∧
        ∀ y ∈ c.source,
          (y ∈ F '' (univ ×ˢ Icc a b) ↔ (c y) 0 ≤ 0) := by
  let phi := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := (𝓡 2)) p
  let Q := DifferentialGeometry.Topology.PartialDiffeomorph.prod phi (DifferentialGeometry.Topology.translateDiffeomorph (-b)).toPartialDiffeomorph
  let Q' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Q
    {q : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) | a < q.2} (isOpen_lt continuous_const continuous_snd)
  let L := (DifferentialGeometry.Topology.signedNormalFirstDiffeomorph 2 true).toPartialDiffeomorph
  let c := (F.symm.trans Q').trans L
  have hp : (p, b) ∈ F.source := hsrc ⟨mem_univ _, hab.le, le_rfl⟩
  have hphi : p ∈ phi.source := mem_extChartAt_source p
  have hpoint : F.symm (F (p, b)) = (p, b) := F.left_inv' hp
  refine ⟨c, ?_, ?_, ?_⟩
  · change (F (p, b) ∈ F.target ∧ F.symm (F (p, b)) ∈ Q'.source) ∧ _
    rw [hpoint]
    exact ⟨⟨F.map_source' hp, ⟨⟨hphi, mem_univ _⟩, hab⟩⟩, mem_univ _⟩
  · change (F.symm (F (p, b))).2 + -b = 0
    rw [hpoint]
    exact add_neg_cancel b
  · intro y hy
    have hyt : y ∈ F.target := hy.1.1
    have hlow : a < (F.symm y).2 := hy.1.2.2
    change y ∈ F '' (univ ×ˢ Icc a b) ↔ (F.symm y).2 + -b ≤ 0
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [show F.symm (F z) = z from F.left_inv' (hsrc hz)]
      exact sub_nonpos.mpr hz.2.2
    · intro hhigh
      exact ⟨F.symm y, ⟨mem_univ _, hlow.le, sub_nonpos.mp hhigh⟩, F.right_inv' hyt⟩

private theorem slab_lower_boundary_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (F : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) M ∞) {a b : ℝ} (hab : a < b)
    (hsrc : univ ×ˢ Icc a b ⊆ F.source) (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    ∃ c : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞,
      F (p, a) ∈ c.source ∧ (c (F (p, a))) 0 = 0 ∧
        ∀ y ∈ c.source,
          (y ∈ F '' (univ ×ˢ Icc a b) ↔ (c y) 0 ≤ 0) := by
  let phi := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := (𝓡 2)) p
  let Q := DifferentialGeometry.Topology.PartialDiffeomorph.prod phi (DifferentialGeometry.Topology.translateDiffeomorph (-a)).toPartialDiffeomorph
  let Q' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Q
    {q : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) | q.2 < b} (isOpen_lt continuous_snd continuous_const)
  let L := (DifferentialGeometry.Topology.signedNormalFirstDiffeomorph 2 false).toPartialDiffeomorph
  let c := (F.symm.trans Q').trans L
  have hp : (p, a) ∈ F.source := hsrc ⟨mem_univ _, le_rfl, hab.le⟩
  have hphi : p ∈ phi.source := mem_extChartAt_source p
  have hpoint : F.symm (F (p, a)) = (p, a) := F.left_inv' hp
  refine ⟨c, ?_, ?_, ?_⟩
  · change (F (p, a) ∈ F.target ∧ F.symm (F (p, a)) ∈ Q'.source) ∧ _
    rw [hpoint]
    exact ⟨⟨F.map_source' hp, ⟨⟨hphi, mem_univ _⟩, hab⟩⟩, mem_univ _⟩
  · change -((F.symm (F (p, a))).2 + -a) = 0
    rw [hpoint]
    simp
  · intro y hy
    have hyt : y ∈ F.target := hy.1.1
    have hupper : (F.symm y).2 < b := hy.1.2.2
    change y ∈ F '' (univ ×ˢ Icc a b) ↔ -((F.symm y).2 + -a) ≤ 0
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [show F.symm (F z) = z from F.left_inv' (hsrc hz)]
      linarith [hz.2.1]
    · intro hhigh
      exact ⟨F.symm y, ⟨mem_univ _, by linarith, hupper.le⟩, F.right_inv' hyt⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
