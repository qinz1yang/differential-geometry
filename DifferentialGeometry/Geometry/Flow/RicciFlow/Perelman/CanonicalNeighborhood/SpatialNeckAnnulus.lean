import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckOverlap
import DifferentialGeometry.Topology.Manifold.GraphBand

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}
  {eps : ℝ} {x y : M}

theorem SpatialNeck.exists_annulus_in_nearby_neck
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000)
    (hy : y ∈ nk₀.map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)))
    (hdisjoint : Disjoint (nk₀.map '' (univ ×ˢ ({0} : Set ℝ)))
      (nk₁.map '' (univ ×ˢ ({0} : Set ℝ)))) :
    ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
      ∃ Ψ : PartialDiffeomorph IC I3 Cylinder M ∞,
        (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
        (∀ p, Ψ (p, 0) = nk₀.map (p, 0)) ∧
        (∀ p, Ψ (p, 1) = nk₁.map (eta p, 0)) ∧
        IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
        (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
          nk₀.map '' (univ ×ˢ ({0} : Set ℝ)) ∪
            nk₁.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
        Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
          nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk₀.eps_pos
  obtain ⟨eta, height, hheight, hmem, hgraph⟩ :=
    nk₀.exists_graph_in_nearby_neck nk₁ hsmall hy
      (by constructor <;> linarith : (0 : ℝ) ∈ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10))
  have hne (p : Sphere 2) : (0 : ℝ) ≠ height p := by
    intro hp
    apply Set.disjoint_left.mp hdisjoint
      (show nk₀.map (p, 0) ∈ nk₀.map '' (univ ×ˢ ({0} : Set ℝ)) from
        ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩)
    refine ⟨(eta p, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    have hh := hgraph p
    rw [← hp] at hh
    exact hh.symm
  have hband : {z : Cylinder | z.2 ∈ uIcc 0 (height z.1)} ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨mem_univ _, (lt_min (neg_lt_zero.mpr hi) (hmem z.1).1).trans_le hz.1,
      hz.2.trans_lt (max_lt hi (hmem z.1).2)⟩
  obtain ⟨Ψ, hsource, hval, himage, hcompact, hfront⟩ :=
    DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk₀.map
      (fun _ ↦ 0) height contMDiff_const hheight hne (hband.trans nk₀.domain)
  have hrange (f : Cylinder → M) :
      range (fun p : Sphere 2 ↦ f (p, 0)) = f '' (univ ×ˢ ({0} : Set ℝ)) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨p, rfl⟩
  have hupper : range (fun p ↦ nk₀.map (p, height p)) =
      range (fun p : Sphere 2 ↦ nk₁.map (p, 0)) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨eta p, (hgraph p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨eta.symm p, ?_⟩
      simpa only [eta.apply_symm_apply] using hgraph (eta.symm p)
  refine ⟨eta, Ψ, hsource, ?_, ?_, hcompact, ?_, ?_⟩
  · intro p
    simp [hval]
  · intro p
    simpa only [hval, zero_add, sub_zero, mul_one] using hgraph p
  · rw [hfront, hupper, hrange, hrange]
  · rw [himage]
    exact image_mono hband

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
