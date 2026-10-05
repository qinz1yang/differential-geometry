import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Composition
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OpenEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_isPLHomeomorphInto_dist_lt_of_inward_push
    {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K W : Set M₁} {h g : M₁ → M₂} {p q : M₁ → M₁} {φ : M₁ → ℝ}
    (hKloc : ∀ x ∈ K, ∃ A ⊆ K, IsCompact A ∧ x ∈ A ∧ A ∈ 𝓝[K] x)
    (hW : IsOpen W) (hpmaps : MapsTo p K W) (hppl : IsPLOn n n p K)
    (hpinj : InjOn p K) (hqpl : IsPLOn n n q W) (hqp : LeftInvOn q p K)
    (hclose : ∀ x ∈ K, dist (h (p x)) (h x) < φ x / 2)
    (hg : IsPLHomeomorphInto n g W)
    (hgclose : ∀ y ∈ W, dist (g y) (h y) < φ (q y) / 2) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x := by
  refine ⟨g ∘ p, isPLHomeomorphInto_comp_of_leftInvOn hKloc hW hpmaps hppl hpinj hqpl hqp hg,
    fun x hx => ?_⟩
  have h1 : dist (g (p x)) (h (p x)) < φ x / 2 := by
    have h0 := hgclose (p x) (hpmaps hx)
    rwa [hqp hx] at h0
  have h2 := hclose x hx
  change dist (g (p x)) (h x) < φ x
  calc dist (g (p x)) (h x) ≤ dist (g (p x)) (h (p x)) + dist (h (p x)) (h x) :=
        dist_triangle _ _ _
    _ < φ x := by linarith

theorem exists_isPLHomeomorphInto_dist_lt_three
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {K : Set M₁} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (φ : M₁ → ℝ)
    (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x := by
  obtain ⟨p, q, W, hW, hWint, hpmaps, hppl, hpinj, hqpl, hqmaps, hqp, hclose⟩ :=
    hK.exists_isPLOn_injOn_leftInvOn_dist_lt
      (continuousOn_iff_continuous_domRestrict.mpr hh.continuous)
      (ψ := fun x => φ x / 2) (hφ.div_const 2) fun x hx => half_pos (hpos x hx)
  have hWK : W ⊆ K := hWint.trans interior_subset
  have hhW : Topology.IsEmbedding (W.domRestrict h) :=
    hh.comp (Topology.IsEmbedding.inclusion hWK)
  have hqcont : ContinuousOn q W := fun y hy => (hqpl y hy).continuousWithinAt
  have hηcont : ContinuousOn (fun y => φ (q y) / 2) W :=
    (show ContinuousOn (fun y => φ (q y)) W from hφ.comp hqcont hqmaps).div_const 2
  have hηpos : ∀ y ∈ W, 0 < φ (q y) / 2 := fun y hy => half_pos (hpos (q y) (hqmaps hy))
  obtain ⟨g, hg, hgclose⟩ := exists_isPLHomeomorphInto_dist_lt_of_isOpen_three hW hhW (fun y => φ (q y) / 2) hηcont hηpos
  exact exists_isPLHomeomorphInto_dist_lt_of_inward_push
    (fun x hx => hK.exists_isCompact_mem_nhdsWithin hx) hW hpmaps hppl hpinj hqpl hqp hclose hg
    hgclose

end DifferentialGeometry.Topology.PiecewiseLinear
