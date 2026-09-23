import DifferentialGeometry.Topology.Manifold.SurvivingSlabSelection
import DifferentialGeometry.Geometry.Neck.ProperSlabEnd

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_proper_neck_end_of_finite_updates
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B})
    (label : ℕ → ι) (hlabels : (range label).Finite)
    (sphere : ℕ → ι → Sphere 2 → M)
    (hunchanged : ∀ n i, label n ≠ i → sphere (n + 1) i = sphere n i)
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (μ : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hlower : ∀ n z, P n (z, 0) = sphere n (label n) z)
    (hupper : ∀ n z, P n (z, 1) = sphere (n + 1) (label n) (μ n z))
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W n = range (sphere n (label n)))
    (hsphere : ∀ n, range (sphere n (label n)) ⊆ frontier (W n))
    (hfilled : ∀ n, range (sphere n (label n)) ⊆ interior (W (n + 1)))
    (point : ℕ → M) (neck : ∀ n, SpatialNeck g eps (point n))
    (hcontrolled : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
      P n '' (univ ×ˢ Icc (0 : ℝ) 1)) :
    ∃ i : ι, ∃ s : ℕ → ℕ, StrictMono s ∧ (∀ n, label (s n) = i) ∧
      ∃ Θ : Cylinder → M,
        ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
        InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
        IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
        (let U : TopologicalSpace.Opens Cylinder :=
          ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
         IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
        Θ '' (univ ×ˢ Ici (0 : ℝ)) = ⋃ n, P (s n) '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
        Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ W 0 = range (sphere 0 i) ∩ W 0 ∧
        (∀ z, Θ (z, 0) = sphere 0 i z) ∧
        ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
          T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨i, s, hmono, hlabel, hbase, hs, hseam, hadj, hsep, hinitial⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_surviving_slab_sequence_of_finite_updates
      label hlabels sphere hunchanged P hsource μ hlower hupper W hW
        hcontained hinter hsphere hfilled
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  obtain ⟨Θ, hsm, hi, hp, he, hr, hb, _, hscalar⟩ :=
    exists_proper_neck_product_of_fresh_slabs g heps (fun n => point (s n)) (fun n => neck (s n))
      hcompact (fun n => P (s n)) (fun n => (μ (s n)).symm) hs hseam hadj hsep
      (fun n => hcontrolled (s n)) (fun n => hband (s n))
  refine ⟨i, s, hmono, hlabel, Θ, hsm, hi, hp, he, hr, ?_, ?_, hscalar⟩
  · rw [hr]
    exact hinitial
  intro z
  exact (hb z).trans (hbase z)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
