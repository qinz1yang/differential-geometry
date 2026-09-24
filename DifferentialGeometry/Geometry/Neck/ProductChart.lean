import DifferentialGeometry.Topology.Manifold.ProductChartGluing
import DifferentialGeometry.Geometry.Neck.Spatial
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Surgery.Topology

theorem exists_global_product_chart_of_neck_slabs
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} (p : ℕ → M)
    (neck : ∀ n, SpatialNeck g eps (p n)) (D : ℕ → Set M)
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ n, (univ ×ˢ Icc (0 : ℝ) 1 : Set Cylinder) ⊆ (P n).source)
    (himage : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) = D n)
    (hbottom : ∀ n, P n '' (univ ×ˢ ({0} : Set ℝ)) = (neck n).map '' (univ ×ˢ ({0} : Set ℝ)))
    (htop : ∀ n, P n '' (univ ×ˢ ({1} : Set ℝ)) = (neck (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
    (hseam : ∀ n, ∃ V : Set Cylinder, IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (hadjacent : ∀ n, D n ∩ D (n + 1) = (neck (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n → Disjoint (D m) (D n)) :
    ∃ Q : PartialDiffeomorph IC I3 Cylinder M ∞,
      Q.source = univ ×ˢ Ioi (0 : ℝ) ∧
      Q.target = (⋃ n, D n) \ ((neck 0).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      IsOpen ((⋃ n, D n) \ ((neck 0).map '' (univ ×ˢ ({0} : Set ℝ)))) ∧
      (∀ p : Sphere 2, ∀ s : ℝ, 0 < s →
        Q (p, s) = P ⌊s⌋₊ (p, s - (⌊s⌋₊ : ℝ))) ∧
      ∀ n : ℕ, ∀ p : Sphere 2, ∀ t ∈ Icc (0 : ℝ) 1, 0 < (n : ℝ) + t →
        Q (p, (n : ℝ) + t) = P n (p, t) := by
  let : Nonempty (Sphere 2) := ⟨(neck 0).center⟩
  obtain ⟨Q, hQs, hQt, heq, hstrip⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_product_chart_of_compatible_slabs
      P hsource hseam
      (by intro n; rw [himage, himage, htop]; exact hadjacent n)
      (by intro m n hmn; rw [himage, himage]; exact hseparated m n hmn)
  have ht : Q.target = (⋃ n, D n) \ ((neck 0).map '' (univ ×ˢ ({0} : Set ℝ))) := by
    simpa only [himage, hbottom] using hQt
  refine ⟨Q, hQs, ht, ht ▸ Q.open_target, ?_, hstrip⟩
  intro p s hs
  exact heq (show (p, s) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ _, hs⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Surgery.Topology

theorem global_product_chart_tendsto_endpoint
    {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M]
    (endpoint : UniformSpace.Completion M) (t : ℕ → ℝ) (D : ℕ → Set M)
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (Q : PartialDiffeomorph IC I3 Cylinder M ∞)
    (B : ℝ) (ht : Tendsto t atTop (𝓝 0))
    (himage : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) = D n)
    (hbound : ∀ n, ∀ x ∈ D n, dist (x : UniformSpace.Completion M) endpoint < B * t (n + 1))
    (hformula : ∀ p : Sphere 2, ∀ s : ℝ, 0 < s →
      Q (p, s) = P ⌊s⌋₊ (p, s - (⌊s⌋₊ : ℝ))) :
    ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ p : Sphere 2, ∀ s : ℝ, (N : ℝ) + 1 ≤ s →
      dist (Q (p, s) : UniformSpace.Completion M) endpoint < delta := by
  intro delta hdelta
  have hbt : Tendsto (fun n => B * t n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul B
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbt.eventually_lt_const hdelta)
  refine ⟨N, ?_⟩
  intro p s hs
  have hspos : 0 < s := by have hh := Nat.cast_nonneg (α := ℝ) N; linarith
  let n := ⌊s⌋₊
  have hNs : (N : ℝ) ≤ s := by linarith
  have hNn : N ≤ n := Nat.le_floor hNs
  have hsrc : (p, s - (n : ℝ)) ∈ univ ×ˢ Icc (0 : ℝ) 1 :=
    ⟨mem_univ _, sub_nonneg.mpr (Nat.floor_le hspos.le), by linarith [Nat.lt_floor_add_one s]⟩
  have hmem : Q (p, s) ∈ D n := by
    rw [hformula p s hspos, ← himage n]
    exact mem_image_of_mem _ hsrc
  have hupper := hbound n _ hmem
  have hnN := hN (n + 1) (hNn.trans (Nat.le_succ n))
  exact hupper.trans hnN

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
