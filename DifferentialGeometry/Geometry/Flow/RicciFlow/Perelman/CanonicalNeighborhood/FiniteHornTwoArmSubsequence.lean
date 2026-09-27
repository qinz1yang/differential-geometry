import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornArmSubsequence

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_two_arm_subsequence_eq_endRay
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ (a : Fin 2 → EndRay H.endpoint) (r : Fin 2 → ℝ),
      (∀ k, 0 < r k) → (∀ k, r k < min (a k).length d) → ∀ i : ℕ,
      ∀ (length : Fin 2 → ℕ → ℝ) (c : Fin 2 → ℕ → Icc (0 : ℝ) 1 → W),
        (∀ k n, 0 ≤ length k n) → (∀ k, Tendsto (length k) atTop (𝓝 (r k))) →
        (∀ k n s, c k n s ∈ H.subend i) →
        (∀ k n s t, dist (c k n s) (c k n t) = length k n * dist s t) →
        (∀ k, Tendsto (fun n => (c k n ⟨0, by norm_num⟩ : UniformSpace.Completion W))
          atTop (𝓝 H.endpoint)) →
        (∀ k n, c k n ⟨1, by norm_num⟩ = (a k).point (r k)) →
        ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ k,
          TendstoUniformly (fun n s => (c k (phi n) s : UniformSpace.Completion W))
            (fun s : Icc (0 : ℝ) 1 => if (s : ℝ) = 0 then H.endpoint
              else ((a k).point (r k * s) : UniformSpace.Completion W)) atTop := by
  obtain ⟨d, hd, hsub⟩ := finiteHorn_arm_subsequence_eq_endRay g H
  refine ⟨d, hd, ?_⟩
  intro a r hr hrd i length c hlength hlengthT hmem hdist hbase hend
  obtain ⟨phi, hphi, hfirst⟩ := hsub (a 0) (r 0) (hr 0) (hrd 0) i
    (length 0) (c 0) (hlength 0) (hlengthT 0) (hmem 0) (hdist 0) (hbase 0) (hend 0)
  obtain ⟨psi, hpsi, hsecond⟩ := hsub (a 1) (r 1) (hr 1) (hrd 1) i
    (fun n => length 1 (phi n)) (fun n s => c 1 (phi n) s)
    (fun n => hlength 1 (phi n)) ((hlengthT 1).comp hphi.tendsto_atTop)
    (fun n s => hmem 1 (phi n) s) (fun n s t => hdist 1 (phi n) s t)
    ((hbase 1).comp hphi.tendsto_atTop) (fun n => hend 1 (phi n))
  refine ⟨phi ∘ psi, hphi.comp hpsi, ?_⟩
  intro k
  fin_cases k
  · exact (tendstoUniformly_iff_seq_tendstoUniformly.mp hfirst) psi hpsi.tendsto_atTop
  · exact hsecond

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
