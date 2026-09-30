import DifferentialGeometry.Geometry.Metric.Approximation.PointedPrecompactness
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Topology.MetricSpace.FiniteNets

namespace GC.MetricGeometry

open Set

universe u
variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)]

theorem exists_pointedGHConverges_of_eventual_packing (p : ∀ n, X n)
    (hpack : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∀ S : Finset (X n), (∀ x ∈ S, dist x (p n) ≤ R) →
        (S : Set (X n)).Pairwise (fun x y => η ≤ dist x y) → S.card ≤ N) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun n => p (φ n)) q := by
  apply exists_pointedGHConverges_of_eventual_finite_nets p
  intro R hR η hη
  obtain ⟨N, I, hNI⟩ := hpack R hR η hη
  refine ⟨N, I, fun n hn => ?_⟩
  obtain ⟨S, hS, hrad, hcover⟩ := Metric.exists_finset_net_card_le_of_packing
    (s := Metric.closedBall (p n) R) hη N (fun S hS hsep => hNI n hn S hS hsep)
  exact ⟨S, hS, hrad, fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact ⟨y, hy, hxy.le⟩⟩

theorem exists_geodesic_pointedGHConverges_of_eventual_packing (p : ∀ n, X n)
    (hpack : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∀ S : Finset (X n), (∀ x ∈ S, dist x (p n) ≤ R) →
        (S : Set (X n)).Pairwise (fun x y => η ≤ dist x y) → S.card ≤ N)
    (hcurves : ∀ n, ∀ a b : X n, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun n => p (φ n)) q ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_eventual_packing p hpack
  let := m
  let := hproper
  exact ⟨Y, m, q, φ, hφ, hproper, hconv,
    hconv.exists_metric_segment_of_source_curves (fun n => hcurves (φ n))⟩

end GC.MetricGeometry
