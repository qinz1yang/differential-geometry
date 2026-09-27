import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import DifferentialGeometry.Geometry.Metric.Family.TimeGluing

set_option autoImplicit false

noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_openClosed_solution_of_compatible_open_cover {T : ℝ} (hT : 0 < T)
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcmono : Monotone c) (hcT : ∀ s < T, ∃ n, s < c n)
    (g : ∀ n, ℝ → SmoothRiemannianMetric I (U n))
    (hg : ∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
      (RealTimeInterval.closed (-c n) 0 (neg_nonpos.mpr (hc n)))))
    (hcompat : ∀ n m, ∀ t ∈ Icc (-c n) 0, t ∈ Icc (-c m) 0 →
      (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
        (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) ∧
      ∀ n t, t ∈ Icc (-c n) 0 → (G t).restrictOpen (U n) = g n t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨G, hG⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_metric_family_of_compatible_open_covers U
      (fun n => Icc (-c n) 0) {t | ∃ n, t ∈ Icc (-c n) 0} ⟨0, 0, ⟨neg_nonpos.mpr (hc 0), le_rfl⟩⟩
      g (by
        rintro t ⟨m, hm⟩ x
        obtain ⟨k, hk⟩ := hcover x
        exact ⟨max m k, ⟨(neg_le_neg (hcmono (le_max_left m k))).trans hm.1, hm.2⟩,
          hU (le_max_right m k) hk⟩)
      (fun n m t _ hn hm => hcompat n m t hn hm)
  refine ⟨G, ?_, fun n t ht => hG n t ⟨n, ht⟩ ht⟩
  apply isSolutionOn_of_local_time_restrictions
  intro t ht
  obtain ⟨n, hn⟩ := hcT (-t) (by linarith [ht.1])
  refine ⟨Ioi (-c n), isOpen_Ioi, mem_Ioi.mpr (by linarith), RealTimeInterval.closed (-c n) 0
    (neg_nonpos.mpr (hc n)), fun s hs => ⟨hs.2.le, hs.1.2⟩, fun s hs => ⟨hs.2, hs.1.2⟩, ?_⟩
  apply isSolutionOn_of_open_cover G (fun k => U (n + k))
    (fun x => by
      obtain ⟨k, hk⟩ := hcover x
      exact ⟨k, hU (Nat.le_add_left _ _) hk⟩)
  intro k
  have hcar : Icc (-c n) 0 ⊆ Icc (-c (n + k)) 0 := fun s hs =>
    ⟨(neg_le_neg (hcmono (Nat.le_add_right n k))).trans hs.1, hs.2⟩
  have hreg : Ioo (-c n) 0 ⊆ Ioo (-c (n + k)) 0 := fun s hs =>
    ⟨(neg_le_neg (hcmono (Nat.le_add_right n k))).trans_lt hs.1, hs.2⟩
  have hlocal := isSolutionOn_timeRestrict (hg (n + k))
    (D' := RealTimeInterval.closed (-c n) 0 (neg_nonpos.mpr (hc n))) hcar hreg
  exact hlocal.congr_metric (fun s hs => (hG (n + k) s ⟨n + k, hcar hs⟩ (hcar hs)).symm)

theorem exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule {T : ℝ}
    (hT : 0 < T) (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    (g : ∀ n, ℝ → SmoothRiemannianMetric I (U n))
    (hg : ∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
      (RealTimeInterval.closed
        (-(((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) * (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))))
        0 (neg_nonpos.mpr (by positivity)))))
    (hcompat : ∀ n m,
      ∀ t ∈ Icc (-(((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) *
        (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)))) 0,
      t ∈ Icc (-(((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) *
        (T * ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)))) 0 →
      (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
        (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) ∧
      ∀ n t, t ∈ Icc (-(((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) *
        (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)))) 0 → (G t).restrictOpen (U n) = g n t := by
  have hβ (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) = 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    field_simp
    push_cast
    ring
  refine exists_openClosed_solution_of_compatible_open_cover hT U hU hcover _
    (fun n => by positivity) (fun n m hnm => ?_) (fun s hs => ?_) g hg hcompat
  · have h1 : 1 / ((m + 2 : ℕ) : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 2)
    have h3 : 0 ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
      rw [← hβ]
      positivity
    have h4 : 1 - 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by linarith
    rw [mul_div_assoc, mul_div_assoc, hβ, hβ]
    exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h4 hT.le) (mul_nonneg hT.le h3) (h3.trans h4)
  · obtain ⟨n, hn⟩ := exists_nat_gt (2 * T / (T - s))
    refine ⟨n, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hn2 : 2 * T / (T - s) < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hx : 2 * T * (1 / ((n + 2 : ℕ) : ℝ)) < T - s := by
      rw [div_lt_iff₀ hTs] at hn2
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc, hβ]
    nlinarith [mul_nonneg hT.le (sq_nonneg (1 / ((n + 2 : ℕ) : ℝ)))]

end DifferentialGeometry.PDE.RicciFlow

end
