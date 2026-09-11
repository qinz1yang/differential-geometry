import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.GrowingInitialCylinderCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Filter Function TopologicalSpace Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem standard_uniform_initial_cylinder_charts (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 0 < D ∧ ∀ S : DifferentialGeometry.PDE.RicciFlow.StandardSolution, ∀ x : E3,
      D ≤ (riemannianEDistOf (S.val.metric 0) 0 x).toReal →
      ∃ hfit : transitionEnd + (A + 1) ≤ ‖x‖,
        (initialCylinderChart (pointedInitialRotation x) ‖x‖ (A + 1) hfit
          ⟨(spherePoint, 0), by constructor <;> linarith⟩ : E3) = x ∧
        Diffeomorph.pullbackMetricCross
          ((S.val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation x) ‖x‖ (A + 1) hfit))
          (initialCylinderChart (pointedInitialRotation x) ‖x‖ (A + 1) hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder (A + 1)) := by
  refine ⟨transitionEnd + A + 2, by linarith [transitionEnd_pos], ?_⟩
  intro S x hx
  rw [S.val.initial, distance_zero] at hx
  have hfit : transitionEnd + (A + 1) ≤ ‖x‖ := by linarith
  refine ⟨hfit, initialCylinderChart_center x (A + 1) (by linarith) hfit, ?_⟩
  rw [S.val.initial]
  exact initialCylinderChart_pullback _ _ _ _

theorem escaping_initial_centers_exhaust
    (S : ℕ → DifferentialGeometry.PDE.RicciFlow.StandardSolution) (x : ℕ → E3)
    (hescape : Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
      atTop atTop) {K : Set (S2 × ℝ)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ (openCylinder L : Set (S2 × ℝ)) ∧
      ∀ᶠ i in atTop, ∃ hfit : transitionEnd + L ≤ ‖x i‖,
        Diffeomorph.pullbackMetricCross
          (((S i).val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation (x i)) ‖x i‖ L hfit))
          (initialCylinderChart (pointedInitialRotation (x i)) ‖x i‖ L hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L) := by
  obtain ⟨L, hL, hKL⟩ := compact_subset_openCylinder hK
  refine ⟨L, hL, hKL, ?_⟩
  filter_upwards [hescape.eventually_ge_atTop (transitionEnd + L)] with i hi
  rw [(S i).val.initial, distance_zero] at hi
  refine ⟨hi, ?_⟩
  rw [(S i).val.initial]
  exact initialCylinderChart_pullback _ _ _ _

theorem escaping_initial_centers_growing_subsequence
    (S : ℕ → DifferentialGeometry.PDE.RicciFlow.StandardSolution) (x : ℕ → E3)
    (hescape : Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
      atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ,
      ∃ hfit : transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖,
        (initialCylinderChart (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
          ((k : ℝ) + 1) hfit
          ⟨(spherePoint, 0), by
            change -((k : ℝ) + 1) < 0 ∧ (0 : ℝ) < (k : ℝ) + 1
            have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
            exact ⟨neg_neg_of_pos hk, hk⟩⟩ : E3) = x (φ k) ∧
        Diffeomorph.pullbackMetricCross
          (((S (φ k)).val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
              ((k : ℝ) + 1) hfit))
          (initialCylinderChart (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
            ((k : ℝ) + 1) hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen
            (openCylinder ((k : ℝ) + 1)) := by
  classical
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ i ≥ N,
      transitionEnd + ((k : ℝ) + 1) ≤ ‖x i‖ := by
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hescape.eventually_ge_atTop (transitionEnd + ((k : ℝ) + 1)))
    refine ⟨N, fun i hi => ?_⟩
    have h := hN i hi
    rwa [(S i).val.initial, distance_zero] at h
  choose N hN using hN
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun k prev => max (prev + 1) (N (k + 1)))
  have hstep (k : ℕ) : φ k < φ (k + 1) := by
    change φ k < max (φ k + 1) (N (k + 1))
    exact (Nat.lt_succ_self (φ k)).trans_le (le_max_left _ _)
  have hNφ (k : ℕ) : N k ≤ φ k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  refine ⟨φ, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro k
  have hfit := hN k (φ k) (hNφ k)
  refine ⟨hfit, initialCylinderChart_center _ _ (by positivity) hfit, ?_⟩
  rw [(S (φ k)).val.initial]
  exact initialCylinderChart_pullback _ _ _ _

end DifferentialGeometry.PDE.RicciFlow

end
