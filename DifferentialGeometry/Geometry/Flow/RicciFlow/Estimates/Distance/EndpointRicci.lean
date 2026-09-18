import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.MovingSlope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.DiniComparison

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval}

theorem upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds_of_two_le_finrank
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) {T t B vx vy : ℝ}
    (ht : 0 < t) (hB : 0 < B) (hreg : T - t ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric (T - t)))
    (x y : ℝ → M) (hx : ContMDiffAt 𝓘(ℝ, ℝ) I 1 x t)
    (hy : ContMDiffAt 𝓘(ℝ, ℝ) I 1 y t)
    (hspeedx : Real.sqrt ((S.base.metric (T - t)).inner (x t)
      (mfderiv 𝓘(ℝ, ℝ) I x t 1) (mfderiv 𝓘(ℝ, ℝ) I x t 1)) ≤ vx)
    (hspeedy : Real.sqrt ((S.base.metric (T - t)).inner (y t)
      (mfderiv 𝓘(ℝ, ℝ) I y t 1) (mfderiv 𝓘(ℝ, ℝ) I y t 1)) ≤ vy)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (S.base.metric (T - t)) (x t) z <
          ENNReal.ofReal (Real.sqrt t / B) ∨
        riemannianEDistOf (S.base.metric (T - t)) (y t) z <
          ENNReal.ofReal (Real.sqrt t / B)) →
      ricciTensor (S.base.metric (T - t)) z w w ≤
        3 * B ^ 2 / t * (S.base.metric (T - t)).inner z w w) :
    UpperRightDiniLE
      (fun s => (riemannianEDistOf (S.base.metric (T - s)) (x s) (y s)).toReal)
      t (2 * ((Module.finrank ℝ E : ℝ) + 1) * B / Real.sqrt t + vx + vy) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let K := 3 * B ^ 2 / (((Module.finrank ℝ E : ℝ) - 1) * t)
  let r := Real.sqrt t / B
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr ht) hB
  have hdim' : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
  have hn : 0 < (Module.finrank ℝ E : ℝ) - 1 := by linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hRic' : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (S.base.metric (T - t)) (x t) z < ENNReal.ofReal r ∨
        riemannianEDistOf (S.base.metric (T - t)) (y t) z < ENNReal.ofReal r) →
      ricciTensor (S.base.metric (T - t)) z w w ≤
        ((Module.finrank ℝ E : ℝ) - 1) * K * (S.base.metric (T - t)).inner z w w := by
    intro z w hw
    have hh := hRic z w hw
    convert hh using 1
    dsimp only [K]
    field_simp [hn.ne', ht.ne']
  have hroot : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hrootne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hKmul : ((Module.finrank ℝ E : ℝ) - 1) * K * r =
      3 * B / Real.sqrt t := by
    dsimp only [K, r]
    field_simp [hn.ne', ht.ne', hB.ne', hrootne]
    exact hroot
  have hinvr : 1 / r = B / Real.sqrt t := by
    dsimp only [r]
    field_simp
  have hlongcoef : 2 * ((Module.finrank ℝ E : ℝ) - 1) *
      ((2 / 3 : ℝ) * K * r + 1 / r) =
        2 * ((Module.finrank ℝ E : ℝ) + 1) * B / Real.sqrt t := by
    calc
      _ = (4 / 3 : ℝ) * (((Module.finrank ℝ E : ℝ) - 1) * K * r) +
          2 * ((Module.finrank ℝ E : ℝ) - 1) * (1 / r) := by ring
      _ = _ := by rw [hKmul, hinvr]; ring
  have hshortcoef : 2 * ((Module.finrank ℝ E : ℝ) - 1) * K * r ≤
      2 * ((Module.finrank ℝ E : ℝ) + 1) * B / Real.sqrt t := by
    calc
      _ = 6 * B / Real.sqrt t := by rw [mul_assoc 2, mul_assoc 2, hKmul]; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg t)
        nlinarith only [hdim', hB]
  intro ε hε
  by_cases hshort : (riemannianEDistOf (S.base.metric (T - t)) (x t) (y t)).toReal < 2 * r
  · filter_upwards [eventually_slope_riemannianEDistOf_lt_of_lt_two_mul S hS hreg
      hcomplete hK hr x y hx hy hshort hRic' ε hε] with s hs
    exact hs.le.trans (add_le_add (add_le_add (add_le_add hshortcoef hspeedx) hspeedy) le_rfl)
  · filter_upwards [eventually_slope_riemannianEDistOf_lt_of_two_mul_le S hS hreg
      hcomplete hr x y hx hy (le_of_not_gt hshort) hRic' ε hε] with s hs
    rw [hlongcoef] at hs
    exact hs.le.trans (add_le_add (add_le_add (add_le_add le_rfl hspeedx) hspeedy) le_rfl)

theorem upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T t B vx vy : ℝ}
    (ht : 0 < t) (hB : 0 < B) (hreg : T - t ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric (T - t)))
    (x y : ℝ → M) (hx : ContMDiffAt 𝓘(ℝ, ℝ) I 1 x t)
    (hy : ContMDiffAt 𝓘(ℝ, ℝ) I 1 y t)
    (hspeedx : Real.sqrt ((S.base.metric (T - t)).inner (x t)
      (mfderiv 𝓘(ℝ, ℝ) I x t 1) (mfderiv 𝓘(ℝ, ℝ) I x t 1)) ≤ vx)
    (hspeedy : Real.sqrt ((S.base.metric (T - t)).inner (y t)
      (mfderiv 𝓘(ℝ, ℝ) I y t 1) (mfderiv 𝓘(ℝ, ℝ) I y t 1)) ≤ vy)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (S.base.metric (T - t)) (x t) z <
          ENNReal.ofReal (Real.sqrt t / B) ∨
        riemannianEDistOf (S.base.metric (T - t)) (y t) z <
          ENNReal.ofReal (Real.sqrt t / B)) →
      ricciTensor (S.base.metric (T - t)) z w w ≤
        3 * B ^ 2 / t * (S.base.metric (T - t)).inner z w w) :
    UpperRightDiniLE
      (fun s => (riemannianEDistOf (S.base.metric (T - s)) (x s) (y s)).toReal)
      t (8 * B / Real.sqrt t + vx + vy) := by
  have hdim' : 2 ≤ Module.finrank ℝ E := by omega
  simpa only [hdim, Nat.cast_ofNat, show (2 : ℝ) * (3 + 1) = 8 by norm_num] using
    upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds_of_two_le_finrank
      S hS hdim' ht hB hreg hcomplete x y hx hy hspeedx hspeedy hRic

end DifferentialGeometry.PDE.RicciFlow
