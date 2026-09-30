import DifferentialGeometry.Geometry.Metric.Approximation.NormedProductBlowdown
import DifferentialGeometry.Geometry.Metric.Approximation.ConvergenceIsometry
import DifferentialGeometry.Geometry.Metric.Approximation.PointedIsometry
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleIsometry

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {X E F C : Type*} [mX : MetricSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace F] [MetricSpace C]

theorem pointedGHConverges_rescaled_of_normed_product [CompleteSpace E]
    (e : X ≃ᵢ WithLp 2 (E × F)) (p : X)
    (hF : Bornology.IsBounded (univ : Set F))
    {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hlim : Tendsto c atTop (𝓝 0)) :
    @PointedGHConverges (fun _ : ℕ => X)
      (fun n => mX.rescale (c n) (hc n)) E _ (fun _ => p) 0 := by
  have hprod := pointedGHConverges_rescaled_normed_product (e p).fst (e p).snd hF hc hlim
  apply @PointedGHConverges.comap_source_isometry
    (fun _ : ℕ => WithLp 2 (E × F)) (fun _ : ℕ => X) E
    (fun n => (inferInstance : MetricSpace (WithLp 2 (E × F))).rescale (c n) (hc n))
    (fun n => mX.rescale (c n) (hc n)) _
    (fun _ => WithLp.toLp 2 ((e p).fst, (e p).snd)) (fun _ => p) 0 hprod
    (fun n => e.rescale (c n) (hc n))
  intro n
  change e p = WithLp.toLp 2 ((e p).fst, (e p).snd)
  exact (WithLp.equiv 2 _).injective (Prod.ext rfl rfl)

theorem PointedGHConverges.exists_isometryEquiv_of_rescaled_normed_product
    [ProperSpace E] [ProperSpace C]
    {p : X} {q : C} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hlim : Tendsto c atTop (𝓝 0))
    (h : @PointedGHConverges (fun _ : ℕ => X)
      (fun n => mX.rescale (c n) (hc n)) C _ (fun _ => p) q)
    (e : X ≃ᵢ WithLp 2 (E × F)) (hF : Bornology.IsBounded (univ : Set F)) :
    ∃ f : C ≃ᵢ E, f q = 0 := by
  exact @PointedGHConverges.exists_isometryEquiv C E _ _ _ _ q 0
    (fun _ : ℕ => X) (fun n => mX.rescale (c n) (hc n)) (fun _ => p)
    h (pointedGHConverges_rescaled_of_normed_product e p hF hc hlim)

end GC.MetricGeometry
