import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity



noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]





theorem riemannianAreaDensity_metric_relative_error
    (g h : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgh : ∀ (x : M) (v : TangentSpace I x),
      |h.inner x v v - g.inner x v v| ≤ δ * g.inner x v v)
    (U : ℂ → M) (z : ℂ) :
    |riemannianAreaDensity h U z - riemannianAreaDensity g U z| ≤
      δ * riemannianAreaDensity g U z := by
  have hup := riemannianAreaDensity_metric_upper g h (by linarith : 0 < 1 + δ)
    (fun x v => by have hh := (abs_le.mp (hgh x v)).2; linarith) U z
  have hlo : (1 - δ) * riemannianAreaDensity g U z ≤ riemannianAreaDensity h U z := by
    by_cases hd : δ < 1
    · exact riemannianAreaDensity_metric_lower g h (by linarith : 0 < 1 - δ)
        (fun x v => by have hh := (abs_le.mp (hgh x v)).1; linarith) U z
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (riemannianAreaDensity_nonneg g U z)).trans
        (riemannianAreaDensity_nonneg h U z)
  rw [abs_le]
  constructor <;> linarith





theorem riemannianAreaDensity_metric_time_error
    (g : SmoothRiemannianMetric I M) {G : ℝ → SmoothRiemannianMetric I M}
    {T : Set ℝ} {m R K : ℝ} (hm : 0 < m) (hR : 0 < R) (hK : 0 ≤ K)
    (hlo : ∀ t ∈ T, ∀ (x : M) (v : TangentSpace I x), m * g.inner x v v ≤ (G t).inner x v v)
    (hhi : ∀ t ∈ T, ∀ (x : M) (v : TangentSpace I x), (G t).inner x v v ≤ R * g.inner x v v)
    (hLip : ∀ t ∈ T, ∀ s ∈ T, ∀ (x : M) (v : TangentSpace I x),
      |(G t).inner x v v - (G s).inner x v v| ≤ K * |t - s| * g.inner x v v)
    {t s : ℝ} (ht : t ∈ T) (hs : s ∈ T) (U : ℂ → M) (z : ℂ) :
    |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G s) U z| ≤
      (K * R / m * riemannianAreaDensity g U z) * |t - s| := by
  have hδ : 0 ≤ K * |t - s| / m := div_nonneg (mul_nonneg hK (abs_nonneg _)) hm.le
  have hb := riemannianAreaDensity_metric_relative_error (G s) (G t) hδ
    (fun x v => (hLip t ht s hs x v).trans (by
      have he := mul_le_mul_of_nonneg_left (hlo s hs x v) hδ
      have hcancel : K * |t - s| / m * (m * g.inner x v v) =
          K * |t - s| * g.inner x v v := by field_simp
      rw [hcancel] at he
      exact he)) U z
  have harea := riemannianAreaDensity_metric_upper g (G s) hR (hhi s hs) U z
  exact hb.trans ((mul_le_mul_of_nonneg_left harea hδ).trans_eq (by ring))

end DifferentialGeometry.Geometry
