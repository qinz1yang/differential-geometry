import DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence

set_option autoImplicit false

/-!
# CH12-S85 / G2a: `Ric` and `g(V,V)` are continuous under `C²` metric-jet convergence at a point

Quantitative form (adapting `ricciTensor_nonnegative_of_local_metric_jet_convergence`): if
`metricDerivNorm a u G G q < δ` for `a ≤ 2`, then `|Ric_u(v,v) − Ric_G(v,v)| < ε'` and
`|u(v,v) − G(v,v)| < ε'`.  This turns the terminal `C^a` convergence of the flow metrics at an event
time into pointwise convergence of the vector defect.
-/

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace GC.LongTime.Ch12

section JetConv
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ricci_inner_close_of_jet_S85 (G : SmoothRiemannianMetric I M) (q : M)
    (v : TangentSpace I q) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ a : ℕ, a ≤ 2 → metricDerivNorm a u G G q < δ) →
      |ricciTensor u q v v - ricciTensor G q v v| < ε' ∧
        |u.inner q v v - G.inner q v v| < ε' := by
  classical
  let B : ℝ := (∑ a ∈ Finset.range 3, metricCovDerivNorm a G G q) + 1
  have hnorm (a : ℕ) : 0 ≤ metricCovDerivNorm a G G q := Real.sqrt_nonneg _
  have hB : 0 ≤ B := add_nonneg (Finset.sum_nonneg (fun a _ => hnorm a)) zero_le_one
  have hself (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a G G q ≤ B - 1 := by
    dsimp only [B]
    simp only [add_sub_cancel_right]
    exact Finset.single_le_sum (fun i _ => hnorm i)
      (Finset.mem_range.mpr (show a < 3 by omega))
  obtain ⟨C, hC, hRic⟩ := ricciSub_le_dNorm G q (1 / 2) B (by norm_num) hB v v
  have hGnn (w : TangentSpace I q) : 0 ≤ G.inner q w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (G.pos q w hw).le
  have hv1 : 0 < G.inner q v v + 1 := by linarith [hGnn v]
  let δ : ℝ := min (1 / 2) (min 1 (min (ε' / (6 * C)) (ε' / (G.inner q v v + 1))))
  have hδ : 0 < δ :=
    lt_min (by norm_num) (lt_min one_pos (lt_min (by positivity) (div_pos hε' hv1)))
  refine ⟨δ, hδ, fun u hu => ?_⟩
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ ε' / (6 * C) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδ4 : δ ≤ ε' / (G.inner q v v + 1) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsmall (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a u G G q ≤ δ := (hu a ha).le
  have hdiff (w : TangentSpace I q) :
      |u.inner q w w - G.inner q w w| ≤ δ * G.inner q w w := by
    have hd := metricDifference_abs_le u G G q w w
    rw [mul_assoc, Real.mul_self_sqrt (hGnn w)] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (hsmall 0 (by omega)) (hGnn w))
  have hlowu (w : TangentSpace I q) : (1 / 2) * G.inner q w w ≤ u.inner q w w := by
    have h1 := (abs_le.mp (hdiff w)).1
    nlinarith [hGnn w]
  have hlowG (w : TangentSpace I q) : (1 / 2) * G.inner q w w ≤ G.inner q w w := by
    nlinarith [hGnn w]
  have hbu (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a u G q ≤ B := by
    have hh := covNorm_le_add a u G G q
    have hs := hself a ha
    have he := (hsmall a ha).trans hδ2
    linarith
  have hbG (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a G G q ≤ B := by
    linarith [hself a ha]
  have hric := hRic u G hlowu hlowG hbu hbG
  have hsum : (∑ a ∈ Finset.range 3, metricDerivNorm a u G G q) ≤ 3 * δ := by
    calc _ ≤ ∑ _a ∈ Finset.range 3, δ := Finset.sum_le_sum (fun a ha =>
          hsmall a (by have := Finset.mem_range.mp ha; omega))
      _ = _ := by simp
  have hCδ : C * (3 * δ) ≤ ε' / 2 := by
    have h6 : δ * (6 * C) ≤ ε' := (le_div_iff₀ (by positivity : 0 < 6 * C)).mp hδ3
    nlinarith
  refine ⟨lt_of_le_of_lt (hric.trans (mul_le_mul_of_nonneg_left hsum hC.le)) (by linarith),
    lt_of_le_of_lt (hdiff v) ?_⟩
  have h4 : δ * (G.inner q v v + 1) ≤ ε' := (le_div_iff₀ hv1).mp hδ4
  have hpos : 0 < δ := hδ
  nlinarith [hGnn v]

end JetConv
end GC.LongTime.Ch12
