import DifferentialGeometry.Topology.Manifold.FiniteChartBalls
import DifferentialGeometry.Topology.Manifold.AffineCharts
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas








open Set Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology





theorem exists_finite_translated_chart_cover
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M]
    (e : V ≃L[ℝ] E) (R : ℝ) :
    ∃ t : Finset M, t.Nonempty ∧
      ∃ c : t → OpenPartialHomeomorph V M, ∃ K : t → Set V,
        (∀ i, ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (c i) (c i).source ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (c i).symm (c i).target ∧
          IsCompact (K i) ∧ K i ⊆ (c i).source) ∧
        ∃ j : M → t, ∃ b : M → V, ∀ p,
          c (j p) (b p) = p ∧
          MapsTo (fun y => b p + y) (Metric.closedBall (0 : V) R) (K (j p)) := by
  classical
  obtain ⟨r, hr, t, ht⟩ := exists_finite_chart_ball_cover (E := E) (M := M)
    (a := 3) (by norm_num)
  have htn : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := ht (Classical.arbitrary M)
    exact ⟨i, hi⟩
  let d : ℝ := t.inf' htn r
  have hd : 0 < d := (Finset.lt_inf'_iff _).mpr (fun i _ => (hr i).1)
  have hdr (i : M) (hi : i ∈ t) : d ≤ r i := Finset.inf'_le _ hi
  obtain ⟨δ, hδ, hδsmall⟩ := exists_pos_mul_lt hd (‖(e : V →L[ℝ] E)‖ * R)
  let L : V ≃L[ℝ] E := e.trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 δ hδ.ne'))
  have hL (y : V) : L y = δ • e y := rfl
  have hsmall (y : V) (hy : y ∈ Metric.closedBall (0 : V) R) : ‖L y‖ < d := by
    have hyn : ‖y‖ ≤ R := by simpa using hy
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc
      δ * ‖e y‖ ≤ δ * (‖(e : V →L[ℝ] E)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm y) hδ.le
      _ ≤ δ * (‖(e : V →L[ℝ] E)‖ * R) := by gcongr
      _ < d := by nlinarith
  let c : t → OpenPartialHomeomorph V M := fun i =>
    affineChart (chartAt E (i : M)).symm 0 L
  let K : t → Set V := fun i => L.symm ''
    Metric.closedBall (chartAt E (i : M) i) (2 * r i)
  have hK (i : t) : IsCompact (K i) :=
    (isCompact_closedBall _ _).image L.symm.continuous
  have hKs (i : t) : K i ⊆ (c i).source := by
    rintro x ⟨y, hy, rfl⟩
    have hyr : y ∈ (chartAt E (i : M)).target := (hr i).2
      (Metric.closedBall_subset_closedBall (by linarith [(hr i).1]) hy)
    simpa [c, affineChart_source] using hyr
  have hchoose (p : M) : ∃ i : t,
      p ∈ (chartAt E (i : M)).source ∧
        chartAt E (i : M) p ∈ Metric.ball (chartAt E (i : M) i) (r i) := by
    obtain ⟨i, hi, hp, hb⟩ := ht p
    exact ⟨⟨i, hi⟩, hp, hb⟩
  choose j hj hb using hchoose
  let b : M → V := fun p => L.symm (chartAt E (j p : M) p)
  refine ⟨t, htn, c, K, ?_, j, b, fun p => ?_⟩
  · intro i
    have hs := contMDiffOn_affineChart
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := (i : M)))
      (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := (i : M))) (0 : E) L
    exact ⟨hs.1, hs.2, hK i, hKs i⟩
  · constructor
    · simpa [c, b] using (chartAt E (j p : M)).left_inv (hj p)
    · intro y hy
      refine ⟨chartAt E (j p : M) p + L y, ?_, ?_⟩
      · rw [Metric.mem_closedBall]
        have hnear : dist (chartAt E (j p : M) p) (chartAt E (j p : M) (j p)) < r (j p) := hb p
        have hly := (hsmall y hy).trans_le (hdr _ (j p).property)
        calc
          _ ≤ dist (chartAt E (j p : M) p + L y) (chartAt E (j p : M) p) +
              dist (chartAt E (j p : M) p) (chartAt E (j p : M) (j p)) :=
            dist_triangle _ _ _
          _ = ‖L y‖ + dist (chartAt E (j p : M) p) (chartAt E (j p : M) (j p)) := by
            simp [dist_eq_norm]
          _ ≤ 2 * r (j p) := by linarith
      · simp [b, map_add]

end DifferentialGeometry.Topology
