import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.VectorTimeComposition

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem exists_scalar_vectorH1_time_composition_on_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (n : ℕ)
    (F : (Option ι → ℝ) → ℝ) (G : (Option ι → ℝ) → (Fin n → ℝ))
    {U : Set (Option ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hU : IsOpen U) (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0, u0))) ⊆ U) :
    ∃ R : ℝ, 0 < R ∧ ∃ Cα CB : ℝ≥0,
      ∃ α : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R → TensorHs g 0 0 1,
      ∃ B : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R →
        PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1),
      LipschitzWith Cα (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => α p.1 p.2) ∧
      LipschitzWith CB (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => B p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R,
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0 + t, u0 + u))) ⊆ U) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x,
        scalarH1ToContinuous g (α t u) x = F (fun i => match i with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (u0 i + u.1 i) x)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x j,
        scalarH1ToContinuous g (B t u j) x = G (fun i => match i with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (u0 i + u.1 i) x) j := by
  obtain ⟨r, hr, Cα, α, hα, hRange, hαeval⟩ :=
    exists_scalarH1_time_composition_on_closedBall g F hF hU t0 u0 hu0
  obtain ⟨s, hs, CB, B, hB, _, hBeval⟩ :=
    exists_vectorH1_time_composition_on_closedBall g n G hG hU t0 u0 hu0
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R
  let inclα : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (min_le_left r s)) u.2⟩
  let inclB : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) s :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (min_le_right r s)) u.2⟩
  refine ⟨R, hR, Cα, CB, fun t u => α t (inclα u), fun t u => B t (inclB u), ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact hα.dist_le_mul (p.1, inclα p.2) (q.1, inclα q.2)
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact hB.dist_le_mul (p.1, inclB p.2) (q.1, inclB q.2)
  · intro t ht u hu
    exact hRange t ⟨ht.1, ht.2.trans (min_le_left r s)⟩ u
      ((Metric.closedBall_subset_closedBall (min_le_left r s)) hu)
  · intro t ht u x
    exact hαeval t ⟨ht.1, ht.2.trans (min_le_left r s)⟩ (inclα u) x
  · intro t ht u x j
    exact hBeval t ⟨ht.1, ht.2.trans (min_le_right r s)⟩ (inclB u) x j

end DifferentialGeometry.Analysis.Spectral
