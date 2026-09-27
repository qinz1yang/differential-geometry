import DifferentialGeometry.Tensor.LinearAlgebra.PositivePlanarLinearMap
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactComplexMultiplication
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactTriangularGerm

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_compact_isotopy_realizing_positive_linear_map
    (A : ℂ →ₗ[ℝ] ℂ) (hA : 0 < A.det) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] A ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  obtain ⟨a, ha, s, b, hb, hfactor⟩ := exists_positive_triangular_decomposition A hA
  obtain ⟨S, hS, hSi, hS0, hSg, hSfix⟩ := exists_compact_isotopy_realizing_shear s r hr
  obtain ⟨V, hV, hVi, hV0, hVg, hVfix⟩ :=
    exists_compact_isotopy_realizing_vertical_scale b hb r hr
  obtain ⟨M, hM, hMi, hM0, hMg, hMfix⟩ := exists_compact_isotopy_realizing_complex_mul a ha r hr
  let D (p : ℝ) := ((S p).trans (V p)).trans (M p)
  have hD : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) :=
    hM.comp (contDiff_fst.prodMk (hV.comp (contDiff_fst.prodMk hS)))
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) :=
    hSi.comp (contDiff_fst.prodMk (hVi.comp (contDiff_fst.prodMk hMi)))
  have hSzero : S 1 0 = 0 := by simpa using hSg.eq_of_nhds
  have hVzero : V 1 0 = 0 := by simpa using hVg.eq_of_nhds
  have htS : Tendsto (S 1) (𝓝 0) (𝓝 0) := by
    simpa only [hSzero] using (S 1).continuous.tendsto 0
  have htV : Tendsto (V 1) (𝓝 0) (𝓝 0) := by
    simpa only [hVzero] using (V 1).continuous.tendsto 0
  have htVS : Tendsto (fun z ↦ V 1 (S 1 z)) (𝓝 0) (𝓝 0) := htV.comp htS
  refine ⟨D, hD, hDi, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro z
    change M 0 (V 0 (S 0 z)) = z
    rw [hM0, hV0, hS0]
    rfl
  · filter_upwards [hSg, hVg.comp_tendsto htS, hMg.comp_tendsto htVS] with z hs hv hm
    change S 1 z = z + (s * z.im : ℝ) at hs
    change V 1 (S 1 z) = ((S 1 z).re : ℂ) + (b * (S 1 z).im) • Complex.I at hv
    change M 1 (V 1 (S 1 z)) = a * V 1 (S 1 z) at hm
    change M 1 (V 1 (S 1 z)) = A z
    rw [hm, hv, hs]
    exact (hfactor z).symm
  · intro p z hz
    constructor
    · change M p (V p (S p z)) = z
      rw [(hSfix p z hz).1, (hVfix p z hz).1, (hMfix p z hz).1]
    · change (S p).symm ((V p).symm ((M p).symm z)) = z
      rw [(hMfix p z hz).2, (hVfix p z hz).2, (hSfix p z hz).2]

end DifferentialGeometry.Analysis
