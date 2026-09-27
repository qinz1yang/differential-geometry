import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.GluedSpatialJets
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gluedFamily_closed_regularity
    (G H : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (T τ : ℝ) (hT : 0 < T) (hτ : 0 < τ)
    (hzero : H 0 = G T)
    (hGjets :
      ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × E =>
            iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
          (Icc 0 T ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hHjets :
      ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × E =>
            iteratedFDeriv ℝ r (chartGramOnE (H p.1) x₀ i j) p.2)
          (Icc 0 τ ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hGright :
      ∀ t ∈ Ico 0 T, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G t) x v w) (Ici 0) t)
    (hGend :
      ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G T) x v w) (Icc 0 T) T)
    (hHinterior :
      ∀ t ∈ Ioo 0 τ, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivAt (fun s => (H s).inner x v w)
          (-2 * ricciTensor (H t) x v w) t) :
    let Q := gluedFamily G H T
    (∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r (chartGramOnE (Q p.1) x₀ i j) p.2)
        (Icc 0 (T + τ) ×ˢ
          interior (extChartAt 𝓘(ℝ, E) x₀).target)) ∧
    (∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (Q p.1) x₀ p.2 i j)
        (Icc 0 (T + τ) ×ˢ
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)) ∧
    (∀ t ∈ Icc 0 (T + τ),
      ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (Q s).inner x v w)
          (-2 * ricciTensor (Q t) x v w) (Icc 0 (T + τ)) t) ∧
    ∀ t ∈ Ico 0 (T + τ),
      ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (Q s).inner x v w)
          (-2 * ricciTensor (Q t) x v w) (Ici 0) t := by
  let Q := gluedFamily G H T
  have hHclosed :=
    (contMDiffOn_and_equation_Icc_of_spatial_jets
      H 0 τ hτ hHjets hHinterior).2
  have hHright :
      ∀ t ∈ Ico 0 τ,
        ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
          HasDerivWithinAt (fun s => (H s).inner x v w)
            (-2 * ricciTensor (H t) x v w) (Ici 0) t := by
    intro t ht x v w
    have hgerm : Icc (0 : ℝ) τ =ᶠ[𝓝 t] Ici 0 := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      exact propext
        ⟨fun h => h.1, fun h => ⟨h, (show s < τ from hs).le⟩⟩
    exact (hasDerivWithinAt_congr_set hgerm).mp
      (hHclosed t (Ico_subset_Icc_self ht) x v w)
  have hleftSlice (s : ℝ) (hs : s ≤ T) : Q s = G s := by
    change gluedFamily G H T s = G s
    rcases lt_or_eq_of_le hs with hlt | heq
    · exact gluedFamily_of_lt G H T hlt
    · rw [heq, gluedFamily_at_endpoint, hzero]
  have hleftGerm : Icc (0 : ℝ) T =ᶠ[𝓝 T] Iic T := by
    filter_upwards [Ioi_mem_nhds hT] with s hs
    exact propext
      ⟨fun h => h.2, fun h => ⟨(show 0 < s from hs).le, h⟩⟩
  have hcross :
      ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (Q s).inner x v w)
          (-2 * ricciTensor (Q T) x v w) (Iic T) T := by
    intro x v w
    have hleft :
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G T) x v w) (Iic T) T :=
      (hasDerivWithinAt_congr_set hleftGerm).mp (hGend x v w)
    rw [hleftSlice T le_rfl]
    apply hleft.congr
    · intro s hs
      rw [hleftSlice s hs]
    · rw [hleftSlice T le_rfl]
  have hQright :
      ∀ t ∈ Ico 0 (T + τ),
        ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
          HasDerivWithinAt (fun s => (Q s).inner x v w)
            (-2 * ricciTensor (Q t) x v w) (Ici 0) t :=
    gluedFamily_pde (I := 𝓘(ℝ, E)) G H
      (α := 0) (omega := T) (ε := τ) (T := τ)
      hT hτ le_rfl hGright hHright hcross
  have hQinterior :
      ∀ t ∈ Ioo 0 (T + τ),
        ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
          HasDerivAt (fun s => (Q s).inner x v w)
            (-2 * ricciTensor (Q t) x v w) t := by
    intro t ht x v w
    exact (hQright t ⟨ht.1.le, ht.2⟩ x v w).hasDerivAt
      (Ici_mem_nhds ht.1)
  have hQjets := gluedFamily_spatial_gram_jets
    G H T τ hT hτ hzero hGjets hHjets
  obtain ⟨hQgram, hQclosed⟩ :=
    contMDiffOn_and_equation_Icc_of_spatial_jets
      Q 0 (T + τ) (add_pos hT hτ) hQjets hQinterior
  exact ⟨hQjets, hQgram, hQclosed, hQright⟩

end DifferentialGeometry.PDE.RicciFlow
