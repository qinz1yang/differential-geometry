import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousRegularityBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousEuclideanCoordinates
import DifferentialGeometry.Geometry.Metric.SourceCoefficients

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def homogeneousCoordinates_of_homogeneouslyRegularMetric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : HomogeneouslyRegularMetric g) :
    HomogeneousCoordinates (I := 𝓘(ℝ, E)) (Q := M) g 3 := by
  classical
  choose m A hm hmA ψ hψ hC using h
  let atPoint : M → CubeChart (I := 𝓘(ℝ, E)) (Q := M) 3 := fun p =>
    { chart := ψ p
      closedCube_subset_source := (hψ p).1
      smooth := (hψ p).2.2.1
      smooth_inverse := (hψ p).2.2.2.1 }
  refine ⟨atPoint, fun p => (hψ p).2.1, m, A, hm, hmA, ?_, ?_⟩
  · intro p y hy v
    exact (hψ p).2.2.2.2 y hy v
  · intro k
    obtain ⟨C, hC0, hCl⟩ := hC k
    refine ⟨C, hC0, fun p y hy i j => ?_⟩
    have hpair := contDiffOn_sourceMetricPairing g (ψ p).open_source (hψ p).2.2.1
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    have hcontF : ContinuousOn (iteratedFDeriv ℝ k (plateauChartCoefficient g (ψ p) i j))
        (ψ p).source :=
      ContinuousOn.continuousOn_iteratedFDeriv hpair (ψ p).open_source
        (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hcont : ContinuousOn (fun x : plateauCoordinateSpace =>
        ‖iteratedFDeriv ℝ k (plateauChartCoefficient g (ψ p) i j) x‖) (ψ p).source :=
      continuous_norm.comp_continuousOn hcontF
    have hcontAt : ContinuousAt (fun x : plateauCoordinateSpace =>
        ‖iteratedFDeriv ℝ k (plateauChartCoefficient g (ψ p) i j) x‖) y :=
      hcont.continuousAt ((ψ p).open_source.mem_nhds ((hψ p).1 hy))
    have hone : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (𝓝 (0 : ℝ)) := by
      have h : (fun n : ℕ => (((n : ℝ) + 1))⁻¹) = fun n : ℕ => 1 / (((n : ℝ) + 1)) := by
        funext n
        rw [one_div]
      rw [h]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hden : Tendsto (fun n : ℕ => (((n : ℝ) + 2))⁻¹) atTop (𝓝 (0 : ℝ)) := by
      have hshift := hone.comp (tendsto_add_atTop_nat 1)
      have harg : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
        intro n
        push_cast
        ring
      have hfun : (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1)⁻¹) =
          fun n : ℕ => (((n : ℝ) + 2))⁻¹ := by
        funext n
        rw [harg n]
      have hshift' : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1)⁻¹) atTop
          (𝓝 (0 : ℝ)) :=
        hshift
      rwa [hfun] at hshift'
    have hscale : Tendsto (fun n : ℕ => (1 : ℝ) - (((n : ℝ) + 2))⁻¹) atTop
        (𝓝 (1 - 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hden
    have hscalelim : Tendsto (fun n : ℕ => (1 : ℝ) - (((n : ℝ) + 2))⁻¹) atTop
        (𝓝 1) := by
      simpa using hscale
    have hseq : Tendsto (fun n : ℕ =>
        (1 - (((n : ℝ) + 2))⁻¹ : ℝ) • y) atTop (𝓝 ((1 : ℝ) • y)) :=
      hscalelim.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
    have hseqy : Tendsto (fun n : ℕ =>
        (1 - (((n : ℝ) + 2))⁻¹ : ℝ) • y) atTop (𝓝 y) := by
      simpa using hseq
    have hmem : ∀ n : ℕ, (1 - (((n : ℝ) + 2))⁻¹ : ℝ) • y ∈ plateauOpenCube := by
      intro n i
      have hb : (0 : ℝ) < (((n : ℝ) + 2))⁻¹ := by positivity
      have hlt : (1 : ℝ) - (((n : ℝ) + 2))⁻¹ < 1 := sub_lt_self 1 hb
      have hcpos : (0 : ℝ) < 1 - (((n : ℝ) + 2))⁻¹ := by
        have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact sub_pos.mpr (inv_lt_one_of_one_lt₀ h2)
      have hcoord : ((1 - (((n : ℝ) + 2))⁻¹ : ℝ) • y) i =
          (1 - (((n : ℝ) + 2))⁻¹ : ℝ) * y i := by simp
      rw [hcoord, abs_mul, abs_of_pos hcpos]
      calc (1 - (((n : ℝ) + 2))⁻¹) * |y i|
          ≤ (1 - (((n : ℝ) + 2))⁻¹) * 1 :=
            mul_le_mul_of_nonneg_left (hy i) hcpos.le
        _ = 1 - (((n : ℝ) + 2))⁻¹ := by ring
        _ < 1 := hlt
    have hlim := hcontAt.tendsto.comp hseqy
    refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds
      (Eventually.of_forall fun n => hCl p i j _ (hmem n))

theorem nonempty_homogeneousCoordinates_of_euclideanMetric :
    Nonempty (HomogeneousCoordinates (I := 𝓘(ℝ, plateauCoordinateSpace))
      (Q := plateauCoordinateSpace) (euclideanMetric plateauCoordinateSpace) 3) :=
  ⟨homogeneousCoordinates_of_homogeneouslyRegularMetric (euclideanMetric plateauCoordinateSpace)
    homogeneouslyRegularMetric_euclideanMetric⟩

end DifferentialGeometry.Geometry
