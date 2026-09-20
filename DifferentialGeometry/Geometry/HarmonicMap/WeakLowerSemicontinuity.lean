import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource

noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin m)
local notation "μ" => volume.restrict Ω

theorem exists_pullback_dirichlet_integral_le_liminf
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M → F) (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    (hΦemb : _root_.Topology.IsEmbedding Φ)
    (hΦimm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p))
    (u : ℕ → V → M) (w : V → M)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * edist x y)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => Φ (u n x) i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => Φ (w x) i) Ω)
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (u n y) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (w x))) :
    ∃ (r : F → M) (N : Set F), IsOpen N ∧ range Φ ⊆ N ∧
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N ∧ Function.LeftInverse r Φ ∧
      (∀ n j, IntegrableOn (fun x => g.inner (u n x)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))) Ω) ∧
      (∑ j : Fin d, ∫ x in Ω, pullbackMetricCoefficients g r (Φ (w x))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤
        liminf (fun n => ∑ j : Fin d, ∫ x in Ω,
          g.inner (u n x)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))) atTop := by
  let : Nonempty M := ⟨u 0 0⟩
  let : T2Space M := hΦemb.t2Space
  obtain ⟨r, N, hN, hΦN, hr, hleft, _, hBc, hpos, _, C, _, hC⟩ :=
    exists_bounded_pullback_metric_coefficients_of_embedding g hΦ hΦemb hΦimm
  choose K hK using hLip
  obtain ⟨L, _, hL⟩ := exists_riemannian_lipschitz_of_contMDiff g (hΦ.of_le (by simp))
  have hf (n : ℕ) : LipschitzWith (L * K n) (Φ ∘ u n) := by
    intro x y
    apply (hL (u n x) (u n y)).trans
    calc
      (L : ℝ≥0∞) * riemannianEDistOf g (u n x) (u n y) ≤
        (L : ℝ≥0∞) * ((K n : ℝ≥0∞) * edist x y) := by gcongr; exact hK n x y
      _ = (↑(L * K n) : ℝ≥0∞) * edist x y := by simp only [ENNReal.coe_mul, mul_assoc]
  let B : ℕ → V → F →L[ℝ] F →L[ℝ] ℝ :=
    fun n x => pullbackMetricCoefficients g r (Φ (u n x))
  let B₀ : V → F →L[ℝ] F →L[ℝ] ℝ :=
    fun x => pullbackMetricCoefficients g r (Φ (w x))
  have hBm (n : ℕ) : AEStronglyMeasurable (B n) μ :=
    (hBc.comp (continuous_of_riemannian_lipschitz g (hK n))).aestronglyMeasurable
  have hBC (n : ℕ) : ∀ᵐ x ∂μ, ‖B n x‖ ≤ C :=
    Filter.Eventually.of_forall fun x => hC (u n x)
  have hBlim : ∀ᵐ x ∂μ, Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)) :=
    hlim.mono fun x hx => (hBc.tendsto (w x)).comp hx
  have hBpos (n : ℕ) : ∀ᵐ x ∂μ, ∀ z, 0 ≤ B n x z z :=
    Filter.Eventually.of_forall fun x z => (hpos (Φ (u n x))).isNonneg.nonneg z
  have h :=
    Analysis.Sobolev.Euclidean.sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    (fun n => Φ ∘ u n) (Φ ∘ w) hs hv (fun n => L * K n) hf hrep hweak
    B B₀ hBm C hBC hBlim hBpos
  have heq (j : Fin d) (n : ℕ) :
      (∫ x in Ω, B n x (fderiv ℝ (Φ ∘ u n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (Φ ∘ u n) x (EuclideanSpace.single j 1))) =
      ∫ x in Ω, g.inner (u n x)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ω)
      (ae_mdifferentiableAt_of_metric_lipschitz g (hK n))] with x hx
    exact pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
      (hΦ.mdifferentiableAt (by simp))
      ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self (u n x))))).mdifferentiableAt
        (by simp)) hleft hx _ _
  obtain ⟨A, _, hA, _, _⟩ :=
    Analysis.Sobolev.Euclidean.exists_lp_gradient_columns_of_tendsto_inner
      (fun n => Φ ∘ u n) (Φ ∘ w) hs hv (fun n => L * K n) hf hrep hweak
  have hi (n : ℕ) (j : Fin d) : IntegrableOn (fun x => g.inner (u n x)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (u n) x (EuclideanSpace.single j 1))) Ω := by
    have hbil := integrable_bilinear_of_apply_aestronglyMeasurable (B n)
      (fun y z => ((hBm n).apply_continuousLinearMap y).apply_continuousLinearMap z)
      (hBC n) (Lp.memLp (A j n)) (Lp.memLp (A j n))
    refine Integrable.congr hbil ?_
    filter_upwards [hA j n, ae_restrict_of_ae (s := Ω)
      (ae_mdifferentiableAt_of_metric_lipschitz g (hK n))] with x hx hd
    rw [hx]
    exact pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
      (hΦ.mdifferentiableAt (by simp))
      ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self (u n x))))).mdifferentiableAt
        (by simp)) hleft hd _ _
  exact ⟨r, N, hN, hΦN, hr, hleft, hi, by simpa only [heq] using h⟩

end DifferentialGeometry.Geometry
