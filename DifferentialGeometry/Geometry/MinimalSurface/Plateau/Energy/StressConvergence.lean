import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakPullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticConvergence
import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import DifferentialGeometry.Geometry.Metric.Pullback.Continuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Coordinates
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.StressCoordinates
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialStationarity

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem tendsto_integral_pullback_gradient_pair_of_disk_energy_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, ∃ L : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (L : ℝ≥0∞) * edist x y)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (henergy : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 ((∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) / 2)))
    (c : V → ℝ) (hcm : AEStronglyMeasurable c μ) {D : ℝ≥0}
    (hc : ∀ᵐ x ∂μ, |c x| ≤ D) (j k : Fin 2) :
    Tendsto (fun n => ∫ x in Metric.ball (0 : V) 1,
      c x * pullbackMetricCoefficients g r
        (Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        (fderiv ℝ (fun y => Φ (diskExtension (u n)
          (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single j 1))
        (fderiv ℝ (fun y => Φ (diskExtension (u n)
          (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single k 1))) atTop
      (𝓝 (∫ x in Metric.ball (0 : V) 1, c x * pullbackMetricCoefficients g r (w x)
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x k)))) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  let f : ℕ → V → F := fun n x => Φ (diskExtension (u n) (e x))
  let A := pullbackMetricCoefficients g r
  have hA : ContinuousOn A (range Φ) :=
    (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hN hr).mono hΦN
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂μ, w x ∈ range Φ := by
    filter_upwards [hae] with x hx
    exact hK.isClosed.mem_of_tendsto hx (Eventually.of_forall fun n => mem_range_self _)
  obtain ⟨CΦ, _, hCΦ⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le
    g hΦ
  choose L hL using hu
  have hf (n : ℕ) : LipschitzWith (CΦ * L n) (f n) := by
    have h := (hCΦ (diskExtension (u n)) (L n)
      (diskExtension_riemannian_lipschitz g (hL n))).1
    intro x y
    simpa only [f, Function.comp_apply, e.isometry.edist_eq] using! h (e x) (e y)
  have heq (n : ℕ) : (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
      A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) =
      2 * riemannianDiskEnergy g (u n) :=
    sum_integral_pullback_gradient_eq_two_mul_riemannianDiskEnergy
      g hΦ hN hr hΦN hleft (u n) (hL n)
  have hEt : Tendsto (fun n => ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
      A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        A (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)))) := by
    simpa only [heq, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using henergy.const_mul 2
  exact tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto
    measurableSet_ball f w hs hw (fun n => CΦ * L n) hf hrep hweak hK A hA
    (fun _ _ => pullbackMetricCoefficients_isPosSemidef g r _) (fun _ _ _ => mem_range_self _)
    hwK hae hEt c hcm hc j k

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem tendsto_radialDiskEnergyFirstVariation_to_weak_stress_of_energy_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, ∃ L : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (L : ℝ≥0∞) * edist x y)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (henergy : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 ((∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) / 2)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    Tendsto (fun n => radialDiskEnergyFirstVariation g (u n) ψ) atTop
      (𝓝 (∑ i : Fin 2, ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        radialDiskStressCoefficient ψ (Complex.orthonormalBasisOneI.repr.symm x) i j *
          pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun k => (hw k).weakGrad x i))
          (WithLp.toLp 2 (fun k => (hw k).weakGrad x j)))) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have ht (i j : Fin 2) := tendsto_integral_pullback_gradient_pair_of_disk_energy_tendsto
    g hΦ hN hr hΦN hleft u hu w hs hw hrep hweak hae henergy
    (fun x => radialDiskStressCoefficient ψ (e x) i j)
    (((measurable_radialDiskStressCoefficient ψ i j).comp e.continuous.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun x => norm_radialDiskStressCoefficient_le hψ (e x) i j) i j
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => ht i j
  have heq (n : ℕ) : radialDiskEnergyFirstVariation g (u n) ψ =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        radialDiskStressCoefficient ψ (e x) i j *
          pullbackMetricCoefficients g r (Φ (diskExtension (u n) (e x)))
            (fderiv ℝ (fun y => Φ (diskExtension (u n) (e y))) x (EuclideanSpace.single i 1))
            (fderiv ℝ (fun y => Φ (diskExtension (u n) (e y))) x (EuclideanSpace.single j 1)) := by
    obtain ⟨L, hL⟩ := hu n
    exact radialDiskEnergyFirstVariation_eq_sum_integral_pullback_of_lipschitz
      g hΦ hN hr hΦN hleft (u n) hL hψ
  exact hsum.congr' (Eventually.of_forall fun n => (heq n).symm)

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem tendsto_radialDiskEnergyFirstVariation_of_energy_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, ∃ L : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (L : ℝ≥0∞) * edist x y)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    (henergy : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (riemannianDiskEnergy g q)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    Tendsto (fun n => radialDiskEnergyFirstVariation g (u n) ψ) atTop
      (𝓝 (radialDiskEnergyFirstVariation g q ψ)) := by
  have he := (integrable_diskMapEnergyDensity_and_energy_eq_of_contDiffOn_representative
    g hN hr (isCompact_range hΦ.continuous) hΦN
    q w hw v hvc hvw hvK hq).2
  have hstress := radialDiskEnergyFirstVariation_eq_sum_integral_weak_pullback
    g hΦ hN hr hΦN hleft q w hw v hvc hvw hvK hq hψ
  rw [hstress]
  apply tendsto_radialDiskEnergyFirstVariation_to_weak_stress_of_energy_tendsto
    g hΦ hN hr hΦN hleft u hu w hs hw hrep hweak hae
  · rwa [← he]
  · exact hψ

theorem radialDiskEnergyFirstVariation_eq_zero_of_energy_attainment
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    (hattain : riemannianDiskEnergy g q =
      sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : Differentiable ℝ ψ)
    (hψLip : LipschitzWith C ψ) (hper : Function.Periodic ψ 1) :
    radialDiskEnergyFirstVariation g q ψ = 0 := by
  have henergy : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (riemannianDiskEnergy g q)) := by rwa [hattain]
  have htransfer := tendsto_radialDiskEnergyFirstVariation_of_energy_tendsto
    g hΦ hN hr hΦN hleft u (fun n => (hu n).2) w hs hw hrep hweak hae
    v hvc hvw hvK q hq henergy hψLip
  have horiginal := tendsto_radialDiskEnergyFirstVariation_of_minimizing_sequence
    g hu hmin hψ hψLip hper
  exact tendsto_nhds_unique htransfer horiginal

end DifferentialGeometry.Geometry

end
