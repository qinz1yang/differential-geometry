import DifferentialGeometry.Geometry.HarmonicMap.WeakLowerSemicontinuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Coordinates
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin m)
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem exists_pullback_disk_energy_le_of_tendsto_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M → F) (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    (hΦemb : _root_.Topology.IsEmbedding Φ)
    (hΦimm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p))
    (u : ℕ → C(closedDisk, M)) (w : V → M)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * edist x y)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => Φ (w x) i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => diskExtension (u n)
      (Complex.orthonormalBasisOneI.repr.symm x)) atTop (𝓝 (w x)))
    {a : ℝ} (henergy : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop (𝓝 a)) :
    ∃ (r : F → M) (N : Set F), IsOpen N ∧ range Φ ⊆ N ∧
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N ∧ Function.LeftInverse r Φ ∧
      (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        pullbackMetricCoefficients g r (Φ (w x))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) / 2 ≤ a := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hLip' (n : ℕ) : ∃ K : ℝ≥0, ∀ x y : V,
      riemannianEDistOf g (diskExtension (u n) (e x)) (diskExtension (u n) (e y)) ≤
        (K : ℝ≥0∞) * edist x y := by
    obtain ⟨K, hK⟩ := hLip n
    refine ⟨K, fun x y => ?_⟩
    simpa only [e.isometry.edist_eq] using diskExtension_riemannian_lipschitz g hK (e x) (e y)
  obtain ⟨r, N, hN, hΦN, hr, hleft, hi, hle⟩ :=
    exists_pullback_dirichlet_integral_le_liminf g Φ hΦ hΦemb hΦimm
      (fun n => diskExtension (u n) ∘ e) w hLip' hs hv hrep hweak hlim
  have heq (n : ℕ) :
      (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        g.inner (diskExtension (u n) (e x))
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (diskExtension (u n) ∘ e) x
            (EuclideanSpace.single j 1))
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (diskExtension (u n) ∘ e) x
            (EuclideanSpace.single j 1))) = 2 * riemannianDiskEnergy g (u n) :=
    sum_integral_metric_mfderiv_plane_isometry g (diskExtension (u n)) (hi n)
  simp only [Function.comp_def] at heq hle
  simp only [heq] at hle
  rw [(henergy.const_mul 2).liminf_eq] at hle
  refine ⟨r, N, hN, hΦN, hr, hleft, ?_⟩
  linarith

end DifferentialGeometry.Geometry
