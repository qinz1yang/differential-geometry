import DifferentialGeometry.Analysis.Sobolev.MetricTarget.WeakCompactness
import DifferentialGeometry.Geometry.Measure.Energy.ScalarComposition
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Equiv

section

set_option autoImplicit false

noncomputable section

open Bundle Filter MeasureTheory Set Metric
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_coordinate_weak_gradients_comp_diskExtension_of_ae_tendsto
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Φ : M → EuclideanSpace ℝ (Fin m)}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ},
      (∀ n, ∃ L : ℝ≥0, ∀ z w,
        riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * edist z w) →
      (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
        Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z))) →
      (∀ n, (∫ z in closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) →
      let e := Complex.orthonormalBasisOneI.repr.symm
      let f := fun (i : Fin m) (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) =>
        Φ (diskExtension (u n) (e x)) i
      let f₀ := fun (i : Fin m) (x : EuclideanSpace ℝ (Fin 2)) => Φ (v (e x)) i
      ∃ (hs : ∀ i n, DeGiorgi.MemW1pWitness 2 (f i n) (ball 0 1))
        (σ : ℕ → ℕ) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (f₀ i) (ball 0 1)),
        (∀ i n x j, (hs i n).weakGrad x j =
          fderiv ℝ (f i n) x (EuclideanSpace.single j 1)) ∧
        StrictMono σ ∧
        (∀ i, Tendsto (fun n => eLpNorm (fun x => f i n x - f₀ i x)
          2 (volume.restrict (ball 0 1))) atTop (𝓝 0)) ∧
        (∀ i n, ‖DeGiorgi.gradLpOfWitness (hs i n)‖ ≤
          Real.sqrt (2 * (K : ℝ) ^ 2 * A)) ∧
        (∀ i, ‖DeGiorgi.gradLpOfWitness (hv i)‖ ≤
          Real.sqrt (2 * (K : ℝ) ^ 2 * A)) ∧
        ∀ i (z : Lp (EuclideanSpace ℝ (Fin 2)) 2 (volume.restrict (ball 0 1))),
          Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs i (σ n))) z) atTop
            (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g hΦ hΦc
  obtain ⟨D, hD⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hproj (i : Fin m) : LipschitzWith 1
      (fun x : EuclideanSpace ℝ (Fin m) => x i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [one_mul, NNReal.coe_one, dist_eq_norm, PiLp.sub_apply] using
      PiLp.norm_apply_le (x - y) i
  have hcoord (i : Fin m) (p q : M) :
      edist (Φ p i) (Φ q i) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q := by
    have hp := hproj i (Φ p) (Φ q)
    rw [ENNReal.coe_one, one_mul] at hp
    exact hp.trans (hbound p q)
  have hcoordD (i : Fin m) (p : M) : ‖Φ p i‖ ≤ D :=
    (PiLp.norm_apply_le (Φ p) i).trans (hD p)
  refine ⟨K, hK, ?_⟩
  intro u v A hLip hae henergy
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let fC : Fin m → ℕ → ℂ → ℝ := fun i n z => Φ (diskExtension (u n) z) i
  let f : Fin m → ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun i n x => fC i n (e x)
  let f₀ : Fin m → EuclideanSpace ℝ (Fin 2) → ℝ := fun i x => Φ (v (e x)) i
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (ball 0 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  choose L hL using hLip
  have hLipC (i : Fin m) (n : ℕ) : LipschitzWith (K * L n) (fC i n) := by
    intro z w
    calc
      edist (fC i n z) (fC i n w) ≤ (K : ℝ≥0∞) *
          riemannianEDistOf g (diskExtension (u n) z) (diskExtension (u n) w) := hcoord i _ _
      _ ≤ (K : ℝ≥0∞) * ((L n : ℝ≥0∞) * edist z w) :=
        mul_le_mul_right (diskExtension_riemannian_lipschitz g (hL n) z w) _
      _ = ((K * L n : ℝ≥0) : ℝ≥0∞) * edist z w := by
        rw [ENNReal.coe_mul, mul_assoc]
  have hLipE (i : Fin m) (n : ℕ) : LipschitzWith (K * L n) (f i n) := by
    simpa only [f, Function.comp_def, mul_one] using (hLipC i n).comp e.lipschitzWith
  have hint (q : ℂ → ℝ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, q (e x)) =
        ∫ z in closedBall (0 : ℂ) 1, q z := by
    have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
    have hrestrict : (volume.restrict (closedBall (0 : ℂ) 1)).restrict (ball 0 1) =
        volume.restrict (closedBall (0 : ℂ) 1) :=
      Measure.restrict_eq_self_of_ae_mem ae_disk_interior
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr ball_subset_closedBall] at hrestrict
    have h := e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding q (ball (0 : ℂ) 1)
    simpa only [hball, hrestrict] using h
  have hnorm (i : Fin m) (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f i n) x‖ = ‖fderiv ℝ (fC i n) (e x)‖ := by
    change ‖fderiv ℝ (fC i n ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ (fC i n) (e x)).opNorm_comp_linearIsometryEquiv e
  have henergyE (i : Fin m) (n : ℕ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖fderiv ℝ (f i n) x‖ ^ 2) ≤
        2 * (K : ℝ) ^ 2 * A := by
    simp_rw [hnorm]
    rw [hint (fun z => ‖fderiv ℝ (fC i n) z‖ ^ 2)]
    exact (integral_norm_fderiv_sq_le_mul_disk_energy g (u n) (hL n)
      (fun z w => hcoord i _ _)).trans
      (mul_le_mul_of_nonneg_left (henergy n) (by positivity))
  have hfm (i : Fin m) (n : ℕ) : MemLp (f i n) 2 μ :=
    MemLp.of_bound (hLipE i n).continuous.aestronglyMeasurable D
      (Eventually.of_forall fun x => hcoordD i _)
  have hdfm (i : Fin m) (n : ℕ) : MemLp (fderiv ℝ (f i n)) 2 μ :=
    MemLp.of_bound (measurable_fderiv ℝ (f i n)).aestronglyMeasurable (K * L n)
      (Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ (hLipE i n))
  choose hs hrep hgradnorm using fun i n =>
    Analysis.Sobolev.Euclidean.exists_memW1pWitness_fderiv_of_lipschitz
      (hLipE i n) (hfm i n) (hdfm i n)
  have hgradbound (i : Fin m) (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hs i n)‖ ≤
      Real.sqrt (2 * (K : ℝ) ^ 2 * A) := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hgradnorm i n]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le
        (hdfm i n) (henergyE i n))).trans_eq (ENNReal.toReal_ofReal (Real.sqrt_nonneg _))
  have haee : ∀ᵐ x ∂μ,
      Tendsto (fun n => diskExtension (u n) (e x)) atTop (𝓝 (v (e x))) := by
    have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
    have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
    rw [hball] at he
    exact he.quasiMeasurePreserving.ae hae
  have hvdata (i : Fin m) : MemLp (f₀ i) 2 μ ∧
      Tendsto (fun n => eLpNorm (fun x => f i n x - f₀ i x) 2 μ) atTop (𝓝 0) := by
    exact MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      ((EuclideanSpace.proj i).continuous.comp hΦ.continuous) (hcoordD i)
      (fun n => (hfm i n).aestronglyMeasurable) haee
  obtain ⟨σ, hv, hσ, hvbound, hweak⟩ :=
    Analysis.Sobolev.Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded
      f f₀ hs (fun i => (hvdata i).1) (fun _ => Real.sqrt (2 * (K : ℝ) ^ 2 * A))
      hgradbound (fun i => (hvdata i).2)
  exact ⟨hs, σ, hv, hrep, hσ, fun i => (hvdata i).2, hgradbound, hvbound, hweak⟩

end DifferentialGeometry.Geometry

end

end
