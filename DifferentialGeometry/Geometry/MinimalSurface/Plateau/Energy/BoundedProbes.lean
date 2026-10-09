import DifferentialGeometry.Analysis.Sobolev.MetricTarget.WeakCompactness
import DifferentialGeometry.Geometry.Measure.Energy.ScalarComposition
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Equiv

section

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
theorem exists_memW1pWitness_bounded_intrinsic_probe_of_ae_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → ℝ}
    (hΦ : Continuous Φ) {D : ℝ} (hD : ∀ p, ‖Φ p‖ ≤ D) (K : ℝ≥0)
    (hbound : ∀ p q, edist (Φ p) (Φ q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ hv : DeGiorgi.MemW1pWitness 2 (fun x => Φ (v (e x))) (ball 0 1),
      Tendsto (fun n => eLpNorm (fun z => Φ (diskExtension (u n) z) - Φ (v z))
        2 (volume.restrict (ball (0 : ℂ) 1))) atTop (𝓝 0) ∧
      (∫ x in ball 0 1, ‖hv.weakGrad x‖ ^ 2) ≤ 2 * (K : ℝ) ^ 2 * A ∧
      (∫ x in ball 0 1, ‖hv.weakGrad x‖ ^ 2) ≤
        liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
          ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2) atTop := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let f : ℕ → ℂ → ℝ := fun n => Φ ∘ diskExtension (u n)
  let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hf (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (f n) := by
    obtain ⟨L, hL⟩ := hLip n
    refine ⟨K * L, ?_⟩
    intro z w
    calc
      edist (f n z) (f n w) ≤ (K : ℝ≥0∞) *
          riemannianEDistOf g (diskExtension (u n) z) (diskExtension (u n) w) :=
        hbound _ _
      _ ≤ (K : ℝ≥0∞) * ((L : ℝ≥0∞) * edist z w) :=
        mul_le_mul_right (diskExtension_riemannian_lipschitz g hL z w) _
      _ = ((K * L : ℝ≥0) : ℝ≥0∞) * edist z w := by rw [ENNReal.coe_mul, mul_assoc]
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
  have hnorm (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f n ∘ e) x‖ = ‖fderiv ℝ (f n) (e x)‖ := by
    change ‖fderiv ℝ (f n ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ (f n) (e x)).opNorm_comp_linearIsometryEquiv e
  have henergyEq (n : ℕ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖fderiv ℝ (f n ∘ e) x‖ ^ 2) =
        ∫ z in closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2 := by
    simp_rw [hnorm]
    exact hint (fun z => ‖fderiv ℝ (f n) z‖ ^ 2)
  have hB (n : ℕ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖fderiv ℝ (f n ∘ e) x‖ ^ 2) ≤
        2 * (K : ℝ) ^ 2 * A := by
    rw [henergyEq]
    obtain ⟨L, hL⟩ := hLip n
    exact (integral_norm_fderiv_sq_le_mul_disk_energy g (u n) hL
      (fun z w => hbound _ _)).trans
      (mul_le_mul_of_nonneg_left (henergy n) (by positivity))
  have haee : ∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      Tendsto (fun n => diskExtension (u n) (e x)) atTop (𝓝 (v (e x))) := by
    have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
    have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
    rw [hball] at he
    exact he.quasiMeasurePreserving.ae hae
  have hLipe (n : ℕ) : ∃ L : ℝ≥0,
      LipschitzWith L (Φ ∘ (fun x => diskExtension (u n) (e x))) := by
    obtain ⟨L, hL⟩ := hf n
    exact ⟨L, by simpa only [f, Function.comp_def, mul_one] using hL.comp e.lipschitzWith⟩
  obtain ⟨_, _, hv, _, _, _, hvbound, _, hvenergy⟩ :=
    Analysis.Sobolev.Euclidean.exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz
      hΦ hD (fun n x => diskExtension (u n) (e x)) (fun x => v (e x))
      hLipe haee hB
  have hL2 := (MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hΦ hD (fun n => (hf n).choose_spec.continuous.aestronglyMeasurable) hae).2
  refine ⟨hv, hL2, ?_, ?_⟩
  · have hnonneg : 0 ≤ 2 * (K : ℝ) ^ 2 * A :=
      (integral_nonneg fun x => sq_nonneg _).trans (hB 0)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hvbound
    rw [Real.sq_sqrt hnonneg,
      Analysis.Sobolev.Euclidean.norm_gradLpOfWitness_sq_eq_integral] at hsq
    exact hsq
  · change (∫ x in ball 0 1, ‖hv.weakGrad x‖ ^ 2) ≤
      liminf (fun n => ∫ x in ball 0 1, ‖fderiv ℝ (f n ∘ e) x‖ ^ 2) atTop at hvenergy
    simp_rw [henergyEq] at hvenergy
    exact hvenergy

end DifferentialGeometry.Geometry

end

end
