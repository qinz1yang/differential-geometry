import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Affine
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Analysis.Integration.Measure.Affine
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Coordinates
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Scaling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal Pointwise

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem integral_weighted_diskMapEnergyDensity_comp_affine
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (ρ : M → ℝ) (b : ℂ)
    {r : ℝ} (hr : r ≠ 0) (S : Set ℂ) :
    (∫ z in S, ρ (U (b + r • z)) * diskMapEnergyDensity g (fun w => U (b + r • w)) z) =
      ∫ z in (fun w => b + r • w) '' S, ρ (U z) * diskMapEnergyDensity g U z := by
  simp_rw [diskMapEnergyDensity_comp_affine]
  have heq (z : ℂ) : ρ (U (b + r • z)) * (r ^ 2 * diskMapEnergyDensity g U (b + r • z)) =
      r ^ 2 * (ρ (U (b + r • z)) * diskMapEnergyDensity g U (b + r • z)) := by ring
  simp_rw [heq]
  rw [integral_const_mul, Measure.setIntegral_comp_smul volume
    (fun z => ρ (U (b + z)) * diskMapEnergyDensity g U (b + z)) S hr]
  simp only [Complex.finrank_real_complex, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
  simpa only [← image_smul, image_image] using
    ((measurePreserving_add_left (volume : Measure ℂ) b).setIntegral_image_emb
      (MeasurableEquiv.addLeft b).measurableEmbedding
      (fun z => ρ (U z) * diskMapEnergyDensity g U z) (r • S)).symm

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem integral_weighted_disk_energy_of_affine_restriction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (hU : Continuous U)
    (ρ : M → ℝ) (b : ℂ) {r : ℝ} (hr : 0 < r) :
    let w : C(closedDisk, M) := ⟨fun z => U (b + r • (z : ℂ)),
      hU.comp (continuous_const.add (continuous_subtype_val.const_smul r))⟩
    (∫ z in closedBall (0 : ℂ) 1,
      ρ (diskExtension w z) * diskMapEnergyDensity g (diskExtension w) z) =
      ∫ z in ball b r, ρ (U z) * diskMapEnergyDensity g U z := by
  intro w
  have heq : (∫ z in closedBall (0 : ℂ) 1,
      ρ (diskExtension w z) * diskMapEnergyDensity g (diskExtension w) z) =
      ∫ z in closedBall (0 : ℂ) 1,
        ρ (U (b + r • z)) * diskMapEnergyDensity g (fun y => U (b + r • y)) z := by
    apply integral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    have he : diskExtension w =ᶠ[𝓝 z] (fun y => U (b + r • y)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact diskExtension_coe w ⟨y, ball_subset_closedBall hy⟩
    unfold diskMapEnergyDensity diskMapPartial
    rw [he.mfderiv_eq, he.eq_of_nhds]
    rfl
  rw [heq, integral_weighted_diskMapEnergyDensity_comp_affine g U ρ b hr.ne']
  have himage : (fun w : ℂ => b + r • w) '' closedBall 0 1 = closedBall b r := by
    simpa only [← image_vadd, ← image_smul, image_image, vadd_eq_add] using
      affinity_unitClosedBall hr.le b
  rw [himage]
  have hrestrict : (volume.restrict (closedBall b r)).restrict (ball b r) =
      volume.restrict (closedBall b r) :=
    Measure.restrict_eq_self_of_ae_mem
      (ae_mem_ball_of_measure_sphere_eq_zero (Measure.addHaar_sphere volume b r))
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr ball_subset_closedBall] at hrestrict
  rw [hrestrict]

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem weighted_chart_energy_le_liminf_on_ball
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (χ ρ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ Φ.target)
    (hρsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρnonneg : ∀ p, 0 ≤ ρ p)
    (hρ : tsupport ρ ⊆ interior {p | χ p = 1} ∩ Φ.target)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A)
    (hw : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm x))) i) (ball 0 1))
    (b : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hbr : ‖b‖ + r < 1) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    let B (p : M) := (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
    (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball b r,
      B (v (e x)) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      liminf (fun n => ∫ z in ball (e b) r,
        ρ (diskExtension (u n) z) * diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  classical
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let U (n : ℕ) : ℂ → M := diskExtension (u n)
  have hUc (n : ℕ) : Continuous (U n) := (u n).continuous.comp diskRetraction_lipschitz.continuous
  let a : ℂ → ℂ := fun z => e b + r • z
  let w (n : ℕ) : C(closedDisk, M) := ⟨fun z => U n (a z),
    (hUc n).comp (continuous_const.add (continuous_subtype_val.const_smul r))⟩
  have hscaleLip : LipschitzWith (Real.nnabs r) a := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [a, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_eq_abs, Real.coe_nnabs, le_refl]
  have hwLip (n : ℕ) : ∃ C : ℝ≥0, ∀ z z',
      riemannianEDistOf g (w n z) (w n z') ≤ (C : ℝ≥0∞) * edist z z' := by
    obtain ⟨C, hC⟩ := hLip n
    refine ⟨C * Real.nnabs r, fun z z' => ?_⟩
    exact (diskExtension_riemannian_lipschitz g hC (a z) (a z')).trans
      ((mul_le_mul_right (hscaleLip z z') (C : ℝ≥0∞)).trans_eq (by
        rw [ENNReal.coe_mul, mul_assoc]
        rfl))
  have hballC : ball (e b) r ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ dist z (e b) + ‖e b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - e b) (e b)
    rw [e.norm_map] at hn
    exact mem_ball.mpr (by rw [dist_zero_right]; have hd := mem_ball.mp hz; linarith)
  have hmaps : MapsTo a (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    apply hballC
    simp only [a, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_iff_lt_one_right hr).mpr (mem_ball_zero_iff.mp hz)
  have hwAE : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (w n) z) atTop (𝓝 (v (a z))) := by
    have hq := ((measurePreserving_add_left (volume : Measure ℂ) (e b)).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume hr.ne')).restrict hmaps
    filter_upwards [hq.ae hae, ae_restrict_mem measurableSet_ball] with z hz hzB
    have heq (n : ℕ) : diskExtension (w n) z = U n (a z) :=
      diskExtension_coe (w n) ⟨z, ball_subset_closedBall hzB⟩
    simpa only [heq, U, a, Function.comp_apply] using hz
  have hwenergy (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (w n)) z) ≤ A := by
    have hi := integral_weighted_disk_energy_of_affine_restriction g (U n) (hUc n)
      (fun _ => (1 : ℝ)) (e b) hr
    simp only [one_mul] at hi
    rw [hi]
    obtain ⟨C, hC⟩ := hLip n
    exact (setIntegral_mono_set (integrable_diskMapEnergyDensity g hC)
      (Eventually.of_forall fun z => div_nonneg
        (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
          (by norm_num))
      (Eventually.of_forall (hballC.trans ball_subset_closedBall))).trans (henergy n)
  obtain ⟨hv, hbound⟩ := exists_weighted_chart_energy_le_liminf_of_cutoffs
    g L Φ χ ρ hχ hχc hχsupport hρsmooth hρc hρnonneg hρ w (v ∘ a) hwLip hwAE hwenergy
  let B (p : M) := (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
    L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  have hplane : MapsTo (fun x : EuclideanSpace ℝ (Fin 2) => b + r • x) (ball 0 1) (ball 0 1) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hn := norm_add_le b (r • x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hn
    exact mem_ball_zero_iff.mpr (hn.trans_lt (by nlinarith))
  let hw' (i : Fin m) := ((hw i).compAddSmul b hr.ne').restrict isOpen_ball hplane
  have heqfun (i : Fin m) :
      (fun x => L (χ (v (e (b + r • x))) • Φ.symm (v (e (b + r • x)))) i) =
        (fun x => L (χ ((v ∘ a) (e x)) • Φ.symm ((v ∘ a) (e x))) i) := by
    funext x
    simp only [Function.comp_apply, a, map_add, map_smul]
  have hgr (i : Fin m) : (hw' i).weakGrad =ᵐ[volume.restrict (ball 0 1)] (hv i).weakGrad := by
    have hfun : (fun x => L (χ (v (e (b + r • x))) • Φ.symm (v (e (b + r • x)))) i) =ᵐ[
        volume.restrict (ball 0 1)]
        (fun x => L (χ ((v ∘ a) (e x)) • Φ.symm ((v ∘ a) (e x))) i) :=
      Eventually.of_forall fun x => congrFun (heqfun i) x
    exact ((hw' i).congr hfun).ae_eq isOpen_ball (hv i)
  have hgradEq : (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      B ((v ∘ a) (e x)) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in ball b r,
        B (v (e x)) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    trans ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      B (v (e (b + r • x)))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hr.ne').weakGrad x j))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hr.ne').weakGrad x j))
    · apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hgr] with x hx
      have hG : (WithLp.toLp 2 (fun i => (hv i).weakGrad x j) : EuclideanSpace ℝ (Fin m)) =
          WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hr.ne').weakGrad x j) := by
        ext i
        exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z j) (hx i).symm
      rw [hG]
      simp only [Function.comp_apply, a, map_add, map_smul]
    · exact Analysis.integral_quadratic_weakGrad_compAddSmul_ball hw (fun x => B (v (e x))) b hr j
  have hweighted (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1,
      ρ (diskExtension (w n) z) * diskMapEnergyDensity g (diskExtension (w n)) z) =
      ∫ z in ball (e b) r, ρ (U n z) * diskMapEnergyDensity g (U n) z :=
    integral_weighted_disk_energy_of_affine_restriction g (U n) (hUc n) ρ (e b) hr
  change (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
    B ((v ∘ a) (e x)) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤ _ at hbound
  rw [hgradEq] at hbound
  simpa only [hweighted] using hbound

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem chart_energy_le_liminf_disk_energy_on_ball
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (χ ρ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ Φ.target)
    (hρsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρnonneg : ∀ p, 0 ≤ ρ p)
    (hρ : tsupport ρ ⊆ interior {p | χ p = 1} ∩ Φ.target)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A)
    (hw : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm x))) i) (ball 0 1))
    (b : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hbr : ‖b‖ + r < 1)
    (hρle : ∀ p, ρ p ≤ 1)
    (hρone : ∀ x ∈ ball b r, ρ (v (Complex.orthonormalBasisOneI.repr.symm x)) = 1)
    (hz : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm x))) i) (ball b r)) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    let B (p : M) := (pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
    (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball b r,
      B (v (e x)) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      liminf (fun n => ∫ z in ball (e b) r,
        diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  classical
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let U (n : ℕ) : ℂ → M := diskExtension (u n)
  let B (p : M) := (pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
    L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  let Bw (p : M) := (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
    L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  have hsub : ball b r ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x hx
    have hn : ‖x‖ ≤ dist x b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - b) b
    exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  have hsubC : ball (e b) r ⊆ closedBall (0 : ℂ) 1 := by
    intro z hzB
    have hn : ‖z‖ ≤ dist z (e b) + ‖e b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - e b) (e b)
    rw [e.norm_map] at hn
    exact mem_closedBall_zero_iff.mpr (by have hd := mem_ball.mp hzB; linarith)
  have hχone (x) (hx : x ∈ ball b r) : χ (v (e x)) = 1 := by
    have hne : ρ (v (e x)) ≠ 0 := by rw [hρone x hx]; exact one_ne_zero
    exact (interior_subset (s := {p : M | χ p = 1})) (hρ (subset_tsupport _ hne)).1
  have hgr (i : Fin m) : (hw i).weakGrad =ᵐ[volume.restrict (ball b r)] (hz i).weakGrad := by
    let hw' := (hw i).restrict isOpen_ball hsub
    have heq : (fun x => L (χ (v (e x)) • Φ.symm (v (e x))) i) =ᵐ[
        volume.restrict (ball b r)] (fun x => L (Φ.symm (v (e x))) i) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [hχone x hx, one_smul]
    exact (hw'.congr heq).ae_eq isOpen_ball (hz i)
  have hleft : (∑ j : Fin 2, ∫ x in ball b r,
      Bw (v (e x)) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in ball b r,
        B (v (e x)) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hz i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hgr, ae_restrict_mem measurableSet_ball] with x hx hxB
    have hG : (WithLp.toLp 2 (fun i => (hw i).weakGrad x j) : EuclideanSpace ℝ (Fin m)) =
        WithLp.toLp 2 (fun i => (hz i).weakGrad x j) := by
      ext i
      exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z j) (hx i)
    have hρx : ρ (v (e x)) = 1 := hρone x hxB
    simp only [hG, Bw, hρx, one_smul, B]
  have hweighted := weighted_chart_energy_le_liminf_on_ball g L Φ χ ρ hχ hχc hχsupport
    hρsmooth hρc hρnonneg hρ u v hLip hae henergy hw b hr hbr
  change (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball b r,
    Bw (v (e x)) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤ _ at hweighted
  rw [hleft] at hweighted
  apply hweighted.trans
  have hnonneg (n : ℕ) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (U n) z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hInt (n : ℕ) : IntegrableOn (diskMapEnergyDensity g (U n)) (closedBall (0 : ℂ) 1) := by
    obtain ⟨C, hC⟩ := hLip n
    exact integrable_diskMapEnergyDensity g hC
  have hWInt (n : ℕ) : IntegrableOn
      (fun z => ρ (U n z) * diskMapEnergyDensity g (U n) z) (ball (e b) r) := by
    apply ((hInt n).mono_set hsubC).bdd_mul (c := (1 : ℝ))
      (hρsmooth.continuous.comp ((u n).continuous.comp
        diskRetraction_lipschitz.continuous)).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      change ‖ρ (U n z)‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (hρnonneg _)]
      exact hρle _
  have hmono (n : ℕ) : (∫ z in ball (e b) r,
      ρ (U n z) * diskMapEnergyDensity g (U n) z) ≤
      ∫ z in ball (e b) r, diskMapEnergyDensity g (U n) z := by
    apply integral_mono_ae (hWInt n) ((hInt n).mono_set hsubC)
    exact Eventually.of_forall fun z => mul_le_of_le_one_left (hnonneg n z) (hρle _)
  have hupper (n : ℕ) : (∫ z in ball (e b) r, diskMapEnergyDensity g (U n) z) ≤ A :=
    (setIntegral_mono_set (hInt n) (Eventually.of_forall (hnonneg n))
      (Eventually.of_forall hsubC)).trans (henergy n)
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n =>
      ∫ z in ball (e b) r, ρ (U n z) * diskMapEnergyDensity g (U n) z) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ ∫ z in ball (e b) r,
      ρ (U n z) * diskMapEnergyDensity g (U n) z
    exact Eventually.of_forall fun n => integral_nonneg fun z =>
      mul_nonneg (hρnonneg _) (hnonneg n z)
  exact liminf_le_liminf (Eventually.of_forall hmono) hlo
    (isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hupper))

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem translated_chart_energy_le_liminf_disk_energy
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (χ ρ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ Φ.target)
    (hρsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρnonneg : ∀ p, 0 ≤ ρ p) (hρle : ∀ p, ρ p ≤ 1)
    (hρ : tsupport ρ ⊆ interior {p | χ p = 1} ∩ Φ.target)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A)
    (hw : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm x))) i) (ball 0 1))
    (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hbR : ‖b‖ + R < 1)
    (hρone : ∀ x ∈ ball b R, ρ (v (Complex.orthonormalBasisOneI.repr.symm x)) = 1)
    (hz : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm (b + x)))) i)
      (ball 0 R)) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    let z := fun x => L (Φ.symm (v (e (b + x))))
    let ψ := fun p => Φ (L.symm p)
    (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) r,
      pullbackMetricCoefficients g ψ (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      liminf (fun n => ∫ y in ball (e b) r,
        diskMapEnergyDensity g (diskExtension (u n)) y) atTop := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  let z := fun x => L (Φ.symm (v (e (b + x))))
  let ψ := fun p => Φ (L.symm p)
  let B (p : M) := (pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
    L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  have hsub : ball b R ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x hx
    have hn : ‖x‖ ≤ dist x b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - b) b
    exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  have hone (x) (hx : x ∈ ball b R) : χ (v (e x)) = 1 ∧ v (e x) ∈ Φ.target := by
    have hne : ρ (v (e x)) ≠ 0 := by rw [hρone x hx]; exact one_ne_zero
    have h := hρ (subset_tsupport _ hne)
    exact ⟨(interior_subset (s := {p : M | χ p = 1})) h.1, h.2⟩
  have hfun (i : Fin m) : (fun x => L (χ (v (e x)) • Φ.symm (v (e x))) i) =ᵐ[
      volume.restrict (ball b R)] (fun x => L (Φ.symm (v (e x))) i) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [(hone x hx).1, one_smul]
  let hz₀ (i : Fin m) := ((hw i).restrict isOpen_ball hsub).congr (hfun i)
  have htranslate : (fun x : EuclideanSpace ℝ (Fin 2) => b + (1 : ℝ) • x) ⁻¹' ball b R =
      ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    ext x
    simp only [mem_preimage, one_smul, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  let ht (i : Fin m) := ((hz₀ i).compAddSmul b (one_ne_zero : (1 : ℝ) ≠ 0)).restrict
    isOpen_ball (by rw [htranslate])
  have hgr (i : Fin m) : (fun x => (hw i).weakGrad (b + x)) =ᵐ[
      volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)] (hz i).weakGrad := by
    have heq : (fun x => L (Φ.symm (v (e (b + (1 : ℝ) • x)))) i) =ᵐ[
        volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)] (fun x => z x i) := by
      filter_upwards [] with x
      simp only [one_smul, z]
    have hg := ((ht i).congr heq).ae_eq isOpen_ball (hz i)
    simpa only [ht, DeGiorgi.MemW1pWitness.compAddSmul, one_smul, hz₀,
      DeGiorgi.MemW1pWitness.restrict, DeGiorgi.MemW1pWitness.congr] using hg
  have hcoeff (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r) :
      pullbackMetricCoefficients g ψ (z x) = B (v (e (b + x))) := by
    have hxR : b + x ∈ ball b R := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using
        ball_subset_ball hrR hx
    have hp := (hone (b + x) hxR).2
    have hsrc : Φ.symm (v (e (b + x))) ∈ Φ.source := Φ.toOpenPartialHomeomorph.map_target hp
    have hD : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ψ (z x) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (v (e (b + x))))).comp
          L.symm.toContinuousLinearMap := by
      have hΦ := (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hsrc)).mdifferentiableAt
        (by simp)
      have hL : Differentiable ℝ L.symm := L.symm.differentiable
      have heq : L.symm (z x) = Φ.symm (v (e (b + x))) := L.symm_apply_apply _
      change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E)
        ((Φ : E → M) ∘ L.symm) (z x) = _
      rw [mfderiv_comp (z x) (heq.symm ▸ hΦ) (hL (z x)).mdifferentiableAt,
        mfderiv_eq_fderiv, L.symm.fderiv, heq]
      rfl
    ext ξ η
    simp only [pullbackMetricCoefficients_apply, hD]
    change g.inner (Φ (L.symm (z x)))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (v (e (b + x)))) (L.symm ξ))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (v (e (b + x)))) (L.symm η)) = _
    have heq : L.symm (z x) = Φ.symm (v (e (b + x))) := L.symm_apply_apply _
    rw [heq]
    rfl
  have hleft : (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) r,
      pullbackMetricCoefficients g ψ (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in ball b r,
        B (v (e x)) (WithLp.toLp 2 (fun i => (hz₀ i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hz₀ i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    trans ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) r,
      B (v (e (b + x))) (WithLp.toLp 2 (fun i => (hw i).weakGrad (b + x) j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad (b + x) j))
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR)
        (ae_all_iff.mpr hgr), ae_restrict_mem measurableSet_ball] with x hx hxB
      have hG : (WithLp.toLp 2 (fun i => (hz i).weakGrad x j) : EuclideanSpace ℝ (Fin m)) =
          WithLp.toLp 2 (fun i => (hw i).weakGrad (b + x) j) := by
        ext i
        exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v j) (hx i).symm
      rw [hcoeff x hxB, hG]
    · have hm := measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin 2))) b
      have h := hm.setIntegral_preimage_emb (MeasurableEquiv.addLeft b).measurableEmbedding
          (fun x => B (v (e x)) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) (ball b r)
      have heq : (fun x : EuclideanSpace ℝ (Fin 2) => b + x) ⁻¹' ball b r = ball 0 r := by
        ext x
        simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
      rw [heq] at h
      exact h
  have hls := chart_energy_le_liminf_disk_energy_on_ball g L Φ χ ρ hχ hχc hχsupport
    hρsmooth hρc hρnonneg hρ u v hLip hae henergy hw b hr (by linarith) hρle
    (fun x hx => hρone x (ball_subset_ball hrR hx))
    (fun i => (hz₀ i).restrict isOpen_ball (ball_subset_ball hrR))
  change (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 r,
    pullbackMetricCoefficients g ψ (z x)
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤ _
  rw [hleft]
  exact hls

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem integral_disk_energy_comp_add_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) {L : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (L : ℝ≥0∞) * edist z z')
    {b : ℂ} {R : ℝ} (hbR : ‖b‖ + R < 1)
    {S : Set ℂ} (hS : S ⊆ closedBall (0 : ℂ) R) :
    (∫ z in S, diskMapEnergyDensity g (fun y => diskExtension u (b + y)) z) ≤
      ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  have hchange := integral_diskMapEnergyDensity_comp_affine g (diskExtension u) b
    (one_ne_zero : (1 : ℝ) ≠ 0) S
  simp only [one_smul] at hchange
  rw [hchange]
  apply setIntegral_mono_set (integrable_diskMapEnergyDensity g hu)
    (Eventually.of_forall fun z => div_nonneg
      (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _)) (by norm_num))
  apply Eventually.of_forall
  rintro z ⟨y, hy, rfl⟩
  have hyR := mem_closedBall_zero_iff.mp (hS hy)
  exact mem_closedBall_zero_iff.mpr ((norm_add_le b y).trans
    (by linarith : ‖b‖ + ‖y‖ ≤ 1))

end DifferentialGeometry.Geometry

end

end
