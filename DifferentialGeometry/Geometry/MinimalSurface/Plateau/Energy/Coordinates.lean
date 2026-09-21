import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionDifferential
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DifferentialGeometry.Topology.Manifold.BumpFunction.Nested
import DifferentialGeometry.Geometry.Metric.Pullback.Localization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalWeakCompactness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

section

noncomputable section

open Manifold MeasureTheory Set
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

private theorem mfderiv_comp_linearEquiv
    {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (U : W → M) (L : V ≃L[ℝ] W) (z : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) z =
      (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) U (L z)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) L z := L.differentiableAt.mdifferentiableAt
  by_cases hU : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) U (L z)
  · rw [mfderiv_comp z hU hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, V) L.symm (L z) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) (U ∘ L) (L.symm (L z)) :=
        (L.symm_apply_apply z).symm ▸ h
      have heq : ((U ∘ L) ∘ L.symm) = U := by
        funext w
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hU (heq ▸ h'.comp (L z) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem sum_metric_mfderiv_plane_isometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ j : Fin 2, g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
        (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
        (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))) =
      2 * diskMapEnergyDensity g U (Complex.orthonormalBasisOneI.repr.symm x) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hd := mfderiv_comp_linearEquiv (E := E) U e.toContinuousLinearEquiv x
  have hde (j : Fin 2) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e x) (e (EuclideanSpace.single j 1)) := by
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E =>
      L (EuclideanSpace.single j 1)) hd
  have h0 : e (EuclideanSpace.single 0 (1 : ℝ)) = (1 : ℂ) := by simp [e]
  have h1 : e (EuclideanSpace.single 1 (1 : ℝ)) = Complex.I := by simp [e]
  change (∑ j : Fin 2, g.inner (U (e x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) (U ∘ e) x
        (EuclideanSpace.single j 1))) = 2 * diskMapEnergyDensity g U (e x)
  simp only [Fin.sum_univ_two, hde, h0, h1, diskMapEnergyDensity, diskMapPartial]
  ring

theorem sum_integral_metric_mfderiv_plane_isometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hi : ∀ j : Fin 2, IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) =>
      g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1)))
        (Metric.ball 0 1)) :
    (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      g.inner (U (Complex.orthonormalBasisOneI.repr.symm x))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
          (U ∘ Complex.orthonormalBasisOneI.repr.symm) x (EuclideanSpace.single j 1))) =
      2 * ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g U z := by
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [sum_metric_mfderiv_plane_isometry]
  rw [integral_const_mul]
  congr 1
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hset : e ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball 0 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hchange := e.measurePreserving.setIntegral_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding (diskMapEnergyDensity g U) (Metric.ball (0 : ℂ) 1)
  rw [hset] at hchange
  apply hchange.trans
  apply setIntegral_congr_set
  have hball := (ae_restrict_iff' measurableSet_closedBall).mp ae_disk_interior
  filter_upwards [hball] with z hz
  exact propext ⟨fun h => Metric.ball_subset_closedBall h, hz⟩

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T3Space M]

omit [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [T3Space M] in
private theorem coefficient_pullback_continuous_compact_posSemidef
    {m : ℕ} (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (hQpos : ∀ p, LinearMap.IsPosSemidef (Q p).toBilinForm)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    let B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
      CheegerGromovCompactness.pullbackForm (Q p, L.symm.toContinuousLinearMap)
    Continuous B ∧ HasCompactSupport B ∧
      (∀ p y, 0 ≤ B p y y) ∧ ∃ C : ℝ, ∀ p, ‖B p‖ ≤ C := by
  let : NormedAddCommGroup ((EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
    CheegerGromovCompactness.pullbackForm (Q p, L.symm.toContinuousLinearMap)
  have hB : Continuous B :=
    (CheegerGromovCompactness.pullbackForm.contDiff
      (E := EuclideanSpace ℝ (Fin m)) (F := E)).continuous.comp
      (hQ.prodMk (continuous_const (y := L.symm.toContinuousLinearMap)))
  have hBc : HasCompactSupport B := by
    apply hQc.mono
    intro p hp
    by_contra hn
    have hz : Q p = 0 := not_ne_iff.mp hn
    exact hp (by simp only [B, CheegerGromovCompactness.pullbackForm, hz,
      ContinuousLinearMap.bilinearComp_zero])
  exact ⟨hB, hBc, fun p y => (hQpos p).isNonneg.nonneg (L.symm y),
    hB.bounded_above_of_compact_support hBc⟩

omit [FiniteDimensional ℝ E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_weighted_chart_energy_le_liminf_of_cutoffs
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (χ ρ : M → ℝ)
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
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    let P : M → EuclideanSpace ℝ (Fin m) := fun p => L (χ p • Φ.symm p)
    let B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
        (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
          L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ hv : ∀ i : Fin m,
          DeGiorgi.MemW1pWitness 2 (fun x => P (v (e x)) i) (ball 0 1),
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
          B (v (e x)) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤
          liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
            ρ (diskExtension (u n) z) * diskMapEnergyDensity g (diskExtension (u n)) z)
            atTop := by
  classical
  let : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup ((EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let F : M → E := fun p => χ p • Φ.symm p
  let P : M → EuclideanSpace ℝ (Fin m) := L ∘ F
  let Q : M → E →L[ℝ] E →L[ℝ] ℝ :=
    fun p => ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)
  let B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    fun p => CheegerGromovCompactness.pullbackForm (Q p, L.symm.toContinuousLinearMap)
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F := by
    refine contMDiff_of_tsupport fun p hp => ?_
    have hpTarget : p ∈ Φ.target :=
      hχsupport (tsupport_smul_subset_left χ (fun p => Φ.symm p) hp)
    exact hχ.contMDiffAt.smul
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hpTarget))
  have hFc : HasCompactSupport F :=
    hχc.mono (Function.support_smul_subset_left χ (fun p => Φ.symm p))
  have hQOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)) Φ.target :=
    (contDiffOn_pullback_metric_coefficients g Φ.open_source
      Φ.contMDiffOn_toFun).contMDiffOn.comp Φ.contMDiffOn_invFun
        (fun p hp => Φ.toOpenPartialHomeomorph.map_target hp)
  have hA : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ Q := by
    refine contMDiff_of_tsupport fun p hp => ?_
    have hpTarget : p ∈ Φ.target :=
      (hρ (tsupport_smul_subset_left ρ
        (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)) hp)).2
    exact hρsmooth.contMDiffAt.smul (hQOn.contMDiffAt (Φ.open_target.mem_nhds hpTarget))
  have hAc : HasCompactSupport Q := hρc.mono (Function.support_smul_subset_left ρ
    (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)))
  have hApos (p : M) : LinearMap.IsPosSemidef (Q p).toBilinForm := by
    have hp := pullbackMetricCoefficients_isPosSemidef g Φ (Φ.symm p)
    refine ⟨⟨fun v w => ?_⟩, ⟨fun v => ?_⟩⟩
    · change ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) v w =
        ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) w v
      exact congrArg (fun r : ℝ => ρ p * r) (hp.isSymm.eq v w)
    · change 0 ≤ ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) v v
      exact mul_nonneg (hρnonneg p) (hp.isNonneg.nonneg v)
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (ball 0 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hPsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 P :=
    L.toContinuousLinearMap.contMDiff.comp (hF.of_le (by simp))
  have hPcompact : HasCompactSupport P := hFc.comp_left L.map_zero
  obtain ⟨hBcont, hBcompact, hBpos, C, hCbound⟩ :=
    coefficient_pullback_continuous_compact_posSemidef Q hA.continuous hAc hApos L
  choose Cu hu using hLip
  let U : ℕ → ℂ → M := fun n => diskExtension (u n)
  have hUcont (n : ℕ) : Continuous (U n) :=
    (u n).continuous.comp diskRetraction_lipschitz.continuous
  have henergy_nonneg (n : ℕ) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (U n) z := by
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  obtain ⟨Cρ, hCρ⟩ := hρsmooth.continuous.bounded_above_of_compact_support hρc
  let Dρ : ℝ := max Cρ 0
  have hDρ : 0 ≤ Dρ := le_max_right _ _
  have hρbound (p : M) : ‖ρ p‖ ≤ Dρ := (hCρ p).trans (le_max_left _ _)
  have hweightedInt (n : ℕ) : IntegrableOn
      (fun z => ρ (U n z) * diskMapEnergyDensity g (U n) z) (closedBall (0 : ℂ) 1) :=
    (integrable_diskMapEnergyDensity g (hu n)).bdd_mul
      (hρsmooth.continuous.comp (hUcont n)).aestronglyMeasurable
      (Eventually.of_forall fun z => hρbound (U n z))
  let q : ℕ → ℝ := fun n => ∫ z in closedBall (0 : ℂ) 1,
    ρ (U n z) * diskMapEnergyDensity g (U n) z
  have hqlo (n : ℕ) : 0 ≤ q n :=
    integral_nonneg fun z => mul_nonneg (hρnonneg (U n z)) (henergy_nonneg n z)
  have hqhi (n : ℕ) : q n ≤ Dρ * A := by
    calc
      q n ≤ ∫ z in closedBall (0 : ℂ) 1,
          Dρ * diskMapEnergyDensity g (U n) z := by
        apply integral_mono_ae (hweightedInt n)
          ((integrable_diskMapEnergyDensity g (hu n)).const_mul Dρ)
        exact Eventually.of_forall fun z => mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hρbound (U n z))) (henergy_nonneg n z)
      _ = Dρ * ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (U n) z :=
        integral_const_mul _ _
      _ ≤ Dρ * A := mul_le_mul_of_nonneg_left (henergy n) hDρ
  have hqBound : IsBoundedUnder (· ≥ ·) atTop q := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q n
    exact Eventually.of_forall hqlo
  obtain ⟨τ₀, hτ₀q, hτ₀⟩ := exists_seq_tendsto_liminf
    (isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hqhi))
    hqBound
  obtain ⟨τ₁, hτ₁, hτmono⟩ := strictMono_subseq_of_tendsto_atTop hτ₀
  let τ := τ₀ ∘ τ₁
  have hτ : StrictMono τ := hτmono
  have hτq : Tendsto (fun n => q (τ n)) atTop (𝓝 (liminf q atTop)) :=
    hτ₀q.comp hτ₁.tendsto_atTop
  have haeτ : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => U (τ n) z) atTop (𝓝 (v z)) :=
    hae.mono fun z hz => hz.comp hτ.tendsto_atTop
  obtain ⟨K, _, hclosure⟩ :=
    exists_coordinate_weak_gradients_comp_diskExtension_of_ae_tendsto g hPsmooth hPcompact
  obtain ⟨hs, σ, hv, hrep, hσ, _, _, _, hweak⟩ := hclosure
    (fun n => u (τ n)) v (fun n => ⟨Cu (τ n), hu (τ n)⟩) haeτ (fun n => henergy (τ n))
  let k := τ ∘ σ
  have hkq : Tendsto (fun n => q (k n)) atTop (𝓝 (liminf q atTop)) :=
    hτq.comp hσ.tendsto_atTop
  let f : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m) :=
    fun n x => P (U (k n) (e x))
  let f₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m) := fun x => P (v (e x))
  obtain ⟨KP, _, hPbound⟩ :=
    exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g hPsmooth hPcompact
  have hf (n : ℕ) : LipschitzWith (KP * Cu (k n)) (f n) := by
    have hfc : LipschitzWith (KP * Cu (k n)) (P ∘ U (k n)) := by
      intro z w
      exact (hPbound _ _).trans (by
        simpa only [ENNReal.coe_mul, mul_assoc] using
          mul_le_mul_right (diskExtension_riemannian_lipschitz g (hu (k n)) z w)
            (KP : ℝ≥0∞))
    simpa only [f, Function.comp_def, mul_one] using hfc.comp e.lipschitz
  let Bn := fun n x => B (U (k n) (e x))
  let Bv := fun x => B (v (e x))
  have hBn (n : ℕ) : AEStronglyMeasurable (Bn n) μ :=
    (hBcont.comp ((hUcont (k n)).comp e.continuous)).aestronglyMeasurable
  have hBconv : ∀ᵐ x ∂μ, Tendsto (fun n => Bn n x) atTop (𝓝 (Bv x)) := by
    have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
    have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
    rw [hball] at he
    filter_upwards [he.quasiMeasurePreserving.ae hae] with x hx
    exact (hBcont.tendsto (v (e x))).comp (hx.comp (hτ.comp hσ).tendsto_atTop)
  have hls :=
    Analysis.Sobolev.Euclidean.sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    f f₀ (fun n i => hs i (σ n)) hv (fun n => KP * Cu (k n)) hf
    (fun n i j => Eventually.of_forall fun x => hrep i (σ n) x j)
    hweak Bn Bv hBn C (fun n => Eventually.of_forall fun x => hCbound _)
    hBconv (fun n => Eventually.of_forall fun x y => hBpos _ y)
  have hidentity (n : ℕ) :
      (∑ j : Fin 2, ∫ x in ball 0 1,
        Bn n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) = 2 * q (k n) := by
    have hmd : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        𝓘(ℝ, E) (U (k n) ∘ e) x := by
      have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
      have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        ext x
        simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
      rw [hball] at he
      have hdiff := ae_mdifferentiableAt_of_metric_lipschitz (μ := (volume : Measure ℂ)) g
        (diskExtension_riemannian_lipschitz g (hu (k n)))
      filter_upwards [he.quasiMeasurePreserving.ae
        (ae_restrict_of_ae (s := ball (0 : ℂ) 1) hdiff)] with x hx
      exact hx.comp x e.differentiableAt.mdifferentiableAt
    have hpoint : ∀ᵐ x ∂μ,
        (∑ j : Fin 2, Bn n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) =
          2 * (ρ (U (k n) (e x)) * diskMapEnergyDensity g (U (k n)) (e x)) := by
      filter_upwards [hmd] with x hx
      have hd : fderiv ℝ (f n) x = L.toContinuousLinearMap.comp
          (fderiv ℝ (F ∘ (U (k n) ∘ e)) x) := L.comp_fderiv
      have hi (j : Fin 2) :
          Bn n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
            (fderiv ℝ (f n) x (EuclideanSpace.single j 1)) =
          ρ (U (k n) (e x)) * g.inner (U (k n) (e x))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
              (U (k n) ∘ e) x (EuclideanSpace.single j 1))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E)
              (U (k n) ∘ e) x (EuclideanSpace.single j 1)) := by
        simp only [Bn, B, CheegerGromovCompactness.pullbackForm_apply, hd,
          ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          L.symm_apply_apply]
        change ρ (U (k n) (e x)) * pullbackMetricCoefficients g Φ (Φ.symm (U (k n) (e x)))
          (fderiv ℝ (F ∘ (U (k n) ∘ e)) x (EuclideanSpace.single j 1))
          (fderiv ℝ (F ∘ (U (k n) ∘ e)) x (EuclideanSpace.single j 1)) = _
        exact smul_pullbackMetricCoefficients_fderiv_of_tsupport_subset g Φ χ ρ hρ hx
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)
      simp_rw [hi]
      rw [← Finset.mul_sum, sum_metric_mfderiv_plane_isometry]
      ring
    have hjMem (j : Fin 2) : MemLp
        (fun x => fderiv ℝ (f n) x (EuclideanSpace.single j 1)) 2 μ := by
      refine MemLp.of_bound
        ((measurable_fderiv ℝ (f n)).apply_continuousLinearMap _).aestronglyMeasurable
        (KP * Cu (k n) : ℝ≥0) (Eventually.of_forall fun x => ?_)
      have h := (fderiv ℝ (f n) x).le_opNorm (EuclideanSpace.single j 1)
      have hle : ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ≤ ‖fderiv ℝ (f n) x‖ := by
        simpa using h
      exact hle.trans (norm_fderiv_le_of_lipschitz ℝ (hf n))
    have hiInt (j : Fin 2) : Integrable
        (fun x => Bn n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) μ :=
      integrable_bilinear_of_apply_aestronglyMeasurable (Bn n)
        (fun a b => ((hBn n).apply_continuousLinearMap a).apply_continuousLinearMap b)
        (Eventually.of_forall fun x => hCbound _) (hjMem j) (hjMem j)
    rw [← integral_finsetSum _ (fun j _ => hiInt j)]
    rw [integral_congr_ae hpoint, integral_const_mul]
    congr 1
    have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
    have hchange := e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding
      (fun z => ρ (U (k n) z) * diskMapEnergyDensity g (U (k n)) z) (ball (0 : ℂ) 1)
    rw [hball] at hchange
    have hrestrict : (volume.restrict (closedBall (0 : ℂ) 1)).restrict (ball 0 1) =
        volume.restrict (closedBall (0 : ℂ) 1) :=
      Measure.restrict_eq_self_of_ae_mem ae_disk_interior
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr ball_subset_closedBall] at hrestrict
    simpa only [q, hrestrict] using hchange
  have hlim : Tendsto
      (fun n => ∑ j : Fin 2, ∫ x in ball 0 1,
        Bn n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (2 * liminf q atTop)) := by
    simpa only [hidentity] using hkq.const_mul 2
  rw [hlim.liminf_eq] at hls
  refine ⟨hv, ?_⟩
  change (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
    Bv x (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤ liminf q atTop
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_weighted_chart_energy_le_liminf
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (center : M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
      (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ center).symm
    ∃ χ ρ : SmoothBumpFunction 𝓘(ℝ, E) center,
      tsupport (ρ : M → ℝ) ⊆ interior {p | χ p = 1} ∩ Φ.target ∧
      ρ center = 1 ∧ (∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) ∧
      let P : M → EuclideanSpace ℝ (Fin m) := fun p => L (χ p • Φ.symm p)
      let B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
        (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
          L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
      let e := Complex.orthonormalBasisOneI.repr.symm
      ∃ hv : ∀ i : Fin m,
          DeGiorgi.MemW1pWitness 2 (fun x => P (v (e x)) i) (ball 0 1),
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
          B (v (e x)) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤
          liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
            ρ (diskExtension (u n) z) * diskMapEnergyDensity g (diskExtension (u n)) z)
            atTop := by
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
    (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ center).symm
  obtain ⟨χ, ρ, hρ, hρcenter, hρrange, _⟩ :=
    exists_nested_chart_cutoffs_pullback_metric_coefficients g center
  have htarget : Φ.target = (chartAt E center).source := by
    change (extChartAt 𝓘(ℝ, E) center).source = _
    exact extChartAt_source 𝓘(ℝ, E) center
  have hχsupport : tsupport (χ : M → ℝ) ⊆ Φ.target := by
    rw [htarget]
    exact χ.tsupport_subset_chartAt_source
  refine ⟨χ, ρ, hρ, hρcenter, hρrange, ?_⟩
  exact exists_weighted_chart_energy_le_liminf_of_cutoffs g L Φ χ ρ
    χ.contMDiff χ.hasCompactSupport hχsupport ρ.contMDiff ρ.hasCompactSupport
    (fun p => (hρrange p).1) hρ u v hLip hae henergy

end DifferentialGeometry.Geometry

end

end
