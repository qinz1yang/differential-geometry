import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicReplacement
import DifferentialGeometry.Analysis.Integration.PlaneScaling
import DifferentialGeometry.Analysis.Sobolev.Interpolation.ConvexAnnulus
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.CircleCompactness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.TargetApproximation.Convex

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set MeasureTheory Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_in_convex_chart_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ψ : F → M} {U K : Set F}
    (hU : IsOpen U) (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ U)
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ (f : ℂ → F) (L : ℝ≥0), LipschitzWith L f →
      MapsTo f (closedBall (0 : ℂ) 1) K →
      ∃ w : C(closedDisk, M),
        (∀ z : closedDisk, w z = ψ (f z)) ∧
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (C * L : ℝ≥0∞) * edist z z') ∧
        riemannianDiskEnergy g w =
          ∫ z in closedBall (0 : ℂ) 1,
            (pullbackMetricCoefficients g ψ (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
              pullbackMetricCoefficients g ψ (f z)
                (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  let A := pullbackMetricCoefficients g ψ
  have hA : ContinuousOn A K :=
    (contDiffOn_pullback_metric_coefficients g hU hψ).continuousOn.mono hKU
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA)
  let C : ℝ≥0 := Real.nnabs (Real.sqrt (max B 0))
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hbound (x : F) (hx : x ∈ K) (ξ : F) :
      Real.sqrt (g.inner (ψ x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ x ξ)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ x ξ)) ≤ C * ‖ξ‖ := by
    have hxB : ‖A x‖ ≤ max B 0 := (hB (mem_image_of_mem (fun x => ‖A x‖) hx)).trans
      (le_max_left _ _)
    have hquad : A x ξ ξ ≤ max B 0 * ‖ξ‖ ^ 2 := by
      calc
        _ ≤ ‖A x ξ ξ‖ := le_abs_self _
        _ ≤ ‖A x‖ * ‖ξ‖ * ‖ξ‖ := (A x).le_opNorm₂ ξ ξ
        _ ≤ max B 0 * ‖ξ‖ * ‖ξ‖ := by gcongr
        _ = max B 0 * ‖ξ‖ ^ 2 := by ring
    have hs := Real.sqrt_le_sqrt hquad
    simpa only [Real.sqrt_mul hB0, Real.sqrt_sq_eq_abs, abs_norm, C,
      Real.coe_nnabs, abs_of_nonneg (Real.sqrt_nonneg _), A,
      pullbackMetricCoefficients_apply] using hs
  have hψLip (x) (hx : x ∈ K) (y) (hy : y ∈ K) :
      riemannianEDistOf g (ψ x) (ψ y) ≤ (C : ℝ≥0∞) * edist x y :=
    riemannian_edist_le_on_convex_source g hU (hψ.of_le (by simp)) hKU hKconv hbound hx hy
  refine ⟨C, ?_⟩
  intro f L hf hfK
  let w : C(closedDisk, M) := ⟨fun z => ψ (f z),
    hψ.continuousOn.comp_continuous (hf.continuous.comp continuous_subtype_val)
      (fun z => hKU (hfK z.property))⟩
  refine ⟨w, fun _ => rfl, ?_, ?_⟩
  · intro z z'
    exact (hψLip (f z) (hfK z.property) (f z') (hfK z'.property)).trans
      ((mul_le_mul_right (hf z z') (C : ℝ≥0∞)).trans_eq (by rw [mul_assoc]; rfl))
  · apply integral_congr_ae
    filter_upwards [ae_disk_interior, ae_restrict_of_ae hf.ae_differentiableAt] with z hz hdf
    have hψz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (f z) :=
      (hψ.contMDiffAt (hU.mem_nhds (hKU (hfK (ball_subset_closedBall hz))))).mdifferentiableAt
        (by simp)
    have heq : diskExtension w =ᶠ[𝓝 z] ψ ∘ f := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact diskExtension_coe w ⟨y, ball_subset_closedBall hy⟩
    have hD : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (ψ ∘ f) z =
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (f z)).comp (fderiv ℝ f z) := by
      rw [mfderiv_comp z hψz hdf.mdifferentiableAt, mfderiv_eq_fderiv]
      rfl
    unfold diskMapEnergyDensity diskMapPartial
    rw [heq.mfderiv_eq, heq.eq_of_nhds, hD]
    rfl

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

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem disk_energy_le_chart_filling_add_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ψ : F → M} {U K : Set F}
    (hU : IsOpen U) (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ U)
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKU : K ⊆ U)
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f)
    {b : ℂ} {R : ℝ} (hR : 0 < R) (hbR : ‖b‖ + R < 1)
    (hfK : MapsTo f (closedBall (0 : ℂ) R) K)
    (hboundary : ∀ z ∈ sphere (0 : ℂ) R, ψ (f z) = diskExtension u (b + z)) :
    (∫ z in closedBall b R, diskMapEnergyDensity g (diskExtension u) z) ≤
      (∫ z in closedBall (0 : ℂ) R,
        (pullbackMetricCoefficients g ψ (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          pullbackMetricCoefficients g ψ (f z)
            (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) +
        (riemannianDiskEnergy g u -
          sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  let F₀ : ℂ → F := fun z => f (R • z)
  have hF : LipschitzWith (L * Real.nnabs R) F₀ := hf.comp (lipschitzWith_smul R)
  have hFK : MapsTo F₀ (closedBall (0 : ℂ) 1) K := by
    intro z hz
    apply hfK
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hR.le).trans_eq (mul_one R)
  obtain ⟨C, hC⟩ := exists_disk_in_convex_chart_of_lipschitz g hU hψ hK hKconv hKU
  obtain ⟨w, hw, hwLip, hwE⟩ := hC F₀ (L * Real.nnabs R) hF hFK
  have hboundaryw (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1) :
      w z = diskExtension u (b + R • (z : ℂ)) := by
    rw [hw]
    exact hboundary _ (by
      rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hz, mul_one])
  obtain ⟨v, hv, _, _, _, hvE⟩ :=
    exists_disk_replacement_from_unit_filling g hu w hwLip hR hbR hboundaryw
  have hbounded : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro e ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  have hInf := csInf_le hbounded (mem_image_of_mem
    (fun v : C(closedDisk, M) => riemannianDiskEnergy g v) hv)
  have hscale := Analysis.integral_quadratic_fderiv_comp_smul_closedBall
    (pullbackMetricCoefficients g ψ) f (by norm_num : (0 : ℝ) < 1) hR
  simp only [div_one] at hscale
  have henergy : riemannianDiskEnergy g w =
      ∫ z in closedBall (0 : ℂ) R,
        (pullbackMetricCoefficients g ψ (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          pullbackMetricCoefficients g ψ (f z)
            (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := hwE.trans hscale
  rw [henergy] at hvE
  linarith

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

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_local_chart_comparison_error_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ψ : F → M} {U K : Set F}
    (hU : IsOpen U) (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ U)
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKU : K ⊆ U)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (p q : ℕ → ℂ → F) (Kp Kq : ℕ → ℝ≥0)
    (hp : ∀ n, LipschitzWith (Kp n) (p n)) (hq : ∀ n, LipschitzWith (Kq n) (q n))
    {b : ℂ} {R : ℝ} (hR : 0 < R) (hbR : ‖b‖ + R < 1)
    (hgap : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
      ‖q n (circleMap 0 R (2 * Real.pi * t - Real.pi)) -
        p n (circleMap 0 R (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0))
    {D : ℝ} (hder : ∀ n, (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => q n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => p n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D)
    (hpK : ∀ᶠ n in atTop, MapsTo (p n) (sphere (0 : ℂ) R) K)
    (hqK : ∀ n, MapsTo (q n) (closedBall (0 : ℂ) R) K)
    (hboundary : ∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) R,
      ψ (p n z) = diskExtension (u n) (b + z)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, (∫ z in closedBall b R, diskMapEnergyDensity g (diskExtension (u n)) z) ≤
        (∫ z in closedBall (0 : ℂ) R,
          (pullbackMetricCoefficients g ψ (q n z) (fderiv ℝ (q n) z 1) (fderiv ℝ (q n) z 1) +
            pullbackMetricCoefficients g ψ (q n z)
              (fderiv ℝ (q n) z Complex.I) (fderiv ℝ (q n) z Complex.I)) / 2) + ε n := by
  let A := pullbackMetricCoefficients g ψ
  let energy (f : ℂ → F) (z : ℂ) :=
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  have hA : ContinuousOn A K :=
    (contDiffOn_pullback_metric_coefficients g hU hψ).continuousOn.mono hKU
  obtain ⟨h, hh, _, hgood, houter, hconverge⟩ :=
    Analysis.exists_convex_thin_annulus_tendsto_quadratic_energy
      p q Kp Kq hp hq hR hgap hder hK hKconv hpK hqK
  let f (n : ℕ) := attachThinAnnulus (p n) (q n) id R (h n)
  let ε (n : ℕ) := ((∫ z in closedBall (0 : ℂ) R, energy (f n) z) -
    (∫ z in closedBall (0 : ℂ) R, energy (q n) z)) +
    (riemannianDiskEnergy g (u n) -
      sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))
  refine ⟨ε, ?_, ?_⟩
  · have hδ := hmin.sub_const
      (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))
    simpa only [sub_self, add_zero, A, energy, f, ε] using (hconverge A hA).add hδ
  · filter_upwards [hgood, hboundary] with n hn hnb
    obtain ⟨C, hC⟩ := hn.2.1
    have hmatch (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
        ψ (f n z) = diskExtension (u n) (b + z) := by
      rw [show f n z = p n z from houter n z (by
        have hz' : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
        exact hz'.ge)]
      exact hnb z hz
    have hle := disk_energy_le_chart_filling_add_minimizing_defect
      g hU hψ hK hKconv hKU (hu n) hC hR hbR hn.2.2 hmatch
    change (∫ z in closedBall b R, diskMapEnergyDensity g (diskExtension (u n)) z) ≤
      (∫ z in closedBall (0 : ℂ) R, energy (f n) z) + _ at hle
    change (∫ z in closedBall b R, diskMapEnergyDensity g (diskExtension (u n)) z) ≤
      (∫ z in closedBall (0 : ℂ) R, energy (q n) z) + ε n
    dsimp only [ε]
    linarith

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

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [PseudoMetricSpace X]

theorem exists_original_energy_comparison_of_sobolev_collar_competitor
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    {P : M → EuclideanSpace ℝ (Fin m)}
    (hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 P)
    (hPc : HasCompactSupport P)
    {ψ : EuclideanSpace ℝ (Fin m) → M} {U K : Set (EuclideanSpace ℝ (Fin m))}
    (hU : IsOpen U) (hψ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ∞ ψ U)
    (hK : IsCompact K) (hKconv : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ K)
    (hKU : K ⊆ U) {O : Set X} (hO : IsOpen O)
    (hleft : ∀ x ∈ O, ψ (P (ι x)) = ι x)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (uX : ℕ → ℂ → X) (V : ℂ → X) (b : ℂ)
    (huX : ∀ n z, ι (uX n z) = diskExtension (u n) (b + z))
    (huLip : ∀ n, ∃ L : ℝ≥0, LipschitzWith L (uX n))
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R) (hbR : ‖b‖ + R < 1)
    (hV : ContinuousOn V {z : ℂ | ‖z‖ ∈ Icc r R})
    (hVO : MapsTo V {z : ℂ | ‖z‖ ∈ Icc r R} O)
    (hVK : MapsTo (fun z => P (ι (V z))) {z : ℂ | ‖z‖ ∈ Icc r R} (interior K))
    (huae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => uX n z) atTop (𝓝 (V z)))
    (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      diskMapEnergyDensity g (ι ∘ uX n) z) ≤ B)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (hf : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ Ω)
    (hcollar : ∀ z : ℂ, ‖z‖ ∈ Icc r R →
      f (Complex.orthonormalBasisOneI.repr z) = P (ι (V z))) :
    ∃ ρ ∈ Icc r R, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ n in atTop,
          (∫ z in closedBall b ρ, diskMapEnergyDensity g (diskExtension (u (σ n))) z) ≤
            (1 / 2 : ℝ) * (∑ j : Fin 2,
              ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ,
                pullbackMetricCoefficients g ψ (f x)
                  (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
                  (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) + ε n := by
  obtain ⟨q, Lq, D, _, hq, hqLip, hqK, hqBound, hqae, hqEnergy⟩ :=
    Analysis.Sobolev.Euclidean.exists_smooth_lipschitz_complex_convex_approximation_tendsto_energy
      hK hKconv h0 hΩ hf hfK hball
  have hAnn : {z : ℂ | ‖z‖ ∈ Icc r R} ⊆ closedBall (0 : ℂ) R :=
    fun z hz => mem_closedBall_zero_iff.mpr hz.2
  have hqae' : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => q n z) atTop (𝓝 (P (ι (V z)))) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAnn hqae,
      ae_restrict_mem (measurableSet_Icc.preimage continuous_norm.measurable)] with z hz hzA
    simpa only [zero_add, hcollar z hzA] using hz
  have hqAnn (n : ℕ) : (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖fderiv ℝ (q n) z‖ ^ 2) ≤ 2 * D := by
    have hi : IntegrableOn (fun z => ‖fderiv ℝ (q n) z‖ ^ 2) (closedBall (0 : ℂ) R) :=
      (((hq n).continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) R)
    exact (setIntegral_mono_set hi (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hAnn)).trans (hqBound n)
  obtain ⟨ρ, hρ, σ, hσ, Kp, hpLip, hgap, ⟨Dp, hpder⟩, hpK, hboundary⟩ :=
    exists_compact_probe_circle_recovery_data g ι hι hP hPc ψ hO hleft
      uX V q huLip (fun n => ⟨Lq n, hqLip n⟩) hr hrR hV hVO hVK huae hqae'
      (fun n => add_le_add (henergy n) (hqAnn n))
  let p : ℕ → ℂ → EuclideanSpace ℝ (Fin m) := fun n z => P (ι (uX (σ n) z))
  have hboundary' : ∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) ρ,
      ψ (p n z) = diskExtension (u (σ n)) (b + z) := by
    filter_upwards [hboundary] with n hn z hz
    exact (hn z hz).trans (huX (σ n) z)
  have hminσ := hmin.comp hσ.tendsto_atTop
  obtain ⟨ε₀, hε₀, hcompare⟩ := exists_local_chart_comparison_error_of_minimizing_sequence
    g hU hψ hK hKconv hKU (u ∘ σ) (fun n => hu (σ n)) hminσ
    p (q ∘ σ) Kp (Lq ∘ σ) hpLip (fun n => hqLip (σ n))
    (hr.trans_le hρ.1) (by linarith [hρ.2]) hgap hpder hpK
    (fun n z _ => hqK (σ n) z) hboundary'
  let J : ℝ := (1 / 2 : ℝ) * (∑ j : Fin 2,
    ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      pullbackMetricCoefficients g ψ (f x)
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))
  let energy (n : ℕ) : ℝ := ∫ z in closedBall (0 : ℂ) ρ,
    (pullbackMetricCoefficients g ψ (q (σ n) z)
        (fderiv ℝ (q (σ n)) z 1) (fderiv ℝ (q (σ n)) z 1) +
      pullbackMetricCoefficients g ψ (q (σ n) z)
        (fderiv ℝ (q (σ n)) z Complex.I) (fderiv ℝ (q (σ n)) z Complex.I)) / 2
  have hA : ContinuousOn (pullbackMetricCoefficients g ψ) K :=
    (contDiffOn_pullback_metric_coefficients g hU hψ).continuousOn.mono hKU
  have hE : Tendsto energy atTop (𝓝 J) :=
    (hqEnergy ρ hρ.2 (pullbackMetricCoefficients g ψ) hA).comp hσ.tendsto_atTop
  let ε (n : ℕ) := energy n - J + ε₀ n
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, sub_self, zero_add] using (hE.sub_const J).add hε₀
  refine ⟨ρ, hρ, σ, hσ, ε, hε, ?_⟩
  filter_upwards [hcompare] with n hn
  change (∫ z in closedBall b ρ, diskMapEnergyDensity g (diskExtension (u (σ n))) z) ≤
    energy n + ε₀ n at hn
  change (∫ z in closedBall b ρ, diskMapEnergyDensity g (diskExtension (u (σ n))) z) ≤ J + ε n
  dsimp only [ε]
  linarith

end DifferentialGeometry.Geometry

end

end
