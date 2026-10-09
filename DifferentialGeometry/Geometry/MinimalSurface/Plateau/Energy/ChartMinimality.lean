import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartComparison
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalLowerSemicontinuity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ZeroTraceRange
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartLocalization
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Topology.Connected.FiniteEDistance

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [PseudoMetricSpace X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_chart_energy_le_of_memW01p_sub
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hιcont : Continuous ι)
    (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (χ ρ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ Φ.target)
    (hρsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρnonneg : ∀ p, 0 ≤ ρ p) (hρle : ∀ p, ρ p ≤ 1)
    (hρsupport : tsupport ρ ⊆ interior {p | χ p = 1} ∩ Φ.target)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) (v : ℂ → M)
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (hw : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm x))) i) (ball 0 1))
    (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hbR : ‖b‖ + R < 1)
    (hρone : ∀ x ∈ ball b R, ρ (v (Complex.orthonormalBasisOneI.repr.symm x)) = 1)
    (uX : ℕ → ℂ → X) (V : ℂ → X)
    (huX : ∀ n z, ι (uX n z) = diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm b + z))
    (hVeq : ∀ z, ι (V z) = v (Complex.orthonormalBasisOneI.repr.symm b + z))
    (huLip : ∀ n, ∃ C : ℝ≥0, LipschitzWith C (uX n))
    (hV : ContinuousOn V (ball (0 : ℂ) R))
    (huV : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) R),
      Tendsto (fun n => uX n z) atTop (𝓝 (V z)))
    {K : Set (EuclideanSpace ℝ (Fin m))}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ K)
    (hKsource : MapsTo L.symm K Φ.source)
    (hzK : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm (b + x)))) ∈ interior K)
    (hz : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm (b + x)))) i) (ball 0 R))
    {s : ℝ} (hs : 0 < s) (hsR : s < R)
    (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball 0 s))
    (hqz : ∀ i, DeGiorgi.MemW01p 2 (fun x => q x i -
      L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm (b + x)))) i) (ball 0 s))
    (hqK : ∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) s), q x ∈ K) :
    let ψ := fun p => Φ (L.symm p)
    let z := fun x => L (Φ.symm (v (Complex.orthonormalBasisOneI.repr.symm (b + x))))
    (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
      pullbackMetricCoefficients g ψ (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
        pullbackMetricCoefficients g ψ (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  let ψ := fun p => Φ (L.symm p)
  let z := fun x => L (Φ.symm (v (e (b + x))))
  let P : M → EuclideanSpace ℝ (Fin m) := fun p => L (χ p • Φ.symm p)
  let U := L.symm ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.symm.continuous
  have hψ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ∞ ψ U :=
    Φ.contMDiffOn_toFun.comp L.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  have hPsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 P := by
    have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun p => χ p • Φ.symm p) := by
      refine contMDiff_of_tsupport fun p hp => ?_
      have hpt := hχsupport (tsupport_smul_subset_left χ (fun p => Φ.symm p) hp)
      exact hχ.contMDiffAt.smul
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hpt))
    exact L.toContinuousLinearMap.contMDiff.comp (hF.of_le (by simp))
  have hPc : HasCompactSupport P :=
    (hχc.mono (Function.support_smul_subset_left χ (fun p => Φ.symm p))).comp_left L.map_zero
  have hzKae : ∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R), z x ∈ K := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact interior_subset (hzK x hx)
  obtain ⟨f, hf, hfq, hfz, hfK, hgradfq⟩ :=
    exists_weak_extension_mem_set_of_memW01p_sub isOpen_ball isOpen_ball
      (ball_subset_ball hsR.le) hz hq hqz hzKae hqK
  obtain ⟨r, hsr, hrR⟩ := exists_between hsR
  obtain ⟨R₁, hrR₁, hR₁R⟩ := exists_between hrR
  have hr : 0 < r := hs.trans hsr
  let S := {y : ℂ | ‖y‖ ∈ Icc r R₁}
  have hS : S ⊆ ball (0 : ℂ) R := fun y hy =>
    mem_ball_zero_iff.mpr (hy.2.trans_lt hR₁R)
  have hplane (y : ℂ) (hy : y ∈ ball (0 : ℂ) R) :
      b + e.symm y ∈ ball b R := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, e.symm.norm_map,
      dist_zero_right, sub_zero] using hy
  have hone (y : ℂ) (hy : y ∈ ball (0 : ℂ) R) :
      ι (V y) ∈ interior {p | χ p = 1} ∩ Φ.target := by
    have he : e (b + e.symm y) = e b + y := by rw [map_add, e.apply_symm_apply]
    have h1raw : ρ (v (e (b + e.symm y))) = 1 := hρone _ (hplane y hy)
    rw [he] at h1raw
    have h1 : ρ (ι (V y)) = 1 := (congrArg ρ (hVeq y)).trans h1raw
    have hne : ρ (ι (V y)) ≠ 0 := by rw [h1]; exact one_ne_zero
    exact hρsupport (subset_tsupport _ hne)
  let O := ι ⁻¹' (interior {p | χ p = 1} ∩ Φ.target)
  have hO : IsOpen O := (isOpen_interior.inter Φ.open_target).preimage hιcont
  have hleft (x : X) (hx : x ∈ O) : ψ (P (ι x)) = ι x := by
    have h1 : χ (ι x) = 1 := (interior_subset (s := {p : M | χ p = 1})) hx.1
    change Φ (L.symm (L (χ (ι x) • Φ.symm (ι x)))) = ι x
    rw [L.symm_apply_apply, h1, one_smul]
    exact Φ.toOpenPartialHomeomorph.right_inv hx.2
  have hcoords (y : ℂ) (hy : y ∈ ball (0 : ℂ) R) : P (ι (V y)) = z (e.symm y) := by
    have h1 : χ (ι (V y)) = 1 :=
      (interior_subset (s := {p : M | χ p = 1})) (hone y hy).1
    change L (χ (ι (V y)) • Φ.symm (ι (V y))) = z (e.symm y)
    rw [h1, one_smul]
    change L (Φ.symm (ι (V y))) = L (Φ.symm (v (e (b + e.symm y))))
    rw [hVeq y, map_add, e.apply_symm_apply]
  have hfCollar (y : ℂ) (hy : y ∈ S) : f (e.symm y) = P (ι (V y)) := by
    rw [hfz (by
      change e.symm y ∉ ball (0 : EuclideanSpace ℝ (Fin 2)) s
      simp only [mem_ball_zero_iff, e.symm.norm_map, not_lt]
      exact hsr.le.trans hy.1), hcoords y (hS hy)]
  obtain ⟨A, hA⟩ := hmin.isBoundedUnder_le.bddAbove_range
  have henergy (n : ℕ) : riemannianDiskEnergy g (u n) ≤ A := hA (mem_range_self n)
  have htranslated (n : ℕ) : (∫ y in S, diskMapEnergyDensity g (ι ∘ uX n) y) ≤ A := by
    have heq : (ι ∘ uX n) = fun y => diskExtension (u n) (e b + y) := funext (huX n)
    rw [heq]
    obtain ⟨C, hC⟩ := (hu n).2
    exact (integral_disk_energy_comp_add_le g (u n) hC
      (by simpa only [e.norm_map] using hbR) (hS.trans ball_subset_closedBall)).trans (henergy n)
  obtain ⟨ρ₀, hρ₀, σ, hσ, ε, hε, hcompare⟩ :=
    exists_original_energy_comparison_of_sobolev_collar_competitor g ι hι hPsmooth hPc
      hU hψ hK hKconv h0 hKsource hO hleft u hu hmin uX V (e b) huX huLip
      hr hrR₁ (by rw [e.norm_map]; linarith) (hV.mono hS) (fun y hy => hone y (hS hy))
      (fun y hy => by
        change P (ι (V y)) ∈ interior K
        rw [hcoords y (hS hy)]
        exact hzK _ (by simpa only [mem_ball_zero_iff, e.symm.norm_map] using hS hy))
      (ae_restrict_of_ae_restrict_of_subset hS huV) htranslated isOpen_ball hf hfK
      (closedBall_subset_ball hR₁R) hfCollar
  have hρpos : 0 < ρ₀ := hr.trans_le hρ₀.1
  have hρR : ρ₀ ≤ R := hρ₀.2.trans hR₁R.le
  have hAcont : ContinuousOn (pullbackMetricCoefficients g ψ) K :=
    (contDiffOn_pullback_metric_coefficients g hU hψ).continuousOn.mono hKsource
  have hls := translated_chart_energy_le_liminf_disk_energy g L Φ χ ρ hχ hχc hχsupport
    hρsmooth hρc hρnonneg hρle hρsupport (u ∘ σ) v (fun n => (hu (σ n)).2)
    (hae.mono fun y hy => hy.comp hσ.tendsto_atTop) (fun n => henergy (σ n)) hw b hbR
    hρone hz hρpos hρR
  let J := (1 / 2 : ℝ) * (∑ j : Fin 2,
    ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₀,
      pullbackMetricCoefficients g ψ (f x)
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))
  have hupper : Tendsto (fun n => J + ε n) atTop (𝓝 J) := by
    simpa only [add_zero] using hε.const_add J
  have hrawlo : IsBoundedUnder (· ≥ ·) atTop (fun n =>
      ∫ y in ball (e b) ρ₀, diskMapEnergyDensity g (diskExtension (u (σ n))) y) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ ∫ y in ball (e b) ρ₀,
      diskMapEnergyDensity g (diskExtension (u (σ n))) y
    exact Eventually.of_forall fun n => integral_nonneg fun y =>
      div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
        (by norm_num)
  have hrawle : ∀ᶠ n in atTop,
      (∫ y in ball (e b) ρ₀, diskMapEnergyDensity g (diskExtension (u (σ n))) y) ≤ J + ε n := by
    filter_upwards [hcompare] with n hn
    obtain ⟨C, hC⟩ := (hu (σ n)).2
    let : IsFiniteMeasure (volume.restrict (closedBall (e b) ρ₀)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (e b) ρ₀).measure_ne_top
    have hi := integrableOn_diskMapEnergyDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hC) (closedBall (e b) ρ₀) (μ := volume)
    exact (setIntegral_mono_set hi (Eventually.of_forall fun y =>
      div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
        (by norm_num)) (Eventually.of_forall ball_subset_closedBall)).trans hn
  have hclosed := hls.trans ((liminf_le_liminf hrawle hrawlo
    hupper.isCoboundedUnder_ge).trans_eq hupper.liminf_eq)
  have hrestrict : volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ₀) =
      volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₀) := by
    have hh := Measure.restrict_eq_self_of_ae_mem
      (ae_mem_ball_of_measure_sphere_eq_zero (Measure.addHaar_sphere volume
        (0 : EuclideanSpace ℝ (Fin 2)) ρ₀))
    rwa [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr ball_subset_closedBall] at hh
  have hleball : (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) ρ₀,
      pullbackMetricCoefficients g ψ (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) ρ₀,
        pullbackMetricCoefficients g ψ (f x)
          (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) := by
    simpa only [J, ← hrestrict] using hclosed
  have hfg : z =ᵐ[volume.restrict
      (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ₀ \ closedBall 0 s)] f := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_closedBall)] with x hx
    exact (hfz (notMem_subset ball_subset_closedBall hx.2)).symm
  have hle := quadratic_weakGrad_energy_le_on_ball_of_ae_eq_on_annulus hz hf hK hzKae hfK
    (pullbackMetricCoefficients g ψ) hAcont (hsr.le.trans hρ₀.1)
    (ball_subset_ball hρR) hfg hleball
  have hqeq : (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
      pullbackMetricCoefficients g ψ (f x)
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
        pullbackMetricCoefficients g ψ (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_all_iff.mpr hgradfq] with x hx hgrad
    have hG : (WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ (Fin m)) =
        WithLp.toLp 2 (fun i => (hq i).weakGrad x j) := by
      ext i
      exact congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y j) (hgrad i)
    rw [hfq hx, hG]
  rw [hqeq] at hle
  exact hle

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [PseudoMetricSpace X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_local_chart_minimality_in_centered_chart
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hιcont : Continuous ι)
    (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (uX : ℕ → ℂ → X) (V : ℂ → X)
    (huX : ∀ n y, ι (uX n y) = diskExtension (u n) y)
    (hV : ContinuousOn V (ball (0 : ℂ) 1))
    (huV : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => uX n y) atTop (𝓝 (V y)))
    (b : EuclideanSpace ℝ (Fin 2)) (hb : ‖b‖ < 1)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (hΦsource : (0 : E) ∈ Φ.source)
    (hΦcenter : Φ 0 = ι (V (Complex.orthonormalBasisOneI.repr.symm b))) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ‖b‖ + R < 1 ∧
        MapsTo L.symm (closedBall (0 : EuclideanSpace ℝ (Fin m)) a) Φ.source ∧
        let ψ := fun p => Φ (L.symm p)
        let z := fun x => L (Φ.symm (ι (V (e (b + x)))))
        MapsTo z (ball (0 : EuclideanSpace ℝ (Fin 2)) R) (ball 0 a) ∧
        ∃ hz : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball 0 R),
          ∀ (s : ℝ), 0 < s → s < R →
            ∀ (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
              (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball 0 s)),
              (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball 0 s)) →
              (∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) s),
                q x ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) a) →
              (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
                pullbackMetricCoefficients g ψ (z x)
                  (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
                  (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
                (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
                  pullbackMetricCoefficients g ψ (q x)
                    (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
                    (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  let v : ℂ → M := ι ∘ V
  have hv : ContinuousOn v (ball (0 : ℂ) 1) := hιcont.comp_continuousOn hV
  have hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (v y)) := by
    filter_upwards [huV] with y hy
    have h : Tendsto (fun n => ι (uX n y)) atTop (𝓝 (ι (V y))) :=
      (hιcont.tendsto (V y)).comp hy
    simpa only [huX, v, Function.comp_apply] using h
  obtain ⟨A, hA⟩ := hmin.isBoundedUnder_le.bddAbove_range
  have henergy (n : ℕ) : riemannianDiskEnergy g (u n) ≤ A := hA (mem_range_self n)
  obtain ⟨χ, ρ, hχsupport, hρsupport, hw, a, R, ha, hR, hbR, hKsource, hρone, hzball⟩ :=
    exists_centered_chart_cutoffs_of_continuous_ae_limit g L Φ hΦsource
      u v (fun n => (hu n).2) hae henergy hv b hb hΦcenter
  have hρone' (x) (hx : x ∈ ball b R) : ρ (v (e x)) = 1 :=
    hρone (ball_subset_closedBall hx)
  have hχone (x) (hx : x ∈ ball b R) : χ (v (e x)) = 1 := by
    have hne : ρ (v (e x)) ≠ 0 := by rw [hρone' x hx]; exact one_ne_zero
    exact (interior_subset (s := {p : M | χ p = 1})) (hρsupport (subset_tsupport _ hne)).1
  have hball : ball b R ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x hx
    have hn : ‖x‖ ≤ dist x b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - b) b
    exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  have heq : EqOn (fun x => L (χ (v (e x)) • Φ.symm (v (e x))))
      (fun x => L (Φ.symm (v (e x)))) (ball b R) := by
    intro x hx
    change L (χ (v (e x)) • Φ.symm (v (e x))) = L (Φ.symm (v (e x)))
    rw [hχone x hx, one_smul]
  obtain ⟨hz, _⟩ := exists_translated_memW1pWitness_of_eqOn hw hball heq
  let z := fun x => L (Φ.symm (v (e (b + x))))
  have hzK (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R) : z x ∈ ball 0 a := by
    apply hzball
    apply ball_subset_closedBall
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
  let UX : ℕ → ℂ → X := fun n y => uX n (e b + y)
  let VX : ℂ → X := fun y => V (e b + y)
  have hmap : MapsTo (fun y : ℂ => e b + y) (ball (0 : ℂ) R) (ball (0 : ℂ) 1) := by
    intro y hy
    have hyn := mem_ball_zero_iff.mp hy
    exact mem_ball_zero_iff.mpr ((norm_add_le (e b) y).trans_lt (by rw [e.norm_map]; linarith))
  have hVX : ContinuousOn VX (ball (0 : ℂ) R) :=
    hV.comp (continuous_const.add continuous_id).continuousOn hmap
  have hUXLip (n : ℕ) : ∃ C : ℝ≥0, LipschitzWith C (UX n) := by
    obtain ⟨C, hC⟩ := (hu n).2
    refine ⟨C, fun y y' => ?_⟩
    rw [hι, huX, huX]
    exact (diskExtension_riemannian_lipschitz g hC (e b + y) (e b + y')).trans_eq (by
      rw [edist_add_left])
  have hUXae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) R),
      Tendsto (fun n => UX n y) atTop (𝓝 (VX y)) := by
    have hm := (measurePreserving_add_left (volume : Measure ℂ) (e b)).quasiMeasurePreserving
    exact (hm.restrict hmap).ae huV
  refine ⟨a, R, ha, hR, hbR, hKsource, hzK, hz, ?_⟩
  intro s hs hsR q hq hqz hqK
  exact local_chart_energy_le_of_memW01p_sub g ι hιcont hι L Φ χ ρ
    χ.contMDiff χ.hasCompactSupport hχsupport ρ.contMDiff ρ.hasCompactSupport
    (fun _ => ρ.nonneg) (fun _ => ρ.le_one) hρsupport γ u v hu hmin hae hw b hbR
    hρone' UX VX (fun n y => huX n (e b + y)) (fun _ => rfl) hUXLip hVX hUXae
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) a) (convex_closedBall 0 a)
    (mem_closedBall_self ha.le) hKsource
    (fun x hx => (interior_maximal ball_subset_closedBall isOpen_ball) (hzK x hx))
    hz hs hsR q hq hqz hqK

end DifferentialGeometry.Geometry

end

end

section

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
theorem exists_local_chart_minimality_in_centered_chart_of_component_limit
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hV : ContinuousOn V (ball (0 : ℂ) 1))
    (hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (V y : M)))
    (b : EuclideanSpace ℝ (Fin 2)) (hb : ‖b‖ < 1)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (hΦsource : (0 : E) ∈ Φ.source)
    (hΦcenter : Φ 0 = (V (Complex.orthonormalBasisOneI.repr.symm b) : M)) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ‖b‖ + R < 1 ∧
        MapsTo L.symm (closedBall (0 : EuclideanSpace ℝ (Fin m)) a) Φ.source ∧
        let ψ := fun p => Φ (L.symm p)
        let z := fun x => L (Φ.symm (V (e (b + x)) : M))
        MapsTo z (ball (0 : EuclideanSpace ℝ (Fin 2)) R) (ball 0 a) ∧
        ∃ hz : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball 0 R),
          ∀ (s : ℝ), 0 < s → s < R →
            ∀ (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
              (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball 0 s)),
              (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball 0 s)) →
              (∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) s),
                q x ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) a) →
              (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
                pullbackMetricCoefficients g ψ (z x)
                  (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
                  (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
                (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) s,
                  pullbackMetricCoefficients g ψ (q x)
                    (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
                    (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) := by
  classical
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  let : IsManifold 𝓘(ℝ, E) 1 C := IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) := ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : EMetricSpace C := eC
  let mC : MetricSpace C := EMetricSpace.toMetricSpace
    (fun x y : C => DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)
  let : MetricSpace C := mC
  have hdist (x y : C) : edist x y = riemannianEDistOf g (x : M) (y : M) :=
    Metric.edistOf_restrictOpen_connCompOpen g (γ 0) x y
  have htrace (n : ℕ) : ∃ τ : C(loopCircle, loopCircle), diskTrace (u n) = γ.comp τ := by
    obtain ⟨τ, _, hτ⟩ := (hu n).1
    exact ⟨τ, hτ⟩
  choose τ hτ using htrace
  let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (τ n) (u n) (hτ n)
  let uX : ℕ → ℂ → C := fun n => diskExtension (uC n)
  have hUX (n : ℕ) (y : ℂ) : (uX n y : M) = diskExtension (u n) y := rfl
  have huV : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => uX n y) atTop (𝓝 (V y)) := by
    filter_upwards [hae] with y hy
    apply tendsto_subtype_rng.mpr
    exact hy
  exact exists_local_chart_minimality_in_centered_chart
    g (Subtype.val : C → M) continuous_subtype_val hdist L γ u hu hmin uX V hUX hV huV b hb
    Φ hΦsource hΦcenter

end DifferentialGeometry.Geometry

end

end
