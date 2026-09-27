import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.EmbeddedSequence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Complex
import DifferentialGeometry.Analysis.Sobolev.Euclidean.TargetApproximation.Energy
import DifferentialGeometry.Analysis.Integration.Lp.StrongConvergence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakLocalComparison
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundedDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ZeroExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Integrability

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem integrable_quadratic_weakGrad_column
    {ι : Type*} [Finite ι] {Ω : Set V}
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ]
      EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : ContinuousOn A K)
    {f : V → EuclideanSpace ℝ ι}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K) (j : Fin 2) :
    IntegrableOn (fun x => A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) Ω := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hAm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hm : AEStronglyMeasurable (fun x => A (f x)) (volume.restrict Ω) := by
    apply (hAm.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [hfK] with x hx
    exact Set.piecewise_eq_of_mem K A 0 hx
  have hn : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hn
  have hb : ∀ᵐ x ∂volume.restrict Ω, ‖A (f x)‖ ≤ C :=
    hfK.mono fun x hx => hC (mem_image_of_mem _ hx)
  have hG : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2
      (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x))
    (fun a b => (hm.apply_continuousLinearMap a).apply_continuousLinearMap b) hb hG hG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem weak_replacement_energy_le_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) (hc1 : c < 1)
    (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 c))
    (hqK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) c), q x ∈ range Φ)
    (hqw : q =ᵐ[volume.restrict (Metric.ball (0 : V) c \ Metric.closedBall 0 a)] w) :
    (∑ j : Fin 2, ∫ x in Metric.closedBall (0 : V) a,
      pullbackMetricCoefficients g r (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.closedBall (0 : V) a,
        pullbackMetricCoefficients g r (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
  classical
  let b : ℝ := (a + c) / 2
  have hab : a < b := by dsimp only [b]; linarith
  have hbc : b < c := by dsimp only [b]; linarith
  let e := Complex.orthonormalBasisOneI.repr
  let un (n : ℕ) : ℂ → F := Φ ∘ diskExtension (u n)
  let K := range Φ
  let A := pullbackMetricCoefficients g r
  have hK : IsCompact K := isCompact_range hΦ.continuous
  have hA : ContinuousOn A K :=
    (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn.mono hΦU
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ K :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hb1 : b < 1 := hbc.trans hc1
  have hbpos : 0 < b := ha.trans hab
  have hballbc : Metric.closedBall (0 : V) b ⊆ Metric.ball (0 : V) c :=
    Metric.closedBall_subset_ball hbc
  have hballb1 : Metric.closedBall (0 : V) b ⊆ Metric.ball (0 : V) 1 :=
    Metric.closedBall_subset_ball hb1
  have hcball1 : Metric.ball (0 : V) c ⊆ Metric.ball (0 : V) 1 :=
    Metric.ball_subset_ball hc1.le
  have hret : ContDiffOn ℝ ∞ (Φ ∘ r) U := (hΦ.comp_contMDiffOn hr).contDiffOn
  have hretK : MapsTo (Φ ∘ r) U K := fun y _ => mem_range_self _
  have hretfix : ∀ y ∈ K, (Φ ∘ r) y = y := by
    rintro y ⟨p, rfl⟩
    exact congrArg Φ (hleft p)
  obtain ⟨Vt, T, L, hVt, hKVt, _, _, hT, _, _, hTL, hTK, hTfix⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound
      hK hU hΦU (Φ ∘ r) hret hretK hretfix
  obtain ⟨Ku, τ, Bu, _, huLip, huK, hτ, htrace, huInt, huBound, _, _, huMin⟩ :=
    exists_embedded_minimizing_sequence_bounds g (hΦ.of_le (by simp)) hU
      (hr.of_le (by simp)) hΦU hleft u hu hmin
  obtain ⟨vn, Kv, Bv, _, hvLip, hvSmooth, hvK, hvL2, hvDer, hvae, hvBound, _⟩ :=
    exists_lipschitz_complex_target_approximation_tendsto_energy_on_ball
      hK hU hΦU (Φ ∘ r) hret hretK hretfix Metric.isOpen_ball hq hqK hballbc A hA
  obtain ⟨Gu, G₀, hGu, hG₀, hGuWeak⟩ :=
    exists_complex_lp_gradient_columns_of_tendsto_inner hballb1 un w hs hw Ku huLip hrep hweak
  let Gq (j : Fin 2) (x : V) : F := WithLp.toLp 2 (fun i => (hq i).weakGrad x j)
  have hGqm (j : Fin 2) : MemLp (Gq j) 2 (volume.restrict (Metric.closedBall (0 : V) b)) :=
    MemLp.of_eval_piLp fun i => ((hq i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hballbc)
  have hGqC (j : Fin 2) : MemLp (Gq j ∘ e) 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (hGqm j).comp_measurePreserving (measurePreserving_complex_plane_repr_closedBall b)
  let H₀ (j : Fin 2) : Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (hGqC j).toLp (Gq j ∘ e)
  have hH₀ (j : Fin 2) : (H₀ j : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
      (Gq j ∘ e) := (hGqC j).coeFn_toLp
  obtain ⟨Hv, hHv, hHvStrong⟩ := exists_complex_lp_columns_tendsto_of_tendsto_eLpNorm
    vn (fun j => Gq j ∘ e) Kv hvLip b H₀ hH₀ hvDer
  have hwm : MemLp w 2 (volume.restrict (Metric.ball (0 : V) 1)) :=
    MemLp.of_eval_piLp fun i => (hw i).memLp
  have hqm : MemLp q 2 (volume.restrict (Metric.ball (0 : V) c)) :=
    MemLp.of_eval_piLp fun i => (hq i).memLp
  have hwCm : MemLp (w ∘ e) 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (hwm.mono_measure (Measure.restrict_mono_set volume hballb1)).comp_measurePreserving
      (measurePreserving_complex_plane_repr_closedBall b)
  have hqCm : MemLp (q ∘ e) 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (hqm.mono_measure (Measure.restrict_mono_set volume hballbc)).comp_measurePreserving
      (measurePreserving_complex_plane_repr_closedBall b)
  have hunm (n : ℕ) : MemLp (un n) 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (huLip n).continuous.continuousOn.memLp_restrict_compact (isCompact_closedBall _ _) 2
  have hvnm (n : ℕ) : MemLp (vn n) 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
    (hvLip n).continuous.continuousOn.memLp_restrict_compact (isCompact_closedBall _ _) 2
  have huL2C : Tendsto (fun n => eLpNorm (fun z => un n z - w (e z)) 2
      (volume.restrict (Metric.closedBall (0 : ℂ) b))) atTop (𝓝 0) := by
    have hlocal : Tendsto (fun n => eLpNorm (fun x =>
        Φ (diskExtension (u n) (e.symm x)) - w x) 2
        (volume.restrict (Metric.ball (0 : V) b))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
        (fun _ => zero_le) (fun n => eLpNorm_mono_measure _
          (Measure.restrict_mono_set volume (Metric.ball_subset_ball hb1.le)))
    have heq (n : ℕ) : eLpNorm (fun z => un n z - w (e z)) 2
        (volume.restrict (Metric.ball (0 : ℂ) b)) =
        eLpNorm (fun x => Φ (diskExtension (u n) (e.symm x)) - w x) 2
          (volume.restrict (Metric.ball (0 : V) b)) := by
      simpa only [Function.comp_def, e, LinearIsometryEquiv.symm_apply_apply, un] using
        eLpNorm_comp_complex_plane_repr_ball
          (fun x => Φ (diskExtension (u n) (e.symm x)) - w x) 2 b
    rw [← restrict_ball_eq_restrict_closedBall_complex b]
    simpa only [heq] using hlocal
  have hvL2C : Tendsto (fun n => eLpNorm (fun z => vn n z - q (e z)) 2
      (volume.restrict (Metric.closedBall (0 : ℂ) b))) atTop (𝓝 0) := by
    rw [← restrict_ball_eq_restrict_closedBall_complex b]
    exact hvL2
  have huAec : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b),
      Tendsto (fun n => un n z) atTop (𝓝 (w (e z))) := by
    have h := (measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae
      (ae_mono (Measure.restrict_mono_set volume hballb1) hae)
    simpa only [un, Function.comp_apply, e, LinearIsometryEquiv.symm_apply_apply] using h
  have hvAec : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b),
      Tendsto (fun n => vn n z) atTop (𝓝 (q (e z))) := by
    rw [← restrict_ball_eq_restrict_closedBall_complex b]
    exact hvae
  have hwKc : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b), w (e z) ∈ K :=
    (measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae
      (ae_mono (Measure.restrict_mono_set volume hballb1) hwK)
  have hqKc : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b), q (e z) ∈ K :=
    (measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae
      (ae_mono (Measure.restrict_mono_set volume hballbc) hqK)
  let a' : ℝ := (a + b) / 2
  have haa' : a < a' := by dsimp only [a']; linarith
  have ha'b : a' < b := by dsimp only [a']; linarith
  let S : Set ℂ := {z | ‖z‖ ∈ Icc a' b}
  have hSb : S ⊆ Metric.closedBall (0 : ℂ) b := fun z hz => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
  have hS1 : S ⊆ Metric.closedBall (0 : ℂ) 1 :=
    hSb.trans (Metric.closedBall_subset_closedBall hb1.le)
  have hmaps : MapsTo e S (Metric.ball (0 : V) c \ Metric.closedBall 0 a) := by
    intro z hz
    constructor
    · simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz.2.trans_lt hbc
    · simp only [Metric.mem_closedBall, dist_zero_right, e.norm_map, not_le]
      exact haa'.trans_le hz.1
  have hweq : (w ∘ e) =ᵐ[volume.restrict S] (q ∘ e) :=
    (e.measurePreserving.quasiMeasurePreserving.restrict hmaps).ae hqw.symm
  have hgap : Tendsto (fun n => ∫ z in S, ‖un n z - vn n z‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
      (Measure.restrict_mono_set volume hSb) un vn (w ∘ e) (q ∘ e) hunm hvnm
      hwCm.aestronglyMeasurable hqCm.aestronglyMeasurable huL2C hvL2C hweq
  have hvInt (n : ℕ) : IntegrableOn (fun z => ‖fderiv ℝ (vn n) z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) b) := by
    let μ := volume.restrict (Metric.closedBall (0 : ℂ) b)
    let _ : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
    have hm : MemLp (fun z => ‖fderiv ℝ (vn n) z‖) 2 μ := by
      apply MemLp.of_bound (measurable_fderiv ℝ (vn n)).norm.aestronglyMeasurable (Kv n)
      exact Eventually.of_forall fun z => by
        simpa only [norm_norm] using norm_fderiv_le_of_lipschitz ℝ (hvLip n) (x₀ := z)
    exact hm.integrable_sq
  have henergy (n : ℕ) : (∫ z in S, ‖fderiv ℝ (un n) z‖ ^ 2 +
      ‖fderiv ℝ (vn n) z‖ ^ 2) ≤ Bu + Bv := by
    rw [integral_add ((huInt n).mono_set hS1) ((hvInt n).mono_set hSb)]
    apply add_le_add
    · exact (setIntegral_mono_set (huInt n) (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hS1)).trans (huBound n)
    · have hbnd := hvBound n
      rw [restrict_ball_eq_restrict_closedBall_complex b] at hbnd
      exact (setIntegral_mono_set (hvInt n) (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hSb)).trans hbnd
  obtain ⟨ρ, hρ, hcomp⟩ := exists_pullback_quadratic_weak_limit_comparison
    g hΦ.continuous hU hr hΦU hleft τ hτ un vn Ku Kv huLip hvLip
    (ha.trans haa') ha'b hb1.le huK hvK htrace hgap henergy hVt hKVt T
    (hT.differentiable (by simp)) hTL hTK hTfix huMin (w ∘ e) (q ∘ e)
    huAec hvAec hwKc hqKc Gu Hv G₀ H₀
    (by simpa only [Complex.coe_orthonormalBasisOneI] using hGu)
    (by simpa only [Complex.coe_orthonormalBasisOneI] using hHv) hGuWeak hHvStrong
  have haρ : a ≤ ρ := haa'.le.trans hρ.1
  have hρc : ρ < c := hρ.2.trans_lt hbc
  have hρ1 : ρ < 1 := hρc.trans hc1
  have hrestrictb : volume.restrict (Metric.closedBall (0 : ℂ) ρ) ≤
      volume.restrict (Metric.closedBall (0 : ℂ) b) :=
    Measure.restrict_mono_set volume (Metric.closedBall_subset_closedBall hρ.2)
  have heqW (j : Fin 2) :
      (∫ z in Metric.closedBall (0 : ℂ) ρ, A (w (e z)) (G₀ j z) (G₀ j z)) =
        ∫ x in Metric.closedBall (0 : V) ρ, A (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
    trans ∫ z in Metric.closedBall (0 : ℂ) ρ, A (w (e z))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad (e z) j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad (e z) j))
    · apply integral_congr_ae
      filter_upwards [ae_mono hrestrictb (hG₀ j)] with z hz
      rw [hz]
    · exact (measurePreserving_complex_plane_repr_closedBall ρ).integral_comp
        e.toMeasurableEquiv.measurableEmbedding (fun x => A (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)))
  have heqQ (j : Fin 2) :
      (∫ z in Metric.closedBall (0 : ℂ) ρ, A (q (e z)) (H₀ j z) (H₀ j z)) =
        ∫ x in Metric.closedBall (0 : V) ρ, A (q x) (Gq j x) (Gq j x) := by
    trans ∫ z in Metric.closedBall (0 : ℂ) ρ, A (q (e z)) (Gq j (e z)) (Gq j (e z))
    · apply integral_congr_ae
      filter_upwards [ae_mono hrestrictb (hH₀ j)] with z hz
      simp only [hz, Function.comp_apply]
    · exact (measurePreserving_complex_plane_repr_closedBall ρ).integral_comp
        e.toMeasurableEquiv.measurableEmbedding (fun x => A (q x) (Gq j x) (Gq j x))
  change (∑ j, ∫ z in Metric.closedBall (0 : ℂ) ρ, A (w (e z)) (G₀ j z) (G₀ j z)) ≤
    ∑ j, ∫ z in Metric.closedBall (0 : ℂ) ρ, A (q (e z)) (H₀ j z) (H₀ j z) at hcomp
  simp_rw [heqW, heqQ] at hcomp
  let hwc (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball (0 : V) c) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hcball1 (hw i)
  exact sum_integral_quadratic_weakGrad_closedBall_le_of_ae_eq_on_collar
    (by norm_num) Metric.isOpen_ball hwc hq (fun _ y => A y) haρ
    (Metric.closedBall_subset_ball hρc) hqw.symm
    (fun j => (integrable_quadratic_weakGrad_column hK A hA hw hwK j).mono_set
      (Metric.closedBall_subset_ball hρ1))
    (fun j => (integrable_quadratic_weakGrad_column hK A hA hq hqK j).mono_set
      (Metric.closedBall_subset_ball hρc)) hcomp

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem weak_replacement_energy_le_on_interior_ball_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    {b : V} {a c : ℝ} (ha : 0 < a) (hac : a < c) (hbc : ‖b‖ + c < 1)
    (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball b c))
    (hqK : ∀ᵐ x ∂volume.restrict (Metric.ball b c), q x ∈ range Φ)
    (hqw : q =ᵐ[volume.restrict (Metric.ball b c \ Metric.closedBall b a)] w) :
    (∑ j : Fin 2, ∫ x in Metric.closedBall b a,
      pullbackMetricCoefficients g r (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.closedBall b a,
        pullbackMetricCoefficients g r (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
  have hball : Metric.ball b c ⊆ Metric.ball (0 : V) 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x - b‖ < c := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (x - b) b
    linarith
  obtain ⟨v, ⟨hv⟩, hvq, hvw⟩ := exists_weak_extension_of_eq_on_collar
    Metric.isOpen_ball ha.le hac hball hw hq hqw
  let K := range Φ
  let A := pullbackMetricCoefficients g r
  have hK : IsCompact K := isCompact_range hΦ.continuous
  have hA : ContinuousOn A K :=
    (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn.mono hΦU
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ K :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hvK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), v x ∈ K := by
    have hqae := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hqK
    have hveq := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hvq
    have hvweq := (ae_restrict_iff' (Metric.isOpen_ball.measurableSet.diff
      Metric.isClosed_closedBall.measurableSet)).mp hvw
    filter_upwards [hwK, ae_restrict_mem Metric.isOpen_ball.measurableSet,
      ae_restrict_of_ae hqae, ae_restrict_of_ae hveq, ae_restrict_of_ae hvweq]
      with x hxK hx hxq hxvq hxvw
    by_cases hxc : x ∈ Metric.ball b c
    · rw [hxvq hxc]
      exact hxq hxc
    · rw [hxvw ⟨hx, fun hxa => hxc (Metric.closedBall_subset_ball hac hxa)⟩]
      exact hxK
  let a₀ := (‖b‖ + c + 1) / 2
  let c₀ := (a₀ + 1) / 2
  have hca₀ : ‖b‖ + c < a₀ := by dsimp only [a₀]; linarith
  have ha₀1 : a₀ < 1 := by dsimp only [a₀]; linarith
  have ha₀ : 0 < a₀ := by
    have hc := ha.trans hac
    have hn := norm_nonneg b
    dsimp only [a₀]
    linarith
  have ha₀c₀ : a₀ < c₀ := by dsimp only [c₀]; linarith
  have hc₀1 : c₀ < 1 := by dsimp only [c₀]; linarith
  have hinner : Metric.closedBall b a ⊆ Metric.closedBall (0 : V) a₀ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x - b‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (x - b) b
    linarith
  let hv₀ (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball
    (Metric.ball_subset_ball hc₀1.le) (hv i)
  have hvw₀ : v =ᵐ[volume.restrict
      (Metric.ball (0 : V) c₀ \ Metric.closedBall 0 a₀)] w :=
    ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff
      (Metric.ball_subset_ball hc₀1.le) hinner) hvw
  have hcomp := weak_replacement_energy_le_of_disk_energy_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha₀ ha₀c₀ hc₀1 v hv₀
    (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hc₀1.le) hvK) hvw₀
  let ew := fun x => ∑ j : Fin 2, A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
  let ev := fun x => ∑ j : Fin 2, A (v x)
    (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
  have hiw (j : Fin 2) := integrable_quadratic_weakGrad_column hK A hA hw hwK j
  have hiv (j : Fin 2) := integrable_quadratic_weakGrad_column hK A hA hv hvK j
  have houter : Metric.closedBall (0 : V) a₀ ⊆ Metric.ball (0 : V) 1 :=
    Metric.closedBall_subset_ball ha₀1
  have hiw₀ : IntegrableOn ew (Metric.closedBall (0 : V) a₀) :=
    (integrable_sum_quadratic_weakGrad hw hK A hA hwK).mono_set houter
  have hiv₀ : IntegrableOn ev (Metric.closedBall (0 : V) a₀) :=
    (integrable_sum_quadratic_weakGrad hv hK A hA hvK).mono_set houter
  have hcomp' : (∫ x in Metric.closedBall (0 : V) a₀, ew x) ≤
      ∫ x in Metric.closedBall (0 : V) a₀, ev x := by
    rw [integral_finsetSum _ (fun j _ => (hiw j).mono_set houter),
      integral_finsetSum _ (fun j _ => (hiv j).mono_set houter)]
    exact hcomp
  have hcoll := quadratic_weakGrad_columns_ae_eq_of_ae_eq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall) sdiff_subset
    hw hv hvw.symm (fun _ y => A y)
  have hsum : ew =ᵐ[volume.restrict
      (Metric.closedBall (0 : V) a₀ \ Metric.closedBall b a)] ev :=
    (ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff_left houter) hcoll).mono
      fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hsmall := setIntegral_le_of_ae_eq_on_sdiff Metric.isClosed_closedBall.measurableSet
    hinner hiw₀ hiv₀ hsum hcomp'
  let hvB (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hball (hv i)
  have heq := quadratic_weakGrad_columns_ae_eq_of_ae_eq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) Metric.isOpen_ball (Subset.rfl)
    hvB hq hvq (fun _ y => A y)
  have heq' : (∫ x in Metric.closedBall b a, ev x) =
      ∑ j : Fin 2, ∫ x in Metric.closedBall b a, A (q x)
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
    rw [integral_finsetSum _ (fun j _ => (hiv j).mono_set (hinner.trans houter))]
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    exact (ae_restrict_of_ae_restrict_of_subset (Metric.closedBall_subset_ball hac) heq).mono
      fun x hx => hx j
  rw [heq', integral_finsetSum _ (fun j _ => (hiw j).mono_set (hinner.trans houter))] at hsmall
  exact hsmall

end DifferentialGeometry.Geometry

end
