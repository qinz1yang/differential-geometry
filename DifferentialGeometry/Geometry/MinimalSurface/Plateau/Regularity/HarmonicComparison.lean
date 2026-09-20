import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.HarmonicReplacement
import DifferentialGeometry.Geometry.HarmonicMap.WeakCoordinates
import DifferentialGeometry.Geometry.Metric.Pullback.Chart
import DifferentialGeometry.Geometry.HarmonicMap.ChartCoercivity
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_harmonic_replacement_comparison_with_coefficient_oscillation
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    {ε : ℝ} (hε : 0 < ε) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    let Ψ : H → M := fun y =>
      (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + z₀))
    let B := pullbackMetricCoefficients g Ψ
    ∃ ρ τ : ℝ, 0 < ρ ∧ 0 < τ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      (∀ y : H, (∀ k, |y k| ≤ τ) → y + z₀ ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p) ∧
      (∀ y : H, (∀ k, |y k| ≤ τ) → ‖B y - B 0‖ ≤ ε) ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ, ∀ k, |z x k| ≤ τ) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball x₀ ρ), ∀ j : Fin 2,
          pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) =
          B (z x) (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
            (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))) ∧
        ∀ (b : V) (a : ℝ), 0 < a → ‖b‖ + a < 1 → Metric.ball b a ⊆ Metric.ball x₀ ρ →
          ∃ (h : V → H) (hh : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => h x k) (Metric.ball b a)),
            (∀ k, DeGiorgi.MemW01p 2 (fun x => h x k - z x k) (Metric.ball b a)) ∧
            (∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |h x k| ≤ τ) ∧
            (∀ k (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
              (∫ x in Metric.ball b a, inner ℝ ((hh k).weakGrad x)
                (DeGiorgi.smoothGradField φ x)) = 0) ∧
            (∑ k, ∫ x in Metric.ball b a, ‖(hh k).weakGrad x‖ ^ 2) ≤
              (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2) ∧
            (∑ j : Fin 2, ∫ x in Metric.ball b a, pullbackMetricCoefficients g r (w x)
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
              ∑ j : Fin 2, ∫ x in Metric.ball b a, B (h x)
                (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))
                (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
  classical
  obtain ⟨r₀, hr₀, hball₀, hrmap, hzmap, hzc, hzback, hz₀, hzgrad⟩ :=
    exists_weak_chart_coordinates_of_continuousOn Metric.isOpen_ball hvc hv hU hr
      (fun x hx => hΦU (hvK hx)) hx₀
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z₀ := χ (v x₀)
  let z : V → H := fun x => χ (v x) - z₀
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen (I := 𝓘(ℝ, E)) p
  have hz₀U : z₀ ∈ Uc := hzmap (Metric.mem_closedBall_self hr₀.le)
  let Ψ₀ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let Ψ : H → M := fun y => Ψ₀ (y + z₀)
  let β : H → F := Φ ∘ Ψ
  let Ushift := (fun y : H => y + z₀) ⁻¹' Uc
  have hUshift : IsOpen Ushift := hUc.preimage (continuous_id.add continuous_const)
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  have hΨ₀ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ₀ Uc :=
    chart.contMDiffOn_invFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun y hy => toEuclidean_symm_mem_target hy)
  have hBcont : ContinuousOn (pullbackMetricCoefficients g Ψ₀) Uc :=
    (contDiffOn_pullback_metric_coefficients g hUc hΨ₀).continuousOn
  have hBAt := hBcont.continuousAt (hUc.mem_nhds hz₀U)
  have hnear : Uc ∩ {y : H | ‖pullbackMetricCoefficients g Ψ₀ y -
      pullbackMetricCoefficients g Ψ₀ z₀‖ < ε} ∈ 𝓝 z₀ := by
    have hballCoeff : Metric.ball (pullbackMetricCoefficients g Ψ₀ z₀) ε ∈
        𝓝 (pullbackMetricCoefficients g Ψ₀ z₀) :=
      Metric.ball_mem_nhds (pullbackMetricCoefficients g Ψ₀ z₀) hε
    have hh := hBAt.preimage_mem_nhds hballCoeff
    apply inter_mem (hUc.mem_nhds hz₀U)
    have heq : (pullbackMetricCoefficients g Ψ₀) ⁻¹'
        Metric.ball (pullbackMetricCoefficients g Ψ₀ z₀) ε =
        {y | ‖pullbackMetricCoefficients g Ψ₀ y - pullbackMetricCoefficients g Ψ₀ z₀‖ < ε} := by
      ext y
      change dist (pullbackMetricCoefficients g Ψ₀ y) (pullbackMetricCoefficients g Ψ₀ z₀) < ε ↔ _
      rw [dist_eq_norm (pullbackMetricCoefficients g Ψ₀ y) (pullbackMetricCoefficients g Ψ₀ z₀)]
      rfl
    rwa [heq] at hh
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hnear
  let n : ℝ := Module.finrank ℝ E
  let τ : ℝ := η / (n + 1)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hτ : 0 < τ := div_pos hη (by linarith)
  have hboxNear : ∀ y : H, (∀ k, |y k| ≤ τ) →
      y + z₀ ∈ Uc ∧ ‖pullbackMetricCoefficients g Ψ₀ (y + z₀) -
        pullbackMetricCoefficients g Ψ₀ z₀‖ < ε := by
    intro y hy
    apply hηsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
    have heq : (∑ k, EuclideanSpace.single k (y k)) = y := by ext; simp
    have hy' : ‖y‖ ≤ n * τ := by
      calc
        ‖y‖ = ‖∑ k, EuclideanSpace.single k (y k)‖ := by rw [heq]
        _ ≤ ∑ k, ‖EuclideanSpace.single k (y k)‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin (Module.finrank ℝ E), τ := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [PiLp.norm_single, Real.norm_eq_abs] using hy k
        _ = n * τ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rfl
    have hτeq : (n + 1) * τ = η := by dsimp only [τ]; field_simp
    linarith
  have hbox : ∀ y : H, (∀ k, |y k| ≤ τ) → y + z₀ ∈ Uc :=
    fun y hy => (hboxNear y hy).1
  have hshiftCoeff (y : H) (hy : y + z₀ ∈ Uc) :
      pullbackMetricCoefficients g Ψ y = pullbackMetricCoefficients g Ψ₀ (y + z₀) := by
    ext v₁ v₂
    have hh := pullbackMetricCoefficients_fderiv_of_eventuallyEq
      (f := fun z : H => z + z₀) (ψ := Ψ₀) (r := Ψ) (x := y) g
      (by fun_prop) ((hΨ₀.contMDiffAt (hUc.mem_nhds hy)).mdifferentiableAt (by simp))
      (Eventually.of_forall fun z => rfl) v₁ v₂
    simpa only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] using hh.symm
  have hBclose : ∀ y : H, (∀ k, |y k| ≤ τ) →
      ‖pullbackMetricCoefficients g Ψ y - pullbackMetricCoefficients g Ψ 0‖ ≤ ε := by
    intro y hy
    have hzero : (0 : H) + z₀ ∈ Uc := by simpa only [zero_add] using hz₀U
    rw [hshiftCoeff y (hbox y hy), hshiftCoeff 0 hzero, zero_add]
    exact (hboxNear y hy).2.le
  have hzcont : ContinuousOn z (Metric.closedBall x₀ r₀) := hzc.sub continuousOn_const
  have hzcenter : z x₀ = 0 := sub_self _
  have hopen : IsOpen (Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ) :=
    (hzcont.mono Metric.ball_subset_closedBall).isOpen_inter_preimage
      Metric.isOpen_ball Metric.isOpen_ball
  have hxopen : x₀ ∈ Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ := by
    exact ⟨Metric.mem_ball_self hr₀, by rw [mem_preimage, hzcenter]; exact Metric.mem_ball_self hτ⟩
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxopen)
  let ρ := ρ₀ / 2
  have hρ : 0 < ρ := half_pos hρ₀
  have hρsub : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ :=
    (Metric.closedBall_subset_ball (half_lt_self hρ₀)).trans hρ₀sub
  have hρr : Metric.ball x₀ ρ ⊆ Metric.ball x₀ r₀ :=
    fun x hx => (hρsub (Metric.ball_subset_closedBall hx)).1
  have hρB : Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 :=
    fun x hx => hball₀ (Metric.ball_subset_closedBall (hρsub hx).1)
  have hzbound : ∀ x ∈ Metric.closedBall x₀ ρ, ∀ k, |z x k| ≤ τ := by
    intro x hx k
    have hh : ‖z x‖ < τ := by
      simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using (hρsub hx).2
    have hcol : |z x k| ≤ ‖z x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (z x) k
    exact hcol.trans hh.le
  let _ : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let hz (k : Fin (Module.finrank ℝ E)) :=
    (DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hρr (hz₀ k)).subConst
      Metric.isOpen_ball (z₀ k)
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ Ushift :=
    hΨ₀.comp ((contDiff_id.add contDiff_const).contMDiff.contMDiffOn) (fun _ hy => hy)
  have hβ : ContDiffOn ℝ ∞ β Ushift := (hΦ.comp_contMDiffOn hΨ).contDiffOn
  refine ⟨ρ, τ, hρ, hτ, hρB, hbox, hBclose, hzcont.mono ?_, hzbound, hz, ?_, ?_, ?_⟩
  · exact fun x hx => Metric.ball_subset_closedBall (hρsub hx).1
  · intro x hx j
    exact hzgrad x (hρr hx) j
  · have hvwa : v =ᵐ[volume.restrict (Metric.ball x₀ ρ)] w :=
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hρB) hvw
    have hGvw := weakGrad_columns_ae_eq_of_ae_eq (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hρB) hv hw hvwa
    filter_upwards [hvwa, hGvw, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hGx hxρ
    intro j
    have hxB := hρB (Metric.ball_subset_closedBall hxρ)
    have hxR := Metric.ball_subset_closedBall (hρr hxρ)
    have hchart := pullbackMetricCoefficients_chart_fderiv g p hU hr
      ⟨hΦU (hvK hxB), hrmap hxR⟩
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
    have hzU : z x + z₀ ∈ Uc := by
      simpa only [z, sub_add_cancel, χ, p, Function.comp_def, Uc] using hzmap hxR
    have hshift := pullbackMetricCoefficients_fderiv_of_eventuallyEq
      (f := fun y : H => y + z₀) (ψ := Ψ₀) (r := Ψ) (x := z x) g
      (by fun_prop) ((hΨ₀.contMDiffAt (hUc.mem_nhds hzU)).mdifferentiableAt (by simp))
      (Eventually.of_forall fun y => rfl)
      (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
    simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] at hshift
    rw [← hshift]
    have hχG : (WithLp.toLp 2 (fun k => (hz k).weakGrad x j) : H) =
        fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) :=
      hzgrad x (hρr hxρ) j
    rw [hχG]
    change _ = pullbackMetricCoefficients g Ψ₀ (χ (v x) - z₀ + z₀) _ _
    rw [sub_add_cancel]
    rw [← hx, ← hGx j]
    exact hchart.symm
  · intro b a ha hba hbaρ
    let hza (k : Fin (Module.finrank ℝ E)) :=
      DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hbaρ (hz k)
    have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |z x k| ≤ τ := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact hzbound x (Metric.ball_subset_closedBall (hbaρ hx))
    have hβw : (fun x => β (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w := by
      have hvwa := ae_restrict_of_ae_restrict_of_subset
        (hbaρ.trans (Metric.ball_subset_closedBall.trans hρB)) hvw
      filter_upwards [hvwa, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
      have hxρ := Metric.ball_subset_closedBall (hbaρ hxB)
      have hxR := Metric.ball_subset_closedBall (hρsub hxρ).1
      change Φ (Ψ₀ ((χ (v x) - z₀) + z₀)) = w x
      rw [sub_add_cancel]
      have hback : Ψ₀ (χ (v x)) = r (v x) := hzback x hxR
      rw [hback]
      obtain ⟨m, hm⟩ := hvK (hρB hxρ)
      rw [← hm, hleft, hm, hx]
    have hmetric (y : H) (hy : y ∈ Ushift) (v₁ v₂ : H) :
        pullbackMetricCoefficients g r (β y) (fderiv ℝ β y v₁) (fderiv ℝ β y v₂) =
          pullbackMetricCoefficients g Ψ y v₁ v₂ :=
      pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
        (hΦ.mdifferentiableAt (by simp))
        ((hr.contMDiffAt (hU.mem_nhds (hΦU (mem_range_self (Ψ y))))).mdifferentiableAt (by simp))
        hleft ((hΨ.contMDiffAt (hUshift.mem_nhds hy)).mdifferentiableAt (by simp)) v₁ v₂
    exact exists_local_harmonic_replacement_metric_comparison_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hba
      z hza (fun _ => τ) hbound hUshift (fun y hy => hbox y hy) β hβ hβw
      (fun y _ => mem_range_self (Ψ y)) (pullbackMetricCoefficients g Ψ) hmetric

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_harmonic_replacement_small_gradient_error_of_minimizing_sequence
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    {δ : ℝ} (hδ : 0 < δ) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        ∀ (b : V) (a : ℝ), 0 < a → ‖b‖ + a < 1 → Metric.ball b a ⊆ Metric.ball x₀ ρ →
          ∃ (h : V → H) (hh : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => h x k) (Metric.ball b a)),
            (∀ k, DeGiorgi.MemW01p 2 (fun x => h x k - z x k) (Metric.ball b a)) ∧
            (∀ k (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
              (∫ x in Metric.ball b a, inner ℝ ((hh k).weakGrad x)
                (DeGiorgi.smoothGradField φ x)) = 0) ∧
            (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x - (hh k).weakGrad x‖ ^ 2) ≤
              δ * ∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2 := by
  classical
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z₀ := χ (v x₀)
  let z : V → H := fun x => χ (v x) - z₀
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen (I := 𝓘(ℝ, E)) p
  have hz₀U : z₀ ∈ Uc := by
    exact ⟨extChartAt 𝓘(ℝ, E) p p,
      (extChartAt 𝓘(ℝ, E) p).map_source (mem_extChartAt_source p), rfl⟩
  let Ψ₀ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let Ψ : H → M := fun y => Ψ₀ (y + z₀)
  let B := pullbackMetricCoefficients g Ψ
  obtain ⟨lam, hlam, hcoerce⟩ := exists_pos_mul_norm_sq_le_centered_inverse_chart_metric g p hz₀U
  let ε := δ * lam / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨ρ, τ, hρ, hτ, hρB, hbox, hclose, hzc, hzbox, hz, hzgrad, hbase, hcomp⟩ :=
    exists_chart_harmonic_replacement_comparison_with_coefficient_oscillation
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀ hε
  let Ushift := (fun y : H => y + z₀) ⁻¹' Uc
  have hUshift : IsOpen Ushift := hUc.preimage (continuous_id.add continuous_const)
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  have hΨ₀ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ₀ Uc :=
    chart.contMDiffOn_invFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun y hy => toEuclidean_symm_mem_target hy)
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ Ushift :=
    hΨ₀.comp ((contDiff_id.add contDiff_const).contMDiff.contMDiffOn) (fun _ hy => hy)
  let K := {y : H | ∀ k, |y k| ≤ τ}
  have hK : IsCompact K := isCompact_coordinate_box (fun _ => τ)
  have hB : ContinuousOn B K :=
    (contDiffOn_pullback_metric_coefficients g hUshift hΨ).continuousOn.mono hbox
  have hBMeas : Measurable (K.piecewise B 0) :=
    hB.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hsym : ∀ v₁ v₂ : H, B 0 v₁ v₂ = B 0 v₂ v₁ := fun _ _ => g.symm _ _ _
  refine ⟨ρ, hρ, hρB, hzc, hz, hzgrad, ?_⟩
  intro b a ha hba hsub
  obtain ⟨h, hh, htrace, hbound, hEuler, _, hmetric⟩ := hcomp b a ha hba hsub
  let hza (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hsub (hz k)
  have hzK : ∀ᵐ x ∂volume.restrict (Metric.ball b a), z x ∈ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hzbox x (Metric.ball_subset_closedBall (hsub hx))
  have hhm : MemLp h 2 (volume.restrict (Metric.ball b a)) :=
    MemLp.of_eval_piLp fun k => (hh k).memLp
  have hzm : MemLp z 2 (volume.restrict (Metric.ball b a)) :=
    MemLp.of_eval_piLp fun k => (hza k).memLp
  have hCompMeas (f : V → H) (hfm : MemLp f 2 (volume.restrict (Metric.ball b a)))
      (hfK : ∀ᵐ x ∂volume.restrict (Metric.ball b a), f x ∈ K) :
      AEStronglyMeasurable (fun x => B (f x)) (volume.restrict (Metric.ball b a)) :=
    (hBMeas.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable.congr
      (hfK.mono fun x hx => Set.piecewise_eq_of_mem K B 0 hx)
  have hBz := hCompMeas z hzm hzK
  have hBh := hCompMeas h hhm hbound
  have hminz : (∑ j : Fin 2, ∫ x in Metric.ball b a, B (z x)
      (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.ball b a, B (h x)
        (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
    have heq : (∑ j : Fin 2, ∫ x in Metric.ball b a, B (z x)
        (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))) =
        ∑ j : Fin 2, ∫ x in Metric.ball b a, pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset hsub hbase).mono
        fun x hx => (hx j).symm)
    exact heq.trans_le hmetric
  have herr := integral_weakGrad_difference_sq_le_of_harmonic_comparison
    Metric.isOpen_ball hza hh htrace hEuler (B 0) hsym hlam hε.le hcoerce B
    (fun v₁ v₂ => (hBz.apply_continuousLinearMap v₁).apply_continuousLinearMap v₂)
    (fun v₁ v₂ => (hBh.apply_continuousLinearMap v₁).apply_continuousLinearMap v₂)
    (hzK.mono fun x hx => hclose (z x) hx) (hbound.mono fun x hx => hclose (h x) hx) hminz
  have hfactor : 2 * ε / lam = δ := by dsimp only [ε]; field_simp
  rw [hfactor] at herr
  exact ⟨h, hh, htrace, hEuler, herr⟩

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_harmonic_replacement_comparison_of_minimizing_sequence
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    let Ψ : H → M := fun y =>
      (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + z₀))
    let B := pullbackMetricCoefficients g Ψ
    ∃ ρ τ : ℝ, 0 < ρ ∧ 0 < τ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      (∀ y : H, (∀ k, |y k| ≤ τ) → y + z₀ ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p) ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ, ∀ k, |z x k| ≤ τ) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball x₀ ρ), ∀ j : Fin 2,
          pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) =
          B (z x) (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
            (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))) ∧
        ∀ (b : V) (a : ℝ), 0 < a → ‖b‖ + a < 1 → Metric.ball b a ⊆ Metric.ball x₀ ρ →
          ∃ (h : V → H) (hh : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => h x k) (Metric.ball b a)),
            (∀ k, DeGiorgi.MemW01p 2 (fun x => h x k - z x k) (Metric.ball b a)) ∧
            (∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |h x k| ≤ τ) ∧
            (∀ k (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
              (∫ x in Metric.ball b a, inner ℝ ((hh k).weakGrad x)
                (DeGiorgi.smoothGradField φ x)) = 0) ∧
            (∑ k, ∫ x in Metric.ball b a, ‖(hh k).weakGrad x‖ ^ 2) ≤
              (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2) ∧
            (∑ j : Fin 2, ∫ x in Metric.ball b a, pullbackMetricCoefficients g r (w x)
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
              ∑ j : Fin 2, ∫ x in Metric.ball b a, B (h x)
                (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))
                (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
  classical
  obtain ⟨r₀, hr₀, hball₀, hrmap, hzmap, hzc, hzback, hz₀, hzgrad⟩ :=
    exists_weak_chart_coordinates_of_continuousOn Metric.isOpen_ball hvc hv hU hr
      (fun x hx => hΦU (hvK hx)) hx₀
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z₀ := χ (v x₀)
  let z : V → H := fun x => χ (v x) - z₀
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen (I := 𝓘(ℝ, E)) p
  have hz₀U : z₀ ∈ Uc := hzmap (Metric.mem_closedBall_self hr₀.le)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (hUc.mem_nhds hz₀U)
  let n : ℝ := Module.finrank ℝ E
  let τ : ℝ := η / (n + 1)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hτ : 0 < τ := div_pos hη (by linarith)
  have hbox : ∀ y : H, (∀ k, |y k| ≤ τ) → y + z₀ ∈ Uc := by
    intro y hy
    apply hηsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
    have heq : (∑ k, EuclideanSpace.single k (y k)) = y := by ext; simp
    have hy' : ‖y‖ ≤ n * τ := by
      calc
        ‖y‖ = ‖∑ k, EuclideanSpace.single k (y k)‖ := by rw [heq]
        _ ≤ ∑ k, ‖EuclideanSpace.single k (y k)‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin (Module.finrank ℝ E), τ := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [PiLp.norm_single, Real.norm_eq_abs] using hy k
        _ = n * τ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rfl
    have hτeq : (n + 1) * τ = η := by dsimp only [τ]; field_simp
    linarith
  have hzcont : ContinuousOn z (Metric.closedBall x₀ r₀) := hzc.sub continuousOn_const
  have hzcenter : z x₀ = 0 := sub_self _
  have hopen : IsOpen (Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ) :=
    (hzcont.mono Metric.ball_subset_closedBall).isOpen_inter_preimage
      Metric.isOpen_ball Metric.isOpen_ball
  have hxopen : x₀ ∈ Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ := by
    exact ⟨Metric.mem_ball_self hr₀, by rw [mem_preimage, hzcenter]; exact Metric.mem_ball_self hτ⟩
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxopen)
  let ρ := ρ₀ / 2
  have hρ : 0 < ρ := half_pos hρ₀
  have hρsub : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r₀ ∩ z ⁻¹' Metric.ball 0 τ :=
    (Metric.closedBall_subset_ball (half_lt_self hρ₀)).trans hρ₀sub
  have hρr : Metric.ball x₀ ρ ⊆ Metric.ball x₀ r₀ :=
    fun x hx => (hρsub (Metric.ball_subset_closedBall hx)).1
  have hρB : Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 :=
    fun x hx => hball₀ (Metric.ball_subset_closedBall (hρsub hx).1)
  have hzbound : ∀ x ∈ Metric.closedBall x₀ ρ, ∀ k, |z x k| ≤ τ := by
    intro x hx k
    have hh : ‖z x‖ < τ := by
      simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using (hρsub hx).2
    have hcol : |z x k| ≤ ‖z x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (z x) k
    exact hcol.trans hh.le
  let _ : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let hz (k : Fin (Module.finrank ℝ E)) :=
    (DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hρr (hz₀ k)).subConst
      Metric.isOpen_ball (z₀ k)
  let Ψ₀ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let Ψ : H → M := fun y => Ψ₀ (y + z₀)
  let β : H → F := Φ ∘ Ψ
  let Ushift := (fun y : H => y + z₀) ⁻¹' Uc
  have hUshift : IsOpen Ushift := hUc.preimage (continuous_id.add continuous_const)
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  have hΨ₀ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ₀ Uc :=
    chart.contMDiffOn_invFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun y hy => toEuclidean_symm_mem_target hy)
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ Ushift :=
    hΨ₀.comp ((contDiff_id.add contDiff_const).contMDiff.contMDiffOn) (fun _ hy => hy)
  have hβ : ContDiffOn ℝ ∞ β Ushift := (hΦ.comp_contMDiffOn hΨ).contDiffOn
  refine ⟨ρ, τ, hρ, hτ, hρB, hbox, hzcont.mono ?_, hzbound, hz, ?_, ?_, ?_⟩
  · exact fun x hx => Metric.ball_subset_closedBall (hρsub hx).1
  · intro x hx j
    exact hzgrad x (hρr hx) j
  · have hvwa : v =ᵐ[volume.restrict (Metric.ball x₀ ρ)] w :=
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hρB) hvw
    have hGvw := weakGrad_columns_ae_eq_of_ae_eq (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hρB) hv hw hvwa
    filter_upwards [hvwa, hGvw, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hGx hxρ
    intro j
    have hxB := hρB (Metric.ball_subset_closedBall hxρ)
    have hxR := Metric.ball_subset_closedBall (hρr hxρ)
    have hchart := pullbackMetricCoefficients_chart_fderiv g p hU hr
      ⟨hΦU (hvK hxB), hrmap hxR⟩
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
    have hzU : z x + z₀ ∈ Uc := by
      simpa only [z, sub_add_cancel, χ, p, Function.comp_def, Uc] using hzmap hxR
    have hshift := pullbackMetricCoefficients_fderiv_of_eventuallyEq
      (f := fun y : H => y + z₀) (ψ := Ψ₀) (r := Ψ) (x := z x) g
      (by fun_prop) ((hΨ₀.contMDiffAt (hUc.mem_nhds hzU)).mdifferentiableAt (by simp))
      (Eventually.of_forall fun y => rfl)
      (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hz k).weakGrad x j))
    simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] at hshift
    rw [← hshift]
    have hχG : (WithLp.toLp 2 (fun k => (hz k).weakGrad x j) : H) =
        fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) :=
      hzgrad x (hρr hxρ) j
    rw [hχG]
    change _ = pullbackMetricCoefficients g Ψ₀ (χ (v x) - z₀ + z₀) _ _
    rw [sub_add_cancel]
    rw [← hx, ← hGx j]
    exact hchart.symm
  · intro b a ha hba hbaρ
    let hza (k : Fin (Module.finrank ℝ E)) :=
      DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hbaρ (hz k)
    have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |z x k| ≤ τ := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact hzbound x (Metric.ball_subset_closedBall (hbaρ hx))
    have hβw : (fun x => β (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w := by
      have hvwa := ae_restrict_of_ae_restrict_of_subset
        (hbaρ.trans (Metric.ball_subset_closedBall.trans hρB)) hvw
      filter_upwards [hvwa, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
      have hxρ := Metric.ball_subset_closedBall (hbaρ hxB)
      have hxR := Metric.ball_subset_closedBall (hρsub hxρ).1
      change Φ (Ψ₀ ((χ (v x) - z₀) + z₀)) = w x
      rw [sub_add_cancel]
      have hback : Ψ₀ (χ (v x)) = r (v x) := hzback x hxR
      rw [hback]
      obtain ⟨m, hm⟩ := hvK (hρB hxρ)
      rw [← hm, hleft, hm, hx]
    have hmetric (y : H) (hy : y ∈ Ushift) (v₁ v₂ : H) :
        pullbackMetricCoefficients g r (β y) (fderiv ℝ β y v₁) (fderiv ℝ β y v₂) =
          pullbackMetricCoefficients g Ψ y v₁ v₂ :=
      pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
        (hΦ.mdifferentiableAt (by simp))
        ((hr.contMDiffAt (hU.mem_nhds (hΦU (mem_range_self (Ψ y))))).mdifferentiableAt (by simp))
        hleft ((hΨ.contMDiffAt (hUshift.mem_nhds hy)).mdifferentiableAt (by simp)) v₁ v₂
    exact exists_local_harmonic_replacement_metric_comparison_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hba
      z hza (fun _ => τ) hbound hUshift (fun y hy => hbox y hy) β hβ hβw
      (fun y _ => mem_range_self (Ψ y)) (pullbackMetricCoefficients g Ψ) hmetric

end DifferentialGeometry.Geometry

end
