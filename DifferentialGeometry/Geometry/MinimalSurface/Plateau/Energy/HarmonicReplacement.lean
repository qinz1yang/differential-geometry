import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ZeroTraceExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakReplacement
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.Harmonic
import DifferentialGeometry.Analysis.Convex.CoordinateBox
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact

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

theorem weak_replacement_energy_le_of_memW01p_sub_of_disk_energy_minimizing_sequence
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
    {b : V} {a : ℝ} (ha : 0 < a) (hba : ‖b‖ + a < 1)
    (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball b a))
    (hqK : ∀ᵐ x ∂volume.restrict (Metric.ball b a), q x ∈ range Φ)
    (hqw : ∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - w x i) (Metric.ball b a)) :
    (∑ j : Fin 2, ∫ x in Metric.ball b a,
      pullbackMetricCoefficients g r (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.ball b a,
        pullbackMetricCoefficients g r (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
  obtain ⟨v, ⟨hv⟩, hvq, hvw⟩ := exists_weak_extension_of_memW01p_sub
    Metric.isOpen_ball Metric.isOpen_ball hw hqw
  let c := (1 - ‖b‖ + a) / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hbc : ‖b‖ + c < 1 := by dsimp only [c]; linarith
  have hball : Metric.closedBall b c ⊆ Metric.ball (0 : V) 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x - b‖ ≤ c := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x - b‖ + ‖b‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - b) b
    linarith
  let hvc (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hball) (hv i)
  let K := range Φ
  let A := pullbackMetricCoefficients g r
  have hK : IsCompact K := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ K :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hvK : ∀ᵐ x ∂volume.restrict (Metric.ball b c), v x ∈ K := by
    have hqae := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hqK
    filter_upwards [ae_restrict_of_ae hqae,
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hwK]
      with x hxq hxw
    by_cases hx : x ∈ Metric.ball b a
    · rw [hvq hx]
      exact hxq hx
    · rw [hvw hx]
      exact hxw
  have hvweq : v =ᵐ[volume.restrict (Metric.ball b c \ Metric.closedBall b a)] w := by
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff
      Metric.isClosed_closedBall.measurableSet)] with x hx
    exact hvw (fun h => hx.2 (Metric.ball_subset_closedBall h))
  have hcomp := weak_replacement_energy_le_on_interior_ball_of_disk_energy_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hac hbc v hvc hvK hvweq
  have heqμ : volume.restrict (Metric.closedBall b a) = volume.restrict (Metric.ball b a) := by
    apply Measure.restrict_congr_set
    have hnull := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume b a)
    filter_upwards [hnull] with x hx
    apply propext
    exact ⟨fun h => lt_of_le_of_ne h hx, le_of_lt⟩
  rw [heqμ] at hcomp
  let hva (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball
    (Metric.ball_subset_ball hac.le) (hvc i)
  have hveq : v =ᵐ[volume.restrict (Metric.ball b a)] q := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hvq hx
  have hgrad := quadratic_weakGrad_columns_ae_eq_of_ae_eq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) Metric.isOpen_ball (Subset.rfl)
    hva hq hveq (fun _ y => A y)
  have hE : (∑ j : Fin 2, ∫ x in Metric.ball b a, A (v x)
      (WithLp.toLp 2 (fun i => (hvc i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hvc i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in Metric.ball b a, A (q x)
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_congr_ae (hgrad.mono fun x hx => hx j)
  exact hcomp.trans_eq hE

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

theorem exists_composed_harmonic_replacement_energy_comparison_of_minimizing_sequence
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
    {κ : Type*} [Fintype κ] {b : V} {a : ℝ} (ha : 0 < a) (hba : ‖b‖ + a < 1)
    (z : V → EuclideanSpace ℝ κ)
    (hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball b a))
    (C : κ → ℝ) (hzC : ∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |z x k| ≤ C k)
    (T : EuclideanSpace ℝ κ → F) (hT : ContDiff ℝ 1 T)
    {L : ℝ} (hL : ∀ y, ‖fderiv ℝ T y‖ ≤ L)
    (hTw : (fun x => T (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w)
    (hTK : MapsTo T {y | ∀ k, |y k| ≤ C k} (range Φ)) :
    ∃ (h : V → EuclideanSpace ℝ κ)
      (hh : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => h x k) (Metric.ball b a)),
      (∀ k, DeGiorgi.MemW01p 2 (fun x => h x k - z x k) (Metric.ball b a)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |h x k| ≤ C k) ∧
      (∀ k (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
        (∫ x in Metric.ball b a, inner ℝ ((hh k).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      (∑ k, ∫ x in Metric.ball b a, ‖(hh k).weakGrad x‖ ^ 2) ≤
        (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2) ∧
      (∑ j : Fin 2, ∫ x in Metric.ball b a,
        pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
        ∑ j : Fin 2, ∫ x in Metric.ball b a,
          pullbackMetricCoefficients g r (T (h x))
            (fderiv ℝ T (h x) (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)))
            (fderiv ℝ T (h x) (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))) := by
  obtain ⟨h, hh, hq, htrace, hbox, htraceT, htarget, hgradient, hEuler, hminEuclid⟩ :=
    exists_harmonic_replacement_comp_of_coordinate_bounds hz C hzC T hT hL hTw hTK
  have henergy := hminEuclid z (fun k => by
    simpa only [sub_self] using DeGiorgi.smoothTest_memH01 Metric.isOpen_ball
      (DeGiorgi.IsSmoothTestOn.zero (Ω := Metric.ball b a))) hz
  refine ⟨h, hh, htrace, hbox, hEuler, henergy, ?_⟩
  have hminQ := weak_replacement_energy_le_of_memW01p_sub_of_disk_energy_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hba
    (fun x => T (h x)) hq htarget htraceT
  have hcol (x : V) (j : Fin 2) :
      (WithLp.toLp 2 (fun i => (hq i).weakGrad x j) : F) =
        fderiv ℝ T (h x) (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
    ext i
    exact hgradient i x j
  simpa only [hcol] using hminQ

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

theorem exists_local_harmonic_replacement_metric_comparison_of_minimizing_sequence
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
    {κ : Type*} [Fintype κ] {b : V} {a : ℝ} (ha : 0 < a) (hba : ‖b‖ + a < 1)
    (z : V → EuclideanSpace ℝ κ)
    (hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball b a))
    (C : κ → ℝ) (hzC : ∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |z x k| ≤ C k)
    {Uc : Set (EuclideanSpace ℝ κ)} (hUc : IsOpen Uc)
    (hbox : {y : EuclideanSpace ℝ κ | ∀ k, |y k| ≤ C k} ⊆ Uc)
    (β : EuclideanSpace ℝ κ → F) (hβ : ContDiffOn ℝ ∞ β Uc)
    (hβw : (fun x => β (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w)
    (hβK : MapsTo β Uc (range Φ))
    (B : EuclideanSpace ℝ κ → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hmetric : ∀ y ∈ Uc, ∀ v₁ v₂,
      pullbackMetricCoefficients g r (β y) (fderiv ℝ β y v₁) (fderiv ℝ β y v₂) = B y v₁ v₂) :
    ∃ (h : V → EuclideanSpace ℝ κ)
      (hh : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => h x k) (Metric.ball b a)),
      (∀ k, DeGiorgi.MemW01p 2 (fun x => h x k - z x k) (Metric.ball b a)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ k, |h x k| ≤ C k) ∧
      (∀ k (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
        (∫ x in Metric.ball b a, inner ℝ ((hh k).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      (∑ k, ∫ x in Metric.ball b a, ‖(hh k).weakGrad x‖ ^ 2) ≤
        (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2) ∧
      (∑ j : Fin 2, ∫ x in Metric.ball b a,
        pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
        ∑ j : Fin 2, ∫ x in Metric.ball b a, B (h x)
          (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))
          (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
  let K := {y : EuclideanSpace ℝ κ | ∀ k, |y k| ≤ C k}
  obtain ⟨T, hT, hTc, hTeq⟩ :=
    exists_contDiff_compactSupport_extension_on_isCompact (isCompact_coordinate_box C) hUc hbox hβ
  obtain ⟨L, hL⟩ := (hT.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hTc.fderiv (𝕜 := ℝ))
  have hTeqAt (y : EuclideanSpace ℝ κ) (hy : y ∈ K) : T =ᶠ[𝓝 y] β :=
    hTeq.filter_mono (nhds_le_nhdsSet hy)
  have hTw : (fun x => T (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w := by
    filter_upwards [hzC, hβw] with x hx hwx
    exact (hTeqAt (z x) hx).eq_of_nhds.trans hwx
  have hTK : MapsTo T K (range Φ) := by
    intro y hy
    rw [(hTeqAt y hy).eq_of_nhds]
    exact hβK (hbox hy)
  obtain ⟨h, hh, htrace, hbound, hEuler, henergy, hcomp⟩ :=
    exists_composed_harmonic_replacement_energy_comparison_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hba
      z hz C hzC T (hT.of_le (by simp)) hL hTw hTK
  refine ⟨h, hh, htrace, hbound, hEuler, henergy, ?_⟩
  apply hcomp.trans_eq
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hbound] with x hx
  rw [(hTeqAt (h x) hx).eq_of_nhds, (hTeqAt (h x) hx).fderiv_eq]
  exact hmetric (h x) (hbox hx) _ _

end DifferentialGeometry.Geometry

end
