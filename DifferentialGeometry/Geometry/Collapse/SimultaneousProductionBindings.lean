import DifferentialGeometry.Geometry.Collapse.AnnularDirections
import DifferentialGeometry.Geometry.Collapse.RankOneAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.SimultaneousProductionApplications
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScaleSmooth

/-!
# F8 actual comparison and common analytic data

LCP01 keeps the original ball20b and every minimizing direction. LPA01 constructs the
actual LC02 scales and derives the same normalized metric bounds at all centers on one tail.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Real Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

section Annular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_simultaneous_annular_directions (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ a b κ τ : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o) (ha : 0 < a) (hab : a ≤ b)
    (hκ : 0 ≤ κ) (hκb : κ * b ≤ 1 / 3)
    (hsec : ∀ y ∈ Metric.ball p (20 * b), SectionalBoundedBelowAt g y (-κ ^ 2))
    (hτ : 0 < τ) (hτπ : τ < π / 2) (hδa : δ < a / 30) (hδb : δ < 1 / (4 * b + 20))
    (hδτ : δ < a * (1 - Real.cos τ) / 90) {q : M} (hq : a ≤ dist p q ∧ dist p q ≤ b) :
    ∃ w : TangentSpace I q, g.inner q w w = 1 ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, π - τ < Real.arccos (g.inner q v w)) ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, g.inner q v w < 0) ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, ∀ v' ∈ minimizingDirectionsTo g hEnorm {p} q,
        Real.sqrt (g.inner q (v - v') (v - v')) < 4 * Real.sin (τ / 2)) ∧
      4 * Real.sin (τ / 2) < 2 * τ := by
  exact exists_outward_unit_direction_of_kleinerLottApprox g hEnorm φ H ha hab hκ hκb
    hsec hτ hτπ hδa hδb hδτ hq

end Annular

section Sequence

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]

theorem eventually_simultaneous_analytic_data (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    let v := w / (2 * (1 + 2 * Λ⁻¹) ^ 3)
    ∀ᶠ i in atTop, 4 < α i ∧ (α i)⁻¹ ≤ v ∧
      (∃ ρ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
        LipschitzWith (Real.toNNReal Λ) ρ ∧ ∀ p, 0 < ρ p ∧
          firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p v) ∧
      ∀ (p : X i) (r : ℝ) (hr : 0 < r), r ≤ 2 * firstVolumeScale (g i) p v →
        0 < v / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ∧
        v / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ≤
          (ballVolume (normalizedCenterMetric (g i) r hr) p 1).toReal ∧
        (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) r hr) p (α i / 4),
          SectionalBoundedBelowAt (normalizedCenterMetric (g i) r hr) y
            (-((α i / 4) ^ 2)⁻¹)) ∧
        ∀ R, 0 < R → 2 * R + 2 < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) r hr) p R,
            curvatureDerivativeNorm (normalizedCenterMetric (g i) r hr) k y ≤
              (2 : ℝ) ^ (K + 2) * A (2 * R + 2) v := by
  let v := w / (2 * (1 + 2 * Λ⁻¹) ^ 3)
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ])
      (n := 3)
    linarith
  have hv : 0 < v := div_pos hw (by linarith)
  have hvc : v < 4 * Real.pi / 3 := (div_lt_self hw hden).trans hwc
  filter_upwards [eventually_exists_smooth_modifiedScale hdim g hmetric hα hstand hΛ hw hwc,
    hα.eventually (eventually_gt_atTop 4),
    hα.eventually (eventually_ge_atTop v⁻¹)] with i hscale hi4 hiv
  have hαpos : 0 < α i := by linarith
  have hinv : (α i)⁻¹ ≤ v := by
    rw [inv_le_comm₀ hαpos hv]
    exact hiv
  refine ⟨hi4, hinv, hscale, ?_⟩
  intro p r hr hup
  have hu := (firstVolumeScale_spec (g i) hdim p hv hvc).1
  have hanti := firstVolumeScale_strictAntiOn (g i) hdim p
  have hule : firstVolumeScale (g i) p v ≤ firstVolumeScale (g i) p (α i)⁻¹ :=
    hanti.antitoneOn ⟨inv_pos.mpr hαpos, hinv.trans_lt hvc⟩ ⟨hv, hvc⟩ hinv
  have hscale' : ENNReal.ofReal (α i * firstVolumeScale (g i) p v) ≤
      curvatureRadius (g i) p :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hule hαpos.le)).trans (hstand i p)
  have hvol := ballVolume_firstVolumeScale (g i) hdim p hv hvc
  have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) p
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let : MetricSpace (X i) := inducedMetricSpace (g i)
  let : RiemannianBundle (fun x : X i => TangentSpace I x) := ⟨(g i).toRiemannianMetric⟩
  have : IsRiemannianManifold I (X i) := inducedMetricSpace_isRiemannianManifold (g i)
  have : IsContinuousRiemannianBundle E (fun x : X i => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric (g i)
  have : CompleteSpace (X i) := inducedMetricSpace_completeSpace (g i)
  exact normalizedCenterMetric_joint_data (g i) (isMetricNorm_of_smoothRiemannianMetric (g i))
    hdim K (fun C => A C v) p hi4 hv hu hr hup hscale' hvol
    (fun C hC => (hA C v hC hv hvc).le)
    (fun C hC hCα k hk y hy => hder i p v hv hvc hinv C hC hCα k hk y hy)

theorem eventually_exists_simultaneous_analytic_scale (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    let v := w / (2 * (1 + 2 * Λ⁻¹) ^ 3)
    ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρ : ∀ p, 0 < ρ p,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
      ∀ p : X i, firstVolumeScale (g i) p w / 2 < ρ p ∧
        ρ p < 2 * firstVolumeScale (g i) p v ∧
        0 < v / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ∧
        v / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ≤
          (ballVolume (normalizedCenterMetric (g i) (ρ p) (hρ p)) p 1).toReal ∧
        (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ p) (hρ p)) p (α i / 4),
          SectionalBoundedBelowAt (normalizedCenterMetric (g i) (ρ p) (hρ p)) y
            (-((α i / 4) ^ 2)⁻¹)) ∧
        ∀ R, 0 < R → 2 * R + 2 < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ p) (hρ p)) p R,
            curvatureDerivativeNorm (normalizedCenterMetric (g i) (ρ p) (hρ p)) k y ≤
              (2 : ℝ) ^ (K + 2) * A (2 * R + 2) v := by
  filter_upwards [eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder
    hΛ hw hwc] with i hi
  have hdata := hi.2.2.2
  obtain ⟨ρ, hsm, hlip, hb⟩ := hi.2.2.1
  refine ⟨ρ, (fun p => (hb p).1), hsm, hlip, fun p => ?_⟩
  exact ⟨(hb p).2.1, (hb p).2.2, hdata p (ρ p) (hb p).1 (hb p).2.2.le⟩

theorem eventually_simultaneous_common_test_range (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    let v := w / (2 * (1 + 2 * Λ⁻¹) ^ 3)
    ∀ B : ℝ, ∀ᶠ i in atTop, 2 * B + 2 < α i ∧
      ∀ (p : X i) (r : ℝ) (hr : 0 < r), r ≤ 2 * firstVolumeScale (g i) p v →
        ∀ R, 0 < R → R < B → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) r hr) p R,
            curvatureDerivativeNorm (normalizedCenterMetric (g i) r hr) k y ≤
              (2 : ℝ) ^ (K + 2) * A (2 * R + 2) v := by
  dsimp only
  intro B
  filter_upwards [eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder
    hΛ hw hwc, hα.eventually (eventually_gt_atTop (2 * B + 2))] with i hi hB
  refine ⟨hB, ?_⟩
  intro p r hr hup R hR hRB k hk y hy
  exact (hi.2.2.2 p r hr hup).2.2.2 R hR (by linarith) k hk y hy

end Sequence

section RankOne

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uR v

theorem exists_simultaneous_rankOne_minimizing_tests {γ : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ < min γ (1 / 4) ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uR) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν),
        (∀ y ∈ Metric.ball q ν⁻¹, SectionalBoundedBelowAt g y (-ν ^ 2)) →
        ∃ φ : M → ℝ,
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1) ∧ φ q = 0 ∧
          (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
            |φ x - φ y| ≤ (1 + γ) * dist x y) ∧
          (∀ x ∈ Metric.ball q 1, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 1,
            Metric.infDist t (φ '' Metric.ball q 1) ≤ γ) ∧
          (∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist x z →
            ∀ w : TangentSpace I x, g.inner x w w = 1 →
            intrinsicGeodesic g hEnorm x w (dist x z) = z →
            |mvfderiv (I := I) φ x w -
              ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < γ) ∧
          ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist x z →
            (∀ w ∈ minimizingDirectionsTo g hEnorm {z} x,
              |mvfderiv (I := I) φ x w -
                ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < γ) ∧
            ∀ w ∈ minimizingDirectionsTo g hEnorm {z} x,
              ∀ w' ∈ minimizingDirectionsTo g hEnorm {z} x,
                |mvfderiv (I := I) φ x w - mvfderiv (I := I) φ x w'| < 2 * γ := by
  obtain ⟨ν₀, hν₀, hν₀bound, hproduction⟩ :=
    exists_rankOne_adapted_coordinate_parameters.{uE, uH, uR, v} hγ hγone
  refine ⟨ν₀, hν₀, hν₀bound, ?_⟩
  intro ν hν hνsmall E instNorm instSpace instFinite instNe H instTop I instBoundary
    M instMetric instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y instY q y₀ α hsec
  obtain ⟨φ, hsm, hq, hlip, himage, hcover, htest⟩ :=
    hproduction ν hν hνsmall E H I M g hEnorm Y q y₀ α hsec
  refine ⟨φ, hsm, hq, hlip, himage, hcover, htest, ?_⟩
  intro x hx z hz hxz
  have hall (w : TangentSpace I x) (hw : w ∈ minimizingDirectionsTo g hEnorm {z} x) :
      |mvfderiv (I := I) φ x w -
        ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < γ := by
    exact htest x hx z hz hxz w hw.1
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hw.2)
  refine ⟨hall, ?_⟩
  intro w hw w' hw'
  have h1 := abs_lt.mp (hall w hw)
  have h2 := abs_lt.mp (hall w' hw')
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end RankOne

end DifferentialGeometry.Geometry.Collapse
