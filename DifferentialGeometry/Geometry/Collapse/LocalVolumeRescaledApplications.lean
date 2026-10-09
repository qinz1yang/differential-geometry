import DifferentialGeometry.Geometry.Collapse.LocalVolumeRescaledPackets
import DifferentialGeometry.Geometry.Collapse.LocalVolumeRescaledCorollaries
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit

set_option autoImplicit false
noncomputable section
open Set Metric Filter Real
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry
namespace DifferentialGeometry.Geometry.Collapse
universe u v
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : ℕ → Type u} [mZ : ∀ n, MetricSpace (Z n)]
  [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)]
  [∀ n, SigmaCompactSpace (Z n)] [∀ n, CompleteSpace (Z n)]

/-- The actual cubes and volume bound hold on one tail of the original convergence. -/
theorem exists_rescaled_cubes_and_volume_on_original_sequence
    (hdim : Module.finrank ℝ E = 3)
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (p : ∀ n, Z n) {ρ L : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ n, ∀ y ∈ riemannianBallOf (g n) (p n) (L n * ρ n),
      SectionalBoundedBelowAt (g n) y (-((L n * ρ n) ^ 2)⁻¹))
    {Y : Type v} [MetricSpace Y] {x : Y}
    (hconv : @PointedGHConverges Z
      (fun n => (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))) Y _ p x)
    (hdimY : 2 < dimH (univ : Set Y)) :
    ∃ r e v : ℝ, 0 < r ∧ r < 1 / 4 ∧ 0 < e ∧ 0 < v ∧
      letI : ∀ n, MetricSpace (Z n) := fun n =>
        (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
      ∀ᶠ n in atTop, ∃ y : Z n, ∃ c d : Fin 3 → Z n,
        dist y (p n) < 1 / 2 ∧ Function.Injective (Sum.elim c d) ∧
        y ∉ range c ∪ range d ∧
        {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - dist y (c j)| ≤ e / 4} ⊆
          distanceCoordinates 2 c ''
            riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (r / 2) ∧
        LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c) ∧
        ENNReal.ofReal v ≤ ballVolume (scaleMetric ((ρ n)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) 2
 := by
  obtain ⟨q, hq, a, b, hp, hinj, hne, a₀, A, r, R,
    ha₀, haA, hr, hrsmall, hR, hμ, he, htail⟩ :=
    exists_uniform_rescaled_packet_cubes_of_dimH_gt_two (mZ := mZ)
      hdim g hmetric p hρ hL hsec hconv hdimY
  obtain ⟨v, hv, hvol⟩ := eventually_rescaled_ballVolume_lower_of_localVolume_producer
    (mZ := mZ) hdim g hmetric p hρ hL hsec hconv hdimY
  refine ⟨r, localVolumeCubeRadius a₀ A r, v, hr, hrsmall, he, hv, ?_⟩
  let m' : ∀ n, MetricSpace (Z n) := fun n =>
    (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
  filter_upwards [htail, hvol] with n hn hnv
  obtain ⟨y, c, d, hy, hcn, hanc, hbuf, hpacket, hc, hb, hcdi, hyanc, hcube, hlip⟩ := hn
  exact ⟨y, c, d, hy, hcdi, hyanc, hcube, hlip, hnv⟩

/-- LC05 selects one actual limit; LC12–15 then apply to that same subsequence. -/
theorem exists_rescaled_pointed_limit_with_local_cubes_and_volume
    (hdim : Module.finrank ℝ E = 3)
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (p : ∀ n, Z n) {ρ L : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ n, ∀ y ∈ riemannianBallOf (g n) (p n) (L n * ρ n),
      SectionalBoundedBelowAt (g n) y (-((L n * ρ n) ^ 2)⁻¹))
    : ∃ (Y : Type) (m : MetricSpace Y),
      let := m
      ∃ (x : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        @PointedGHConverges (fun n => Z (φ n))
          (fun n => (mZ (φ n)).rescale (ρ (φ n))⁻¹ (inv_pos.mpr (hρ (φ n)))) Y m
          (fun n => p (φ n)) x ∧
        dimH (univ : Set Y) ≤ 3 ∧ fourPointComparison 0 (univ : Set Y) ∧
        (2 < dimH (univ : Set Y) →
          ∃ r e v : ℝ, 0 < r ∧ r < 1 / 4 ∧ 0 < e ∧ 0 < v ∧
          letI : ∀ n, MetricSpace (Z (φ n)) := fun n =>
            (mZ (φ n)).rescale (ρ (φ n))⁻¹ (inv_pos.mpr (hρ (φ n)))
          ∀ᶠ n in atTop, ∃ y : Z (φ n), ∃ c d : Fin 3 → Z (φ n),
            dist y (p (φ n)) < 1 / 2 ∧ Function.Injective (Sum.elim c d) ∧
            y ∉ range c ∪ range d ∧
            {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - dist y (c j)| ≤ e / 4} ⊆
              distanceCoordinates 2 c ''
                riemannianBallOf (scaleMetric ((ρ (φ n))⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (hρ (φ n))) 2) (g (φ n))) y (r / 2) ∧
            LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c) ∧
            ENNReal.ofReal v ≤ ballVolume (scaleMetric ((ρ (φ n))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ (φ n))) 2) (g (φ n))) (p (φ n)) 2) := by
  obtain ⟨Y, m, x, φ, hφ, hcomplete, hproper, hconv, hdimY, hcompY, _⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer (mX := mZ) g hmetric p hρ hL hsec
  let := m
  refine ⟨Y, m, x, φ, hφ, hcomplete, hproper, ?_, ?_, hcompY, ?_⟩
  · exact hconv
  · simpa only [hdim, Nat.cast_ofNat] using hdimY
  · intro hdimlo
    exact exists_rescaled_cubes_and_volume_on_original_sequence
      (mZ := fun n => mZ (φ n)) hdim (fun n => g (φ n)) (fun n => hmetric (φ n))
      (fun n => p (φ n)) (fun n => hρ (φ n)) (hL.comp hφ.tendsto_atTop)
      (fun n => hsec (φ n)) hconv hdimlo

end DifferentialGeometry.Geometry.Collapse
