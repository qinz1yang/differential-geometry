import DifferentialGeometry.Geometry.Collapse.LocalVolumePackets
import DifferentialGeometry.Geometry.Collapse.LocalVolumeDimension
import DifferentialGeometry.Geometry.Collapse.LocalVolumeSequence

set_option autoImplicit false

noncomputable section

open Set Metric Filter Bundle Manifold Real
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A genuine Riemannian consumer of LC10, with the comparison generated from sectional bounds. -/
theorem dimH_three_of_sectional_bound_and_chart
    {M : Type*} [MetricSpace M] [CompleteSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y (-1)) (q : M)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L)
    (f : ball q ρ → EuclideanSpace ℝ (Fin 3))
    (hlower : ∀ x y, L⁻¹ * dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ L * dist x y) (hopen : IsOpen (range f)) :
    dimH (univ : Set M) = 3 := by
  have hcomp : fourPointComparison 1 (univ : Set M) := by
    intro z hz a ha b hb c hc hax hbx hcx
    let R := 1 + dist z q + dist a q + dist b q + dist c q
    have hzR : z ∈ ball q R := by
      simp only [mem_ball, R]
      linarith [dist_nonneg (x := a) (y := q), dist_nonneg (x := b) (y := q),
        dist_nonneg (x := c) (y := q)]
    have haR : a ∈ ball q R := by
      simp only [mem_ball, R]
      linarith [dist_nonneg (x := z) (y := q), dist_nonneg (x := b) (y := q),
        dist_nonneg (x := c) (y := q)]
    have hbR : b ∈ ball q R := by
      simp only [mem_ball, R]
      linarith [dist_nonneg (x := z) (y := q), dist_nonneg (x := a) (y := q),
        dist_nonneg (x := c) (y := q)]
    have hcR : c ∈ ball q R := by
      simp only [mem_ball, R]
      linarith [dist_nonneg (x := z) (y := q), dist_nonneg (x := a) (y := q),
        dist_nonneg (x := b) (y := q)]
    exact fourPointComparison_of_sectional_lower_bound_on_eight_ball g hmetric q
      (by norm_num) (fun y hy => hsec y) z hzR a haR b hbR c hcR hax hbx hcx
  exact dimH_eq_of_open_bilipschitz_ball
    (fun a b η hη => exists_arbitrarily_short_riemannian_curve g hmetric a b hη)
    hcomp q hρ hL (by norm_num) f hlower hupper hopen

/-- Actual Riemannian distance coordinates consume LC13 and LC14 with the original constant. -/
theorem packet_distance_coordinates_volume_lower
    {M : Type*} [MetricSpace M] [CompleteSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hdim : Module.finrank ℝ E = 3)
    {Ω V : Set M} {a b : Fin 3 → M} {q : M} {a₀ A δ r : ℝ}
    (hpacket : PairedComparisonPacket δ V a b) (hcomp : fourPointComparison 1 Ω)
    (hV : V ⊆ Ω) (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / 300) (hr : 0 < r)
    (hbuffer : ball q (2 * r) ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A) :
    let μ := 1 - 3 * δ ^ 2 - 12 * δ
    let e := min 1 (min (a₀ / 2)
      (min (δ ^ 2 / (4 * cosh (A + 1) / sinh a₀)) (μ * r / 2)))
    0 < e ∧ ENNReal.ofReal ((e / 2) ^ 3 / (3 * sqrt 3)) ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g (ball q (r / 2)) := by
  obtain ⟨hμ, he, hcube, hlip⟩ := hpacket.cube_subset_distanceCoordinates_image_three
    (fun a b η hη => exists_arbitrarily_short_riemannian_curve g hmetric a b hη)
    hcomp hV hanchors ha₀ hδ hδm hr isClosed_closedBall.isComplete hbuffer hbounds
  exact ⟨he, (volume_lower_of_local_image_cube g hEnorm hdim hlip.lipschitzOnWith
    he (v := distanceCoordinates 2 a q) hcube).1⟩

/-- Actual curvature balls produce a limit and the LC15 implication on that same subsequence. -/
theorem exists_pointed_limit_with_volume_implication
    {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)]
    [∀ n, T2Space (TangentBundle I (Z n))] [∀ n, SigmaCompactSpace (Z n)]
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (hdim : Module.finrank ℝ E = 3) (p : ∀ n, Z n) {κ ρ : ℕ → ℝ}
    (hκ : ∀ n, 0 ≤ κ n) (hκzero : Tendsto κ atTop (𝓝 0))
    (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ n, ∀ y ∈ ball (p n) (ρ n), SectionalBoundedBelowAt (g n) y (-κ n)) :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun n => p (φ n)) q ∧ dimH (univ : Set Y) ≤ 3 ∧
        fourPointComparison 0 (univ : Set Y) ∧
        (2 < dimH (univ : Set Y) → ∃ v : ℝ, 0 < v ∧ ∀ᶠ n in atTop,
          ENNReal.ofReal v ≤ ballVolume (g (φ n)) (p (φ n)) 2) := by
  obtain ⟨Y, m, q, φ, hφ, hc, hp, hconv, hd, hcomp, hrest⟩ :=
    exists_pointed_limit_of_growing_sectional_lower_bound g hmetric p hκ hκzero hρ hsec
  let := m
  refine ⟨Y, m, q, φ, hφ, hc, hp, hconv, by simpa [hdim] using hd, hcomp, ?_⟩
  intro hdimlo
  exact eventually_volume_ball_two_lower_of_growing_sectional_bound
    (fun n => g (φ n)) (fun n => hmetric (φ n)) hdim (fun n => hκ (φ n))
    (hκzero.comp hφ.tendsto_atTop) (hρ.comp hφ.tendsto_atTop)
    (fun n => hsec (φ n)) hconv hdimlo

/-- The LC11–13 adapters supply actual coordinate cubes on one tail of the chosen sequence. -/
theorem eventually_local_coordinate_cubes_of_limit_dimension
    {X : Type*} [MetricSpace X] {Z : ℕ → Type*}
    [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    {p : ∀ n, Z n} {x : X} (hconv : PointedGHConverges p x)
    (hcurves : ∀ n, ∀ a b : Z n, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, fourPointComparison 1 (ball (p n) R))
    (hcompX : fourPointComparison 0 (univ : Set X))
    (hdimlo : 2 < dimH (univ : Set X)) (hdimhi : dimH (univ : Set X) ≤ 3) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ n in atTop, ∃ y : Z n, ∃ c : Fin 3 → Z n,
      dist y (p n) < 1 / 2 ∧
      {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - dist y (c j)| ≤ e / 4} ⊆
        distanceCoordinates 2 c '' ball (p n) 2 ∧
      LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c) := by
  have : CompleteSpace X := hconv.complete_space
  obtain ⟨q, hq, a, b, hpacket, _, _⟩ := exists_local_volume_packet
    (hconv.arbitrarily_short_curves hcurves) hcompX hdimlo hdimhi x
  obtain ⟨a₀, A, r, R, _, _, hr, hrsmall, _, he, htail⟩ :=
    exists_uniform_local_volume_cubes hconv hcurves hcomp hpacket (mem_ball.mp hq)
  refine ⟨localVolumeCubeRadius a₀ A r, he, ?_⟩
  filter_upwards [htail] with n hn
  obtain ⟨y, c, d, hy, _, _, _, _, _, _, hcube, hlip⟩ := hn
  refine ⟨y, c, hy, hcube.trans (image_mono ?_), hlip⟩
  intro z hz
  have hdist := dist_triangle z y (p n)
  have hzy := mem_ball.mp hz
  rw [mem_ball]
  linarith

end DifferentialGeometry.Geometry.Collapse
