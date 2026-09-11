import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open KappaSolutions
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


theorem tensor_noncollapsed_of_growing_scales
    (C : MetricConvergenceData Φ)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (hcomplete : MetricComplete (I := I) L) (kappa : ℝ) (radii : ℕ → ℝ)
    (hradii : Tendsto (fun k => radii (subseq k)) atTop atTop)
    (hsource : ∀ (i : ℕ) (p : (X.obj i).M) (r : ℝ), 0 < r → r ≤ radii i →
      (∀ y ∈ riemannianBallOf (X.obj i).metric p r,
        r ^ 4 * normSq0S (X.obj i).metric y 4 (metricRm04At (X.obj i).metric y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
          (riemannianBallOf (X.obj i).metric p r)) :
    ∀ (z : L.M) (r : ℝ), 0 < r →
      (∀ x ∈ riemannianBallOf L.metric z r,
        r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric z r) := by
  intro z r hr hcurvature
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  let n := Module.finrank ℝ E
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : Tendsto epsilon atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Tendsto (fun j => 1 + epsilon j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hepsilon
  have hs : Tendsto s atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hreal : Tendsto (fun j => ENNReal.ofReal (s j)) atTop (𝓝 (ENNReal.ofReal r)) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  have hleft := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal kappa)
    (ENNReal.Tendsto.pow (n := n) hreal) (Or.inr ENNReal.ofReal_ne_top)
  have hsqrt : Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ n)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow n)
  have hcoef : Tendsto (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hright : Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric (riemannianBallOf L.metric z r))
      atTop (𝓝 (riemannianVolumeMeasure (I := I) (M := L.M) L.metric
        (riemannianBallOf L.metric z r))) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro j
  have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
  have h1 : 0 < 1 + epsilon j := by linarith
  have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
  have hbuffer : (1 + epsilon j) * s j < r := by
    calc
      (1 + epsilon j) * s j = r / (1 + epsilon j) := by
        dsimp only [s]
        field_simp [ne_of_gt h1]
      _ < r := div_lt_self hr (by linarith)
  obtain ⟨kv, hkv⟩ := exists_pointed_buffered_ball_volume_le_at
    C hreference hcomplete z hsj he hbuffer he
  obtain ⟨kc, hkc⟩ := exists_pointed_ball_curvature_control
    C hcanonical hcomplete z hsj he hbuffer hcurvature
  obtain ⟨kr, hkr⟩ := eventually_atTop.1 (hradii.eventually_ge_atTop (s j))
  let k := max kv (max kc kr)
  have hkvk : kv ≤ k := Nat.le_max_left _ _
  have hkck : kc ≤ k := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hkrk : kr ≤ k := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact (hsource (subseq k) (Φ.map k z) (s j) hsj (hkr k hkrk)
    (hkc k hkck)).trans (hkv k hkvk)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
