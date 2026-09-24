import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureShortening
import DifferentialGeometry.Geometry.Comparison.Toponogov.HyperbolicComparisonAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompactBallCompletion
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteMetricSegment

noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
  (exists_intrinsicGeodesic_eq_metric_segment)

universe u



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem hyperbolic_comparison_of_complete_metric_segments
    {W : Type u} [TopologicalSpace W] [T2Space W] [ChartedSpace H W]
    [IsManifold I ∞ W] [SigmaCompactSpace W]
    (g : SmoothRiemannianMetric I W) (hcomplete : RiemannianMetricComplete g)
    (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ) (k : ℝ) (hk : 0 < k) (hL : ∀ k, 0 < L k)
    (hstart : arm 0 0 = arm 1 0)
    (hmetric : ∀ k s, s ∈ Icc 0 (L k) → ∀ t ∈ Icc 0 (L k),
      riemannianEDistOf g (arm k s) (arm k t) = ENNReal.ofReal |s - t|)
    (hsec : ∀ s ∈ Icc 0 (L 0), ∀ t ∈ Icc 0 (L 1), ∀ y : W,
      riemannianEDistOf g (arm 0 s) y + riemannianEDistOf g y (arm 1 t) =
        riemannianEDistOf g (arm 0 s) (arm 1 t) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2))
    (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (haL : a2 ≤ L 0)
    (hb1 : 0 < b1) (hb12 : b1 ≤ b2) (hbL : b2 ≤ L 1) :
    hyperbolicComparisonAngle k a2 b2 (riemannianEDistOf g (arm 0 a2) (arm 1 b2)).toReal ≤
      hyperbolicComparisonAngle k a1 b1 (riemannianEDistOf g (arm 0 a1) (arm 1 b1)).toReal := by
  let : IsManifold I 1 W := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace I W
  let : T3Space W := inferInstance
  let : RiemannianBundle (fun x : W => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : W => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace W := EMetricSpace.ofRiemannianMetric I W
  let : CompleteSpace W := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hdistOf (x y : W) : riemannianEDistOf g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist g hEnorm x y
  have hnmetric (k : Fin 2) (s t : Icc (0 : ℝ) (L k)) :
      riemannianEDist I (arm k s) (arm k t) = ENNReal.ofReal |(s : ℝ) - t| := by
    rw [← hdistOf]
    exact hmetric k s s.property t t.property
  obtain ⟨u, hu, huall⟩ := exists_intrinsicGeodesic_eq_metric_segment g hEnorm (hL 0)
    (fun s : Icc (0 : ℝ) (L 0) => arm 0 s) (hnmetric 0)
  obtain ⟨v, hv, hvall⟩ := exists_intrinsicGeodesic_eq_metric_segment g hEnorm (hL 1)
    (fun s : Icc (0 : ℝ) (L 1) => arm 1 s) (hnmetric 1)
  let o : W := arm 0 0
  let v₀ : TangentSpace I o := (v : E)
  have hv₀ : g.inner o v₀ v₀ = 1 :=
    (congrArg (fun p => g.inner p (v : E) (v : E)) hstart).trans hv
  have hgeo₀ (s : ℝ) (hs : s ∈ Icc 0 (L 0)) :
      arm 0 s = intrinsicGeodesic g hEnorm o u s := huall ⟨s, hs⟩
  have hgeo₁ (t : ℝ) (ht : t ∈ Icc 0 (L 1)) :
      arm 1 t = intrinsicGeodesic g hEnorm o v₀ t :=
    (hvall ⟨t, ht⟩).trans
      (congrArg (fun p => intrinsicGeodesic g hEnorm p (v : E) t) hstart.symm)
  have ha2 : 0 < a2 := ha1.trans_le ha12
  have hb2 : 0 < b2 := hb1.trans_le hb12
  have hminA : (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a2)).toReal = a2 := by
    rw [← hgeo₀ a2 ⟨ha2.le, haL⟩]
    have h := congrArg ENNReal.toReal (hnmetric 0 ⟨0, ⟨le_rfl, (hL 0).le⟩⟩
      ⟨a2, ⟨ha2.le, haL⟩⟩)
    simpa only [zero_sub, abs_neg, abs_of_pos ha2, ENNReal.toReal_ofReal ha2.le] using h
  have hminB : (riemannianEDist I o (intrinsicGeodesic g hEnorm o v₀ b2)).toReal = b2 := by
    rw [← hgeo₁ b2 ⟨hb2.le, hbL⟩]
    have h := congrArg ENNReal.toReal (hnmetric 1 ⟨0, ⟨le_rfl, (hL 1).le⟩⟩
      ⟨b2, ⟨hb2.le, hbL⟩⟩)
    rw [← hstart] at h
    simpa only [zero_sub, abs_neg, abs_of_pos hb2, ENNReal.toReal_ofReal hb2.le] using h
  have h := hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses
    g hEnorm o u v₀ k a1 a2 b1 b2 hk ha1 ha12 hb1 hb12 hu hv₀ hminA hminB (by
      intro s hs t ht y hy
      have hsL : s ∈ Icc 0 (L 0) := ⟨hs.1, hs.2.trans haL⟩
      have htL : t ∈ Icc 0 (L 1) := ⟨ht.1, ht.2.trans hbL⟩
      rw [← hgeo₀ s hsL, ← hgeo₁ t htL] at hy
      simp only [← hdistOf] at hy
      exact hsec s hsL t htL y hy)
  simpa only [← hgeo₀ a1 ⟨ha1.le, ha12.trans haL⟩, ← hgeo₀ a2 ⟨ha2.le, haL⟩,
    ← hgeo₁ b1 ⟨hb1.le, hb12.trans hbL⟩, ← hgeo₁ b2 ⟨hb2.le, hbL⟩,
    ← hdistOf] using h


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparisonAngle_shortening_of_isCompact_closedBall
    {W : Type u} [TopologicalSpace W] [T2Space W] [ChartedSpace H W]
    [IsManifold I ∞ W] [SigmaCompactSpace W]
    (g : SmoothRiemannianMetric I W) (o : W)
    (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ) (k R : ℝ)
    (hk : 0 < k) (hR : 0 < R) (hL : ∀ j, 0 < L j) (hLR : ∀ j, L j ≤ R)
    (hstart : ∀ j, arm j 0 = o)
    (hmetric : ∀ j s, s ∈ Icc 0 (L j) → ∀ t ∈ Icc 0 (L j),
      riemannianEDistOf g (arm j s) (arm j t) = ENNReal.ofReal |s - t|)
    (hcompact : IsCompact {z : W | riemannianEDistOf g o z ≤ ENNReal.ofReal (4 * R)})
    (hsec : ∀ s ∈ Icc 0 (L 0), ∀ t ∈ Icc 0 (L 1), ∀ y : W,
      riemannianEDistOf g (arm 0 s) y + riemannianEDistOf g y (arm 1 t) =
        riemannianEDistOf g (arm 0 s) (arm 1 t) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2))
    (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (haL : a2 ≤ L 0)
    (hb1 : 0 < b1) (hb12 : b1 ≤ b2) (hbL : b2 ≤ L 1) :
    hyperbolicComparisonAngle k a2 b2 (riemannianEDistOf g (arm 0 a2) (arm 1 b2)).toReal ≤
      hyperbolicComparisonAngle k a1 b1 (riemannianEDistOf g (arm 0 a1) (arm 1 b1)).toReal := by
  obtain ⟨g', U, hcomplete, hU, _hballU, heq, _hle, hpreserve⟩ :=
    exists_complete_metric_preserving_closedBall_distances_and_lenses g o hR hcompact
  have hmem (j : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 (L j)) :
      riemannianEDistOf g o (arm j s) ≤ ENNReal.ofReal R := by
    rw [← hstart j, hmetric j 0 ⟨le_rfl, (hL j).le⟩ s hs, zero_sub, abs_neg,
      abs_of_nonneg hs.1]
    exact ENNReal.ofReal_le_ofReal (hs.2.trans (hLR j))
  have hmetric' (j : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 (L j))
      (t : ℝ) (ht : t ∈ Icc 0 (L j)) :
      riemannianEDistOf g' (arm j s) (arm j t) = ENNReal.ofReal |s - t| := by
    rw [(hpreserve (arm j s) (hmem j s hs) (arm j t) (hmem j t ht)).1]
    exact hmetric j s hs t ht
  have hsec' (s : ℝ) (hs : s ∈ Icc 0 (L 0)) (t : ℝ) (ht : t ∈ Icc 0 (L 1))
      (y : W) (hy : riemannianEDistOf g' (arm 0 s) y + riemannianEDistOf g' y (arm 1 t) =
        riemannianEDistOf g' (arm 0 s) (arm 1 t)) :
      SectionalBoundedBelowAt (I := I) g' y (-k ^ 2) := by
    obtain ⟨hlens, hyU⟩ :=
      (hpreserve (arm 0 s) (hmem 0 s hs) (arm 1 t) (hmem 1 t ht)).2 y hy
    exact (sectionalBoundedBelowAt_congr_metric g g' hU heq hyU).2 (hsec s hs t ht y hlens)
  have h := hyperbolic_comparison_of_complete_metric_segments g' hcomplete arm L k hk hL
    ((hstart 0).trans (hstart 1).symm) hmetric' hsec' a1 a2 b1 b2 ha1 ha12 haL hb1 hb12 hbL
  rw [(hpreserve (arm 0 a2) (hmem 0 a2 ⟨(ha1.trans_le ha12).le, haL⟩)
    (arm 1 b2) (hmem 1 b2 ⟨(hb1.trans_le hb12).le, hbL⟩)).1,
    (hpreserve (arm 0 a1) (hmem 0 a1 ⟨ha1.le, ha12.trans haL⟩)
    (arm 1 b1) (hmem 1 b1 ⟨hb1.le, hb12.trans hbL⟩)).1] at h
  exact h


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem metric_arm_triangle_bounds
    {W : Type u} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
    (g : SmoothRiemannianMetric I W) (o : W) (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ)
    (hL : ∀ j, 0 < L j) (hstart : ∀ j, arm j 0 = o)
    (hmetric : ∀ j s, s ∈ Icc 0 (L j) → ∀ t ∈ Icc 0 (L j),
      riemannianEDistOf g (arm j s) (arm j t) = ENNReal.ofReal |s - t|)
    (s t : ℝ) (hs : s ∈ Icc 0 (L 0)) (ht : t ∈ Icc 0 (L 1)) :
    |s - t| ≤ (riemannianEDistOf g (arm 0 s) (arm 1 t)).toReal ∧
      (riemannianEDistOf g (arm 0 s) (arm 1 t)).toReal ≤ s + t := by
  have ha : riemannianEDistOf g o (arm 0 s) = ENNReal.ofReal s := by
    rw [← hstart 0, hmetric 0 0 ⟨le_rfl, (hL 0).le⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  have hb : riemannianEDistOf g o (arm 1 t) = ENNReal.ofReal t := by
    rw [← hstart 1, hmetric 1 0 ⟨le_rfl, (hL 1).le⟩ t ht, zero_sub, abs_neg, abs_of_nonneg ht.1]
  have hupper : riemannianEDistOf g (arm 0 s) (arm 1 t) ≤ ENNReal.ofReal (s + t) := by
    calc
      _ ≤ riemannianEDistOf g (arm 0 s) o + riemannianEDistOf g o (arm 1 t) :=
        riemannianEDistOf_triangle g _ o _
      _ = ENNReal.ofReal (s + t) := by
        rw [riemannianEDistOf_comm g (arm 0 s) o, ha, hb, ← ENNReal.ofReal_add hs.1 ht.1]
  have habfin : riemannianEDistOf g (arm 0 s) (arm 1 t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hab := riemannianEDistOf_toReal_triangle g o (arm 0 s) (arm 1 t)
    (by rw [ha]; exact ENNReal.ofReal_ne_top) habfin
  have hba := riemannianEDistOf_toReal_triangle g o (arm 1 t) (arm 0 s)
    (by rw [hb]; exact ENNReal.ofReal_ne_top)
    (by rw [riemannianEDistOf_comm]; exact habfin)
  rw [ha, hb, ENNReal.toReal_ofReal hs.1, ENNReal.toReal_ofReal ht.1] at hab hba
  rw [riemannianEDistOf_comm g (arm 1 t) (arm 0 s)] at hba
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hs.1 ht.1) hupper

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_comparisonAngle_ge_half_of_sectional_lower_bound_on_minimizing_lenses
    {W : ℕ → Type u} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)]
    [∀ i, ChartedSpace H (W i)] [∀ i, IsManifold I ∞ (W i)]
    [∀ i, SigmaCompactSpace (W i)]
    (g : ∀ i, SmoothRiemannianMetric I (W i)) (o : ∀ i, W i)
    (arm : ∀ i, Fin 2 → ℝ → W i) (L : ℕ → Fin 2 → ℝ) (k : ℕ → ℝ)
    (hk : ∀ i, 0 < k i) (hL : ∀ i j, 0 < L i j)
    (hstart : ∀ i j, arm i j 0 = o i)
    (hmetric : ∀ i j s, s ∈ Icc 0 (L i j) → ∀ t ∈ Icc 0 (L i j),
      riemannianEDistOf (g i) (arm i j s) (arm i j t) = ENNReal.ofReal |s - t|)
    (hcompact : ∀ i, IsCompact {z : W i |
      riemannianEDistOf (g i) (o i) z ≤ ENNReal.ofReal (4 * max (L i 0) (L i 1))})
    (hsec : ∀ i s, s ∈ Icc 0 (L i 0) → ∀ t, t ∈ Icc 0 (L i 1) → ∀ y : W i,
      riemannianEDistOf (g i) (arm i 0 s) y + riemannianEDistOf (g i) y (arm i 1 t) =
        riemannianEDistOf (g i) (arm i 0 s) (arm i 1 t) →
      SectionalBoundedBelowAt (I := I) (g i) y (-k i ^ 2))
    (hlength : ∀ j, Tendsto (fun i => L i j) atTop atTop)
    (hsmall : Tendsto (fun i => k i * max (L i 0) (L i 1)) atTop (𝓝 0))
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ᶠ i in atTop, theta ≤ comparisonAngle (L i 0) (L i 1)
      (riemannianEDistOf (g i) (arm i 0 (L i 0)) (arm i 1 (L i 1))).toReal) :
    ∀ r : ℝ, 0 < r → ∀ᶠ i in atTop, theta / 2 ≤ comparisonAngle r r
      (riemannianEDistOf (g i) (arm i 0 r) (arm i 1 r)).toReal := by
  intro r hr
  have hlarge : ∀ᶠ i in atTop, r ≤ L i 0 ∧ r ≤ L i 1 :=
    ((hlength 0).eventually (eventually_ge_atTop r)).and
      ((hlength 1).eventually (eventually_ge_atTop r))
  have hgood : ∀ᶠ i in atTop,
      0 < k i ∧ 0 < L i 0 ∧ 0 < L i 1 ∧
      |L i 0 - L i 1| ≤
        (riemannianEDistOf (g i) (arm i 0 (L i 0)) (arm i 1 (L i 1))).toReal ∧
      (riemannianEDistOf (g i) (arm i 0 (L i 0)) (arm i 1 (L i 1))).toReal ≤ L i 0 + L i 1 := by
    apply Filter.Eventually.of_forall
    intro i
    exact ⟨hk i, hL i 0, hL i 1,
      metric_arm_triangle_bounds (g i) (o i) (arm i) (L i) (hL i) (hstart i) (hmetric i)
        (L i 0) (L i 1) ⟨(hL i 0).le, le_rfl⟩ ⟨(hL i 1).le, le_rfl⟩⟩
  have hgood' : ∀ᶠ i in atTop,
      0 < k i ∧ 0 < r ∧ 0 < r ∧
      |r - r| ≤ (riemannianEDistOf (g i) (arm i 0 r) (arm i 1 r)).toReal ∧
      (riemannianEDistOf (g i) (arm i 0 r) (arm i 1 r)).toReal ≤ r + r := by
    filter_upwards [hlarge] with i hi
    exact ⟨hk i, hr, hr,
      metric_arm_triangle_bounds (g i) (o i) (arm i) (L i) (hL i) (hstart i) (hmetric i)
        r r ⟨hr.le, hi.1⟩ ⟨hr.le, hi.2⟩⟩
  have hsmall' : Tendsto (fun i => k i * max r r) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun i => mul_nonneg (hk i).le (le_max_left r r |>.trans' hr.le))
      _ hsmall
    filter_upwards [hlarge] with i hi
    exact mul_le_mul_of_nonneg_left (max_le_max hi.1 hi.2) (hk i).le
  apply eventually_comparisonAngle_ge_half_of_hyperbolic_comparison htheta hgood hgood'
    hsmall hsmall' hangle
  filter_upwards [hlarge] with i hi
  have h := hyperbolicComparisonAngle_shortening_of_isCompact_closedBall (g i) (o i)
    (arm i) (L i) (k i) (max (L i 0) (L i 1)) (hk i)
    ((hL i 0).trans_le (le_max_left _ _)) (hL i)
    (fun j => by
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _)
    (hstart i) (hmetric i) (hcompact i) (hsec i)
    r (L i 0) r (L i 1) hr hi.1 le_rfl hr hi.2 le_rfl
  exact h

end DifferentialGeometry.Geometry.Comparison.Toponogov
