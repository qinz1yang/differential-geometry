import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessMovingNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessModelRecenter


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance strictNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem scaled_closedBall_eq (g : SmoothRiemannianMetric I M)
    {c : ℝ} (hc : 0 < c) (p : M) (R : ℝ) :
    riemannianClosedBallOf (scaleMetric c hc g) p R =
      riemannianClosedBallOf g p (R / Real.sqrt c) := by
  have hh := riemannianClosedBallOf_scaleMetric c hc g p (R / Real.sqrt c)
  have hcancel : Real.sqrt c * (R / Real.sqrt c) = R := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hc)]
  rwa [hcancel] at hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem scaled_closedBall_mem_of_limit (g : SmoothRiemannianMetric I M)
    (center y : ℕ → M) {p y₀ : M}
    (hcenter : Tendsto center atTop (𝓝 p)) (hy : Tendsto y atTop (𝓝 y₀))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀)) (R : ℝ)
    (hball : ∀ n, y n ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) g) (center n) R) :
    y₀ ∈ riemannianClosedBallOf (scaleMetric c₀ hc₀ g) p R := by
  have hbound (n : ℕ) : riemannianEDistOf g p (y n) ≤
      riemannianEDistOf g p (center n) + ENNReal.ofReal (R / Real.sqrt (c n)) := by
    have hh := hball n
    rw [scaled_closedBall_eq] at hh
    change riemannianEDistOf g (center n) (y n) ≤ ENNReal.ofReal (R / Real.sqrt (c n)) at hh
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact (Manifold.riemannianEDist_triangle (I := I) (x := p) (y := center n) (z := y n)).trans
      (add_le_add le_rfl hh)
  have hleft : Tendsto (fun n => riemannianEDistOf g p (y n)) atTop
      (𝓝 (riemannianEDistOf g p y₀)) := (continuous_riemannianEDist g p).tendsto y₀ |>.comp hy
  have hcenter' : Tendsto (fun n => riemannianEDistOf g p (center n)) atTop
      (𝓝 (riemannianEDistOf g p p)) := (continuous_riemannianEDist g p).tendsto p |>.comp hcenter
  have hradius : Tendsto (fun n => ENNReal.ofReal (R / Real.sqrt (c n))) atTop
      (𝓝 (ENNReal.ofReal (R / Real.sqrt c₀))) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_const_nhds.div hclim.sqrt (ne_of_gt (Real.sqrt_pos.mpr hc₀)))
  have hle := le_of_tendsto_of_tendsto hleft (hcenter'.add hradius)
    (Filter.Eventually.of_forall hbound)
  rw [riemannianEDistOf_self, zero_add] at hle
  rw [scaled_closedBall_eq]
  exact hle


theorem eventually_strict_weighted_error_norm_on_scaled_ball
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (p : M) (R : ℝ) {K : Set M} (hK : IsCompact K)
    {J L : Set ℝ}
    (hregular : ∀ y ∈ K, ∃ V : Set E, IsOpen V ∧ extChartAt I y y ∈ V ∧
      V ⊆ (extChartAt I y).target ∧
      (∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) y i j z.2) (L ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => A z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2))) (J ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => B z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2))) (L ×ˢ V)))
    (center : ℕ → M) (hcenter : Tendsto center atTop (𝓝 p))
    (t Q c alpha beta : ℕ → ℝ) {t₀ Q₀ c₀ alpha₀ beta₀ : ℝ}
    (hQ₀ : 0 < Q₀) (hc : ∀ n, 0 < c n) (hc₀ : 0 < c₀)
    (htlim : Tendsto t atTop (𝓝 t₀)) (hQlim : Tendsto Q atTop (𝓝 Q₀))
    (hclim : Tendsto c atTop (𝓝 c₀)) (halim : Tendsto alpha atTop (𝓝 alpha₀))
    (hblim : Tendsto beta atTop (𝓝 beta₀))
    {lo hi eps : ℝ} (order : ℕ)
    (hcontain : ∀ n, riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R ⊆ K)
    (hsource : ∀ n s, s ∈ Icc lo hi → t n + s / Q n ∈ J)
    (hmodel : ∀ n s, s ∈ Icc lo hi → s / c n ∈ L)
    (hsource₀ : ∀ s ∈ Icc lo hi, t₀ + s / Q₀ ∈ J)
    (hmodel₀ : ∀ s ∈ Icc lo hi, s / c₀ ∈ L)
    (hstrict : ∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric c₀ hc₀ (g 0)) p R,
        tensor02CovDerivNormWith (I := I) order
          (alpha₀ • A (t₀ + s / Q₀) - beta₀ • B (s / c₀))
          (scaleMetric c₀ hc₀ (g (s / c₀))) (scaleMetric c₀ hc₀ (g (s / c₀))) y < eps) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R,
        tensor02CovDerivNormWith (I := I) order
          (alpha n • A (t n + s / Q n) - beta n • B (s / c n))
          (scaleMetric (c n) (hc n) (g (s / c n)))
          (scaleMetric (c n) (hc n) (g (s / c n))) y < eps := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let f (n : ℕ) (s : ℝ) (y : M) := tensor02CovDerivNormWith (I := I) order
    (alpha n • A (t n + s / Q n) - beta n • B (s / c n))
    (scaleMetric (c n) (hc n) (g (s / c n))) (scaleMetric (c n) (hc n) (g (s / c n))) y
  change ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
    ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R, f n s y < eps
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ (∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R,
        f n s y < eps) := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hbad' (n : ℕ) : ∃ s ∈ Icc lo hi,
      ∃ y ∈ riemannianClosedBallOf (scaleMetric (c (ns n)) (hc (ns n)) (g 0)) (center (ns n)) R,
        eps ≤ f (ns n) s y := by
    have hh := hbad n
    push Not at hh
    exact hh
  choose s hs y hy hbadnorm using hbad'
  obtain ⟨w, hw, phi, hphi, hwlim⟩ := (isCompact_Icc.prod hK).tendsto_subseq
    (x := fun n => (s n, y n)) (fun n => ⟨hs n, hcontain (ns n) (hy n)⟩)
  let pick := ns ∘ phi
  have hpick : Tendsto pick atTop atTop := hns.comp hphi.tendsto_atTop
  have hslim : Tendsto (fun n => s (phi n)) atTop (𝓝 w.1) :=
    (continuous_fst.tendsto w).comp hwlim
  have hylim : Tendsto (fun n => y (phi n)) atTop (𝓝 w.2) :=
    (continuous_snd.tendsto w).comp hwlim
  have hwball := scaled_closedBall_mem_of_limit (g 0) (fun n => center (pick n))
    (fun n => y (phi n)) (hcenter.comp hpick) hylim (fun n => c (pick n))
    (fun n => hc (pick n)) hc₀ (hclim.comp hpick) R (fun n => hy (phi n))
  obtain ⟨V, hV, hwV, hVt, hgram, hA, hB⟩ := hregular w.2 hw.2
  have hsourcelim : Tendsto (fun n => t (pick n) + s (phi n) / Q (pick n)) atTop
      (𝓝 (t₀ + w.1 / Q₀)) := (htlim.comp hpick).add (hslim.div (hQlim.comp hpick) hQ₀.ne')
  have hmodellim : Tendsto (fun n => s (phi n) / c (pick n)) atTop (𝓝 (w.1 / c₀)) :=
    hslim.div (hclim.comp hpick) hc₀.ne'
  have hnorm := weighted_error_covariant_norm_tendsto_at_point g A B w.2 hV hwV hVt
    hgram hA hB (fun n => t (pick n) + s (phi n) / Q (pick n))
    (fun n => s (phi n) / c (pick n))
    (fun n => hsource (pick n) (s (phi n)) (hs (phi n)))
    (fun n => hmodel (pick n) (s (phi n)) (hs (phi n)))
    (hsource₀ w.1 hw.1) (hmodel₀ w.1 hw.1) hsourcelim hmodellim
    (fun n => c (pick n)) (fun n => alpha (pick n)) (fun n => beta (pick n))
    (fun n => hc (pick n)) hc₀ (hclim.comp hpick) (halim.comp hpick) (hblim.comp hpick)
    (fun n => y (phi n)) hylim order
  have hge := ge_of_tendsto hnorm (Filter.Eventually.of_forall (fun n => hbadnorm (phi n)))
  exact (not_le_of_gt (hstrict w.1 hw.1 w.2 hwball)) hge

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
