import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphCurves
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

/-!
# LC39: buffered distance and ball coverage

Blueprint LC39 (master207A:21690). Let `j : O → M` be a smooth embedding between Riemannian
manifolds of the same dimension (here: a `PartialDiffeomorph` whose source contains the closed
ball `B̄(n, L)`), with `(1-λ)² h ≤ j^*g ≤ (1+λ)² h` on that closed ball, `0 ≤ λ < 1`. Then

* coverage: `B_g(j n, (1-λ) L) ⊆ j (B_h(n, L))`;
* for every `x` with `d_h(n, x) < L`: `(1-λ) d_h(n,x) ≤ d_g(j n, j x) ≤ (1+λ) d_h(n,x)`.

The blueprint also assumes `(1+λ) r < (1-λ) L` for the radial bounds on `B̄(n, r)`; that
condition is not needed (the bounds hold on the whole open ball `B(n, L)`), so the statement
below is stronger. Completeness enters only through compactness of the closed `L`-ball
(Hopf–Rinow), which is taken as the hypothesis `hcpt`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [T3Space M] in
private theorem isClosed_riemannianClosedBallOf' (h : SmoothRiemannianMetric I N) (n : N)
    (r : ℝ) : IsClosed (riemannianClosedBallOf h n r) :=
  isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (I := I) h n) continuous_const

omit [FiniteDimensional ℝ E] [T3Space M] [T3Space N] in
private theorem ball_subset_closedBall' (h : SmoothRiemannianMetric I N) (n : N) (r : ℝ) :
    riemannianBallOf h n r ⊆ riemannianClosedBallOf h n r :=
  fun y hy => by
    change riemannianEDistOf h n y ≤ ENNReal.ofReal r
    exact le_of_lt hy

/-- LC39, coverage: the `g`-ball of radius `(1-λ)L` about `j n` lies in the image of the open
`h`-ball of radius `L`. -/
theorem riemannianBallOf_subset_image_ball_of_buffered (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (j : PartialDiffeomorph I I N M ∞) (n : N) {L lam : ℝ}
    (hlam1 : lam < 1) (hcpt : IsCompact (riemannianClosedBallOf h n L))
    (hsrc : riemannianClosedBallOf h n L ⊆ j.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
      (1 - lam) ^ 2 * h.inner z v v ≤
        g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v)) :
    riemannianBallOf g (j n) ((1 - lam) * L) ⊆ (j : N → M) '' riemannianBallOf h n L := by
  intro y hy
  change riemannianEDistOf g (j n) y < ENNReal.ofReal ((1 - lam) * L) at hy
  have hm : 0 < 1 - lam := by linarith
  set C : ℝ := (1 - lam)⁻¹ with hCdef
  have hC : 0 ≤ C := inv_nonneg.mpr hm.le
  have hfin : riemannianEDistOf g (j n) y ≠ ⊤ :=
    ne_top_of_lt hy
  set δ := (riemannianEDistOf g (j n) y).toReal with hδdef
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hδL : δ < (1 - lam) * L := by
    have hpos : 0 < (1 - lam) * L := by
      by_contra hneg
      push Not at hneg
      rw [ENNReal.ofReal_of_nonpos hneg] at hy
      exact (not_lt_zero hy)
    have hh := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hy
    rwa [ENNReal.toReal_ofReal hpos.le] at hh
  set s := δ / (1 - lam) with hsdef
  have hsL : s < L := by rw [hsdef, div_lt_iff₀ hm]; linarith
  have hs0 : 0 ≤ s := div_nonneg hδ0 hm.le
  set R' := (s + L) / 2 with hR'def
  set A := (1 - lam) * ((s + R') / 2) with hAdef
  set r := (R' - s) / 4 with hrdef
  have hR'L : R' < L := by rw [hR'def]; linarith
  have hsR' : s < R' := by rw [hR'def]; linarith
  have hr : 0 < r := by rw [hrdef]; linarith
  have hCA : C * A = (s + R') / 2 := by
    rw [hAdef, hCdef, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
  have hmargin : C * A + r < R' := by rw [hCA, hrdef]; linarith
  have hsub' : riemannianClosedBallOf h n R' ⊆ riemannianClosedBallOf h n L :=
    riemannianClosedBallOf_mono h n hR'L.le
  have hcpt' : IsCompact (riemannianClosedBallOf h n R') :=
    hcpt.of_isClosed_subset (isClosed_riemannianClosedBallOf' h n R') hsub'
  have hlowerC : ∀ z ∈ riemannianClosedBallOf h n R', ∀ v : TangentSpace I z,
      h.inner z v v ≤ C ^ 2 * g.inner (j z) (mfderiv I I (j : N → M) z v)
        (mfderiv I I (j : N → M) z v) := by
    intro z hz v
    have hl := hlower z (hsub' hz) v
    have hC2 : C ^ 2 * (1 - lam) ^ 2 = 1 := by
      rw [hCdef, ← mul_pow, inv_mul_cancel₀ hm.ne', one_pow]
    calc h.inner z v v = C ^ 2 * ((1 - lam) ^ 2 * h.inner z v v) := by
          rw [← mul_assoc, hC2, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (sq_nonneg C)
  have hn : n ∈ riemannianBallOf h n r := by
    change riemannianEDistOf h n n < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hcover := PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower h g j hC
    hcpt' (hsub'.trans hsrc) hlowerC hn hmargin
  have hyA : y ∈ riemannianBallOf g (j n) A := by
    change riemannianEDistOf g (j n) y < ENNReal.ofReal A
    rw [← ENNReal.ofReal_toReal hfin]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ0).mpr
    rw [hAdef]
    have : (1 - lam) * s = δ := by rw [hsdef]; field_simp
    nlinarith
  obtain ⟨x, hx, rfl⟩ := hcover hyA
  refine ⟨x, ?_, rfl⟩
  change riemannianEDistOf h n x < ENNReal.ofReal L
  exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (by linarith : (0 : ℝ) ≤ R')).mpr hR'L)

omit [FiniteDimensional ℝ E] [T3Space M] [T3Space N] in
/-- LC39, upper radial bound: `d_g(j n, j x) ≤ (1+λ) d_h(n, x)` on the open `L`-ball. -/
theorem riemannianEDistOf_map_le_of_buffered (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (j : PartialDiffeomorph I I N M ∞) (n : N) {L lam : ℝ}
    (hL : 0 < L) (hlam0 : 0 ≤ lam) (hsrc : riemannianClosedBallOf h n L ⊆ j.source)
    (hupper : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        (1 + lam) ^ 2 * h.inner z v v)
    {x : N} (hx : riemannianEDistOf h n x < ENNReal.ofReal L) :
    riemannianEDistOf g (j n) (j x) ≤ ENNReal.ofReal (1 + lam) * riemannianEDistOf h n x :=
  PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball h g j n x hL
    (by linarith) hsrc hupper hx

/-- LC39, lower radial bound: `(1-λ) d_h(n, x) ≤ d_g(j n, j x)` on the open `L`-ball. A curve
that leaves the image of the `L`-ball already costs `(1-λ) L`; one that stays in it lifts. -/
theorem le_riemannianEDistOf_map_of_buffered (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (j : PartialDiffeomorph I I N M ∞) (n : N) {L lam : ℝ}
    (hlam1 : lam < 1) (hcpt : IsCompact (riemannianClosedBallOf h n L))
    (hsrc : riemannianClosedBallOf h n L ⊆ j.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
      (1 - lam) ^ 2 * h.inner z v v ≤
        g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v))
    {x : N} (hx : riemannianEDistOf h n x < ENNReal.ofReal L) :
    ENNReal.ofReal (1 - lam) * riemannianEDistOf h n x ≤ riemannianEDistOf g (j n) (j x) := by
  have hm : 0 < 1 - lam := by linarith
  set C : ℝ := (1 - lam)⁻¹ with hCdef
  have hCpos : 0 < C := inv_pos.mpr hm
  have hL : 0 < L := by
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg] at hx
    exact not_lt_zero hx
  have hxB : x ∈ riemannianClosedBallOf h n L := le_of_lt hx
  have hnB : n ∈ riemannianClosedBallOf h n L := by
    change riemannianEDistOf h n n ≤ ENNReal.ofReal L
    rw [riemannianEDistOf_self]
    exact bot_le
  by_cases hfar : ENNReal.ofReal ((1 - lam) * L) ≤ riemannianEDistOf g (j n) (j x)
  · refine le_trans ?_ hfar
    rw [ENNReal.ofReal_mul hm.le]
    gcongr
  · push Not at hfar
    have hfin : riemannianEDistOf g (j n) (j x) ≠ ⊤ := ne_top_of_lt hfar
    set δ := (riemannianEDistOf g (j n) (j x)).toReal with hδdef
    have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
    have hδL : δ < (1 - lam) * L := by
      have hh := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hfar
      rwa [ENNReal.toReal_ofReal (mul_pos hm hL).le] at hh
    set R := (δ + (1 - lam) * L) / 2 with hRdef
    have hR : 0 < R := by rw [hRdef]; nlinarith [mul_pos hm hL]
    have hδR : δ < R := by rw [hRdef]; linarith
    have hRL : R < (1 - lam) * L := by rw [hRdef]; linarith
    have hcover := riemannianBallOf_subset_image_ball_of_buffered h g j n hlam1 hcpt hsrc hlower
    have hball : riemannianClosedBallOf g (j n) R ⊆ (j : N → M) '' riemannianBallOf h n L := by
      intro y hy
      apply hcover
      change riemannianEDistOf g (j n) y < ENNReal.ofReal ((1 - lam) * L)
      exact lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR.le).mpr hRL)
    have himage : (j : N → M) '' riemannianBallOf h n L ⊆ j.target := by
      rintro _ ⟨z, hz, rfl⟩
      exact j.map_source' (hsrc (ball_subset_closedBall' h n L hz))
    have hlowerC : ∀ z ∈ riemannianClosedBallOf h n L, ∀ v : TangentSpace I z,
        h.inner z v v ≤ C ^ 2 * g.inner (j z) (mfderiv I I (j : N → M) z v)
          (mfderiv I I (j : N → M) z v) := by
      intro z hz v
      have hl := hlower z hz v
      have hC2 : C ^ 2 * (1 - lam) ^ 2 = 1 := by
        rw [hCdef, ← mul_pow, inv_mul_cancel₀ hm.ne', one_pow]
      calc h.inner z v v = C ^ 2 * ((1 - lam) ^ 2 * h.inner z v v) := by
            rw [← mul_assoc, hC2, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (sq_nonneg C)
    have hinv := PartialDiffeomorph.metric_upper_symm_of_metric_lower j h g hsrc hlowerC
    have hupperS : ∀ z ∈ riemannianClosedBallOf g (j n) R, ∀ w : TangentSpace I z,
        h.inner (j.symm z) (mfderiv I I (j.symm : M → N) z w)
          (mfderiv I I (j.symm : M → N) z w) ≤ C ^ 2 * g.inner z w w := by
      intro z hz w
      obtain ⟨y, hy, hyz⟩ := hball hz
      exact hinv z ⟨y, ball_subset_closedBall' h n L hy, hyz⟩ w
    have hxR : riemannianEDistOf g (j n) (j x) < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ0).mpr hδR
    have hmain := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      g h j.symm (j n) (j x) hR hCpos
      (fun z hz => by
        obtain ⟨y, hy, hyz⟩ := hball hz
        rw [← hyz]
        exact j.map_source' (hsrc (ball_subset_closedBall' h n L hy)))
      hupperS hxR
    have hn' : j.symm (j n) = n := j.left_inv (hsrc hnB)
    have hx' : j.symm (j x) = x := j.left_inv (hsrc hxB)
    rw [hn', hx'] at hmain
    calc ENNReal.ofReal (1 - lam) * riemannianEDistOf h n x
        ≤ ENNReal.ofReal (1 - lam) * (ENNReal.ofReal C * riemannianEDistOf g (j n) (j x)) :=
          by gcongr
      _ = riemannianEDistOf g (j n) (j x) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hm.le, hCdef, mul_inv_cancel₀ hm.ne',
            ENNReal.ofReal_one, one_mul]

end DifferentialGeometry
