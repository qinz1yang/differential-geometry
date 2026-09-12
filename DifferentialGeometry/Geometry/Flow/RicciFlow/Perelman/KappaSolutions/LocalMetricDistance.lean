import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped _root_.Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem metricPathELength_comp_le
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    {gamma : ℝ → N} {a b L : ℝ} (hL : 0 ≤ L)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hsource : ∀ s ∈ Icc a b, gamma s ∈ F.source)
    (hupper : ∀ s ∈ Ioo a b, ∀ v : TangentSpace I (gamma s),
      g.inner (F (gamma s)) (mfderiv I I (F : N → M) (gamma s) v)
        (mfderiv I I (F : N → M) (gamma s) v) ≤
      L ^ 2 * h.inner (gamma s) v v) :
    metricPathELength (I := I) g ((F : N → M) ∘ gamma) a b ≤
      ENNReal.ofReal L * metricPathELength (I := I) h gamma a b := by
  rw [metricPathELength_eq, metricPathELength_eq, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hFd := (F.contMDiffOn_toFun.contMDiffAt
    (F.open_source.mem_nhds (hsource s ⟨hs.1.le, hs.2.le⟩))).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hgd := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  change Real.sqrt (g.inner (F (gamma s))
      (mfderiv 𝓘(ℝ, ℝ) I ((F : N → M) ∘ gamma) s 1)
      (mfderiv 𝓘(ℝ, ℝ) I ((F : N → M) ∘ gamma) s 1)) ≤ _
  rw [mfderiv_comp_apply s hFd hgd]
  calc
    _ ≤ Real.sqrt (L ^ 2 * h.inner (gamma s)
        (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)) :=
      Real.sqrt_le_sqrt (hupper s hs _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

theorem edistOf_map_le_of_metric_upper_on_ball
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p y : N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hupper : ∀ z ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I z,
      g.inner (F z) (mfderiv I I (F : N → M) z v)
        (mfderiv I I (F : N → M) z v) ≤ L ^ 2 * h.inner z v v)
    (hy : riemannianEDistOf (I := I) h p y < ENNReal.ofReal R) :
    riemannianEDistOf (I := I) g (F p) (F y) ≤
      ENNReal.ofReal L * riemannianEDistOf (I := I) h p y := by
  let d : ℝ := (riemannianEDistOf (I := I) h p y).toReal
  have hfin : riemannianEDistOf (I := I) h p y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hdR : d < R := by
    have hh := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hy
    simpa only [ENNReal.toReal_ofReal hR.le] using hh
  have hdeq : ENNReal.ofReal d = riemannianEDistOf (I := I) h p y :=
    ENNReal.ofReal_toReal hfin
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have heps : 0 < (epsilon : ℝ) := hepsilon
  let eta : ℝ := min ((epsilon : ℝ) / (L + 1)) ((R - d) / 2)
  have heta : 0 < eta := lt_min (div_pos heps (by linarith)) (by linarith)
  have hetale : eta ≤ (epsilon : ℝ) / (L + 1) := min_le_left _ _
  have hLenEta : L * eta ≤ (epsilon : ℝ) := by
    have hh := (le_div_iff₀ (by linarith : 0 < L + 1)).1 hetale
    nlinarith
  have hdeta : d + eta < R := by
    have hh : eta ≤ (R - d) / 2 := min_le_right _ _
    linarith
  have hshort : riemannianEDistOf (I := I) h p y < ENNReal.ofReal (d + eta) := by
    rw [← hdeq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < d + eta)).2 (by linarith)
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ := exists_lt_of_edistOf_lt h hshort
  have hstay : ∀ s ∈ Icc (0 : ℝ) 1,
      gamma s ∈ riemannianClosedBallOf (I := I) h p R := by
    intro s hs
    have hprefix := edistOf_le_metricPathELength h hs.1
      (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
    rw [hzero] at hprefix
    exact ((hprefix.trans (metricPathELength_mono h gamma le_rfl hs.2)).trans
      hlength.le).trans (ENNReal.ofReal_le_ofReal hdeta.le)
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ) I 1 ((F : N → M) ∘ gamma) (Icc 0 1) :=
    (F.contMDiffOn_toFun.of_le (by simp)).comp hgamma
      (fun s hs => hsource (hstay s hs))
  have hdist := edistOf_le_metricPathELength g (by norm_num : (0 : ℝ) ≤ 1) hmap
  simp only [Function.comp_apply, hzero, hone] at hdist
  have hlengthMap := metricPathELength_comp_le h g F hL.le hgamma
    (fun s hs => hsource (hstay s hs))
    (fun s hs => hupper (gamma s) (hstay s ⟨hs.1.le, hs.2.le⟩))
  calc
    _ ≤ ENNReal.ofReal L * metricPathELength (I := I) h gamma 0 1 :=
      hdist.trans hlengthMap
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal (d + eta) := mul_le_mul' le_rfl hlength.le
    _ = ENNReal.ofReal (L * d + L * eta) := by
      rw [← ENNReal.ofReal_mul hL.le, mul_add]
    _ ≤ ENNReal.ofReal (L * d + (epsilon : ℝ)) :=
      ENNReal.ofReal_le_ofReal (add_le_add le_rfl hLenEta)
    _ = ENNReal.ofReal L * riemannianEDistOf (I := I) h p y + epsilon := by
      rw [ENNReal.ofReal_add (mul_nonneg hL.le hd) epsilon.coe_nonneg,
        ENNReal.ofReal_mul hL.le, hdeq]
      simp

private theorem edistOf_triangle
    (h : SmoothRiemannianMetric I N) (x y z : N) :
    riemannianEDistOf (I := I) h x z ≤
      riemannianEDistOf (I := I) h x y + riemannianEDistOf (I := I) h y z := by
  let : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

private theorem edistOf_comm
    (h : SmoothRiemannianMetric I N) (x y : N) :
    riemannianEDistOf (I := I) h x y = riemannianEDistOf (I := I) h y x := by
  let : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

theorem edistOf_map_le_of_metric_upper_on_buffered_ball
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p x y : N)
    {R r L : ℝ} (hr : 0 ≤ r) (hbuffer : 3 * r < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hupper : ∀ z ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I z,
      g.inner (F z) (mfderiv I I (F : N → M) z v)
        (mfderiv I I (F : N → M) z v) ≤ L ^ 2 * h.inner z v v)
    (hx : x ∈ riemannianClosedBallOf (I := I) h p r)
    (hy : y ∈ riemannianClosedBallOf (I := I) h p r) :
    riemannianEDistOf (I := I) g (F x) (F y) ≤
      ENNReal.ofReal L * riemannianEDistOf (I := I) h x y := by
  have hmargin : 0 < R - r := by linarith
  have hball : riemannianClosedBallOf (I := I) h x (R - r) ⊆
      riemannianClosedBallOf (I := I) h p R := by
    intro z hz
    calc
      riemannianEDistOf (I := I) h p z ≤
          riemannianEDistOf (I := I) h p x + riemannianEDistOf (I := I) h x z :=
        edistOf_triangle h p x z
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal (R - r) := add_le_add hx hz
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_add hr hmargin.le]
        congr 1
        ring
  have hxy : riemannianEDistOf (I := I) h x y < ENNReal.ofReal (R - r) := by
    have hxp : riemannianEDistOf (I := I) h x p ≤ ENNReal.ofReal r := by
      rw [edistOf_comm h x p]
      exact hx
    calc
      _ ≤ riemannianEDistOf (I := I) h x p + riemannianEDistOf (I := I) h p y :=
        edistOf_triangle h x p y
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add hxp hy
      _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr hr, two_mul]
      _ < ENNReal.ofReal (R - r) :=
        (ENNReal.ofReal_lt_ofReal_iff hmargin).2 (by linarith)
  exact edistOf_map_le_of_metric_upper_on_ball h g F x y hmargin hL
    (hball.trans hsource) (fun z hz => hupper z (hball hz)) hxy

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
