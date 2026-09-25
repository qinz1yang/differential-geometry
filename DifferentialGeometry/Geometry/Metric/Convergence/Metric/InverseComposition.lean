import DifferentialGeometry.Geometry.Metric.Convergence.Metric.MapDistance
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (crossModel_edist_le_of_metric_upper crossModel_toReal_transfer)

variable {E E' E'' H H' H'' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section InnerBounds
variable {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

omit [FiniteDimensional ℝ E] [T2Space M] [T2Space N] in
private theorem inverse_composition_inner_bounds
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (s : SmoothRiemannianMetric K P)
    (A : PartialDiffeomorph I K M P ∞) (B : PartialDiffeomorph J K N P ∞)
    {x : M} (hx : x ∈ (A.trans B.symm).source)
    {alpha beta : ℝ} (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hA : ∀ v : TangentSpace I x,
      (1 - alpha) * g.inner x v v ≤ s.inner (A x)
        (mfderiv I K A x v) (mfderiv I K A x v) ∧
      s.inner (A x) (mfderiv I K A x v) (mfderiv I K A x v) ≤
        (1 + alpha) * g.inner x v v)
    (hB : ∀ v : TangentSpace J (A.trans B.symm x),
      (1 - beta) * h.inner (A.trans B.symm x) v v ≤
        s.inner (B (A.trans B.symm x))
          (mfderiv J K B (A.trans B.symm x) v) (mfderiv J K B (A.trans B.symm x) v) ∧
      s.inner (B (A.trans B.symm x))
          (mfderiv J K B (A.trans B.symm x) v) (mfderiv J K B (A.trans B.symm x) v) ≤
        (1 + beta) * h.inner (A.trans B.symm x) v v) :
    ∀ v : TangentSpace I x,
      (1 - alpha) / (1 + beta) * g.inner x v v ≤
        h.inner (A.trans B.symm x) (mfderiv I J (A.trans B.symm) x v)
          (mfderiv I J (A.trans B.symm) x v) ∧
      h.inner (A.trans B.symm x) (mfderiv I J (A.trans B.symm) x v)
          (mfderiv I J (A.trans B.symm) x v) ≤
        (1 + alpha) / (1 - beta) * g.inner x v v := by
  let C := A.trans B.symm
  have heq : (B : N → P) ∘ C =ᶠ[𝓝 x] A := by
    filter_upwards [C.open_source.mem_nhds hx] with y hy
    exact B.right_inv hy.2
  have hpoint : B (C x) = A x := heq.eq_of_nhds
  have hd (v : TangentSpace I x) :
      mfderiv J K B (C x) (mfderiv I J C x v) = mfderiv I K A x v := by
    have hc := C.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hx
    have hb := B.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) (B.map_target hx.2)
    exact (mfderiv_comp_apply x hb hc v).symm.trans
      (DFunLike.congr_fun (heq.mfderiv_eq (I := I) (I' := K)) v)
  intro v
  have hh := hB (mfderiv I J C x v)
  have ha := hA v
  change (1 - beta) * h.inner (C x) (mfderiv I J C x v) (mfderiv I J C x v) ≤
    s.inner (B (C x)) (mfderiv J K B (C x) (mfderiv I J C x v))
      (mfderiv J K B (C x) (mfderiv I J C x v)) ∧
    s.inner (B (C x)) (mfderiv J K B (C x) (mfderiv I J C x v))
      (mfderiv J K B (C x) (mfderiv I J C x v)) ≤
    (1 + beta) * h.inner (C x) (mfderiv I J C x v) (mfderiv I J C x v) at hh
  erw [hd v, hpoint] at hh
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + beta)]
    nlinarith only [ha.1, hh.2]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < 1 - beta)]
    nlinarith only [ha.2, hh.1]

end InnerBounds

private theorem exists_distance_comparison_of_quadratic_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    (Hn : ℕ → SmoothRiemannianMetric J N)
    (C : ℕ → PartialDiffeomorph I J M N ∞)
    {s : ℝ} (hs : 0 < s)
    (hcompact : IsCompact (riemannianClosedBallOf g p (8 * s)))
    (hsource : ∀ᶠ i in atTop, riemannianClosedBallOf g p (2 * s) ⊆ (C i).source)
    (hmetricconv : ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf g p (2 * s), ∀ v : TangentSpace I y,
        (1 - eps) * g.inner y v v ≤ (Hn i).inner (C i y)
          (mfderiv I J (C i) y v) (mfderiv I J (C i) y v) ∧
        (Hn i).inner (C i y) (mfderiv I J (C i) y v)
          (mfderiv I J (C i) y v) ≤ (1 + eps) * g.inner y v v) :
    ∃ r : ℝ, 0 < r ∧ r < s ∧ IsCompact (riemannianClosedBallOf g p r) ∧
      (∀ᶠ i in atTop, riemannianClosedBallOf g p r ⊆ (C i).source ∧
        riemannianClosedBallOf (Hn i) (C i p) (r / 4) ⊆
          (C i) '' riemannianClosedBallOf g p r) ∧
      ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
        ∀ a ∈ riemannianClosedBallOf g p r, ∀ b ∈ riemannianClosedBallOf g p r,
          |(riemannianEDistOf (Hn i) (C i a) (C i b)).toReal -
            (riemannianEDistOf g a b).toReal| < eps := by
  let r := s / 10
  have hr : 0 < r := by positivity
  have hc (t : ℝ) (hts : t ≤ 8 * s) : IsCompact (riemannianClosedBallOf g p t) :=
    hcompact.of_isClosed_subset (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g p) continuous_const)
      (riemannianClosedBallOf_mono _ _ hts)
  have hr2 : r ≤ 2 * s := by dsimp [r]; linarith
  have hsub : riemannianClosedBallOf g p r ⊆ riemannianClosedBallOf g p (2 * s) :=
    riemannianClosedBallOf_mono _ _ hr2
  refine ⟨r, hr, by dsimp [r]; linarith, hc r (by linarith), ?_, ?_⟩
  · filter_upwards [hsource, hmetricconv (1 / 4) (by norm_num)] with i hi hmi
    refine ⟨hsub.trans hi, ?_⟩
    apply DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower
      g (Hn i) (C i) p hr (by norm_num : 0 < (2 : ℝ)) (by linarith)
      (hc r (by linarith)) (hsub.trans hi)
    intro y hy v
    have hh := (hmi y (hsub hy) v).1
    have hg := metric_inner_self_nonneg g y v
    nlinarith only [hh, hg]
  intro eps heps
  let eta := min (eps / (4 * r + 1)) (1 / 4)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have heta4 : eta ≤ 1 / 4 := min_le_right _ _
  have hetaE : eta * (4 * r + 1) ≤ eps :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  filter_upwards [hsource, hmetricconv eta heta] with i hi hmi
  have hplus : Real.sqrt (1 + eta) ≤ 1 + eta :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hminus : 1 - eta ≤ Real.sqrt (1 - eta) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [heta.le, heta4]
  have hroom : Real.sqrt (1 + eta) * (3 * r) < Real.sqrt (1 - eta) * (2 * s) := by
    have hu : Real.sqrt (1 + eta) ≤ 3 / 2 := hplus.trans (by linarith)
    have hl : 1 / 2 ≤ Real.sqrt (1 - eta) := (by linarith : (1 / 2 : ℝ) ≤ 1 - eta).trans hminus
    have hrdef : r = s / 10 := rfl
    nlinarith only [mul_le_mul_of_nonneg_right hu (show 0 ≤ 3 * r by positivity),
      mul_le_mul_of_nonneg_right hl (show 0 ≤ 2 * s by positivity), hs, hrdef]
  have hd := crossModel_toReal_transfer g (Hn i) (C i) p (show 0 < 2 * s by positivity)
    heta.le (by linarith) hr.le (hc _ (by linarith)) hi hmi hroom
  intro a ha b hb
  have hpairs := hd a ha b hb
  have hnonneg := ENNReal.toReal_nonneg (a := riemannianEDistOf g a b)
  have hdiam : (riemannianEDistOf g a b).toReal ≤ 2 * r := by
    have hdist : riemannianEDistOf g a b ≤ ENNReal.ofReal (2 * r) := by
      calc
        _ ≤ riemannianEDistOf g a p + riemannianEDistOf g p b :=
          riemannianEDistOf_triangle g a p b
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
          rw [riemannianEDistOf_comm g a p]
          exact add_le_add ha hb
        _ = ENNReal.ofReal (2 * r) := by
          rw [← ENNReal.ofReal_add hr.le hr.le]; congr 1; ring
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ 2 * r by positivity)] using hh
  have hl := (mul_le_mul_of_nonneg_right hminus hnonneg).trans hpairs.1
  have hu := hpairs.2.trans (mul_le_mul_of_nonneg_right hplus hnonneg)
  have herr : eta * (riemannianEDistOf g a b).toReal < eps := by
    nlinarith only [mul_le_mul_of_nonneg_left hdiam heta.le, hetaE, heta, hr]
  exact abs_lt.mpr ⟨by nlinarith only [hl, herr], by nlinarith only [hu, herr]⟩

variable {P : ℕ → Type*} [∀ n, TopologicalSpace (P n)]
  [∀ n, ChartedSpace H'' (P n)] [∀ n, IsManifold K ∞ (P n)]

omit [T2Space N] in
private theorem exists_inverse_composition_domain_of_tendsto_marks
    (gInf gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hSeq : ∀ n, SmoothRiemannianMetric K (P n))
    (hend : ℕ → SmoothRiemannianMetric J N)
    (A : ∀ n, PartialDiffeomorph I K M (P n) ∞)
    (B : ∀ n, PartialDiffeomorph J K N (P n) ∞)
    (p : M) {Rsrc Rend : ℝ} (hRsrc : 0 < Rsrc) (hRend : 0 < Rend)
    (hcompact : IsCompact (riemannianClosedBallOf gInf p Rsrc))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf gInf p Rsrc) 0 gSeq gInf gRef)
    (hAsource : ∀ᶠ n in atTop, riemannianClosedBallOf gInf p Rsrc ⊆ (A n).source)
    (hAmetric : ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf gInf p Rsrc,
      ∀ v : TangentSpace I y,
        (gSeq n).inner y v v = (hSeq n).inner (A n y)
          (mfderiv I K (A n) y v) (mfderiv I K (A n) y v))
    {u : ℕ → M} (x : ℕ → N) (hu : Tendsto u atTop (𝓝 p))
    (hmark : ∀ᶠ n in atTop, A n (u n) = B n (x n))
    (hBsource : ∀ᶠ n in atTop,
      riemannianClosedBallOf (hend n) (x n) Rend ⊆ (B n).source)
    (hcapture : ∀ᶠ n in atTop,
      riemannianClosedBallOf (hSeq n) (B n (x n)) (Rend / 4) ⊆
        (B n) '' riemannianClosedBallOf (hend n) (x n) Rend) :
    ∃ s : ℝ, 0 < s ∧ 8 * s ≤ Rsrc ∧ s < Rend / 100 ∧
      IsCompact (riemannianClosedBallOf gInf p (8 * s)) ∧
      ∀ᶠ n in atTop,
        riemannianClosedBallOf gInf p (2 * s) ⊆ ((A n).trans (B n).symm).source ∧
        (∀ y ∈ riemannianClosedBallOf gInf p (2 * s),
          (A n).trans (B n).symm y ∈ riemannianClosedBallOf (hend n) (x n) Rend) ∧
        u n ∈ ((A n).trans (B n).symm).source ∧
        (A n).trans (B n).symm (u n) = x n := by
  let s : ℝ := min (Rsrc / 16) (Rend / 200)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsR : s ≤ Rsrc / 16 := min_le_left _ _
  have hsE : s ≤ Rend / 200 := min_le_right _ _
  have hs8 : 8 * s ≤ Rsrc := by linarith
  have hs2 : 2 * s < Rsrc := by linarith
  refine ⟨s, hs, hs8, by linarith, ?_, ?_⟩
  · exact hcompact.of_isClosed_subset
      (Geometry.Metric.isClosed_riemannianClosedBallOf gInf p (8 * s))
      (riemannianClosedBallOf_mono gInf p hs8)
  have hoff := tendsto_riemannianEDistOf_map_zero_of_metricCPConvergenceOn
    gInf gRef gSeq hSeq A p hRsrc hcompact hconv hAsource hAmetric hu
  have hsmall : ∀ᶠ n in atTop,
      riemannianEDistOf (hSeq n) (A n p) (A n (u n)) < ENNReal.ofReal (Rend / 8) :=
    hoff.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  have humem : ∀ᶠ n in atTop, u n ∈ riemannianClosedBallOf gInf p (2 * s) :=
    hu.eventually (mem_interior_iff_mem_nhds.mp
      (Geometry.Metric.mem_interior_riemannianClosedBallOf gInf p (by positivity)))
  filter_upwards [hAsource, hAmetric, hmark, hBsource, hcapture, hsmall, humem,
    hconv.eventually_quadratic_bounds hcompact (by norm_num : (0 : ℝ) < 3)]
    with n hAs hAm hm hBs hc ho hu' hquad
  have hlocal (y : M) (hy : y ∈ riemannianClosedBallOf gInf p (2 * s)) :
      y ∈ ((A n).trans (B n).symm).source ∧
        (A n).trans (B n).symm y ∈ riemannianClosedBallOf (hend n) (x n) Rend := by
    have hyR : y ∈ riemannianClosedBallOf gInf p Rsrc :=
      riemannianClosedBallOf_mono gInf p hs2.le hy
    have hd : riemannianEDistOf (hSeq n) (A n p) (A n y) ≤ ENNReal.ofReal (4 * s) := by
      have hb := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        gInf (hSeq n) (A n) p y hRsrc (by norm_num : (0 : ℝ) < 2) hAs
        (fun z hz v => by
          rw [← hAm z hz v]
          convert (hquad z hz v).2 using 1
          norm_num)
        (hy.trans_lt (ENNReal.ofReal_lt_ofReal_iff hRsrc |>.mpr hs2))
      refine hb.trans ?_
      calc
        ENNReal.ofReal 2 * riemannianEDistOf gInf p y ≤
            ENNReal.ofReal 2 * ENNReal.ofReal (2 * s) := mul_le_mul' le_rfl hy
        _ = ENNReal.ofReal (4 * s) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
    have hcball : A n y ∈ riemannianClosedBallOf (hSeq n) (B n (x n)) (Rend / 4) := by
      change riemannianEDistOf (hSeq n) (B n (x n)) (A n y) ≤ _
      rw [← hm]
      calc
        _ ≤ riemannianEDistOf (hSeq n) (A n (u n)) (A n p) +
            riemannianEDistOf (hSeq n) (A n p) (A n y) :=
          riemannianEDistOf_triangle (hSeq n) _ _ _
        _ ≤ ENNReal.ofReal (Rend / 8) + ENNReal.ofReal (4 * s) := by
          rw [riemannianEDistOf_comm (hSeq n) (A n (u n)) (A n p)]
          exact add_le_add ho.le hd
        _ = ENNReal.ofReal (Rend / 8 + 4 * s) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ ≤ ENNReal.ofReal (Rend / 4) := ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨z, hz, heq⟩ := hc hcball
    have hzsource : z ∈ (B n).source := hBs hz
    have hyB : A n y ∈ (B n).target := heq ▸ (B n).map_source hzsource
    have hback : (B n).symm (A n y) = z := by
      rw [← heq]
      exact (B n).left_inv hzsource
    refine ⟨⟨hAs hyR, hyB⟩, ?_⟩
    change (B n).symm (A n y) ∈ _
    rw [hback]
    exact hz
  refine ⟨fun y hy => (hlocal y hy).1, fun y hy => (hlocal y hy).2,
    (hlocal (u n) hu').1, ?_⟩
  change (B n).symm (A n (u n)) = x n
  rw [hm]
  apply (B n).left_inv
  apply hBs
  change riemannianEDistOf (hend n) (x n) (x n) ≤ _
  rw [riemannianEDistOf_self]
  exact bot_le


theorem exists_inverse_composition_distance_comparison_of_tendsto_marks
    (gInf gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (Hseq : ∀ n, SmoothRiemannianMetric K (P n))
    (hend : ℕ → SmoothRiemannianMetric J N)
    (A : ∀ n, PartialDiffeomorph I K M (P n) ∞)
    (B : ∀ n, PartialDiffeomorph J K N (P n) ∞)
    (p : M) {Rsrc Rend : ℝ} (hRsrc : 0 < Rsrc) (hRend : 0 < Rend)
    (hcompact : IsCompact (riemannianClosedBallOf gInf p Rsrc))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf gInf p Rsrc) 0 gSeq gInf gRef)
    (hAsource : ∀ᶠ n in atTop, riemannianClosedBallOf gInf p Rsrc ⊆ (A n).source)
    (hAmetric : ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf gInf p Rsrc,
      ∀ v : TangentSpace I y, (gSeq n).inner y v v =
        (Hseq n).inner (A n y) (mfderiv I K (A n) y v) (mfderiv I K (A n) y v))
    {u : ℕ → M} (x : ℕ → N) (hu : Tendsto u atTop (𝓝 p))
    (hmark : ∀ᶠ n in atTop, A n (u n) = B n (x n))
    (hBsource : ∀ᶠ n in atTop,
      riemannianClosedBallOf (hend n) (x n) Rend ⊆ (B n).source)
    (hcapture : ∀ᶠ n in atTop,
      riemannianClosedBallOf (Hseq n) (B n (x n)) (Rend / 4) ⊆
        (B n) '' riemannianClosedBallOf (hend n) (x n) Rend)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (hend n) (x n) Rend, ∀ v : TangentSpace J y,
        (1 - eta) * (hend n).inner y v v ≤ (Hseq n).inner (B n y)
          (mfderiv J K (B n) y v) (mfderiv J K (B n) y v) ∧
        (Hseq n).inner (B n y) (mfderiv J K (B n) y v) (mfderiv J K (B n) y v) ≤
          (1 + eta) * (hend n).inner y v v) :
    let C := fun n => (A n).trans (B n).symm
    ∃ r : ℝ, 0 < r ∧ r < Rsrc ∧ IsCompact (riemannianClosedBallOf gInf p r) ∧
      (∀ᶠ n in atTop, riemannianClosedBallOf gInf p r ⊆ (C n).source ∧
        riemannianClosedBallOf (hend n) (C n p) (r / 4) ⊆
          (C n) '' riemannianClosedBallOf gInf p r ∧ C n (u n) = x n) ∧
      Tendsto (fun n => riemannianEDistOf (hend n) (C n p) (x n)) atTop (𝓝 0) ∧
      ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
        ∀ a ∈ riemannianClosedBallOf gInf p r, ∀ b ∈ riemannianClosedBallOf gInf p r,
          |(riemannianEDistOf (hend n) (C n a) (C n b)).toReal -
            (riemannianEDistOf gInf a b).toReal| < eps := by
  intro C
  obtain ⟨s, hs, hsSrc, _, hKs, hdomain⟩ :=
    exists_inverse_composition_domain_of_tendsto_marks gInf gRef gSeq Hseq hend A B p
      hRsrc hRend hcompact hconv hAsource hAmetric x hu hmark hBsource hcapture
  have hsub : riemannianClosedBallOf gInf p (2 * s) ⊆
      riemannianClosedBallOf gInf p Rsrc :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hmetricC : ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf gInf p (2 * s), ∀ v : TangentSpace I y,
        (1 - eps) * gInf.inner y v v ≤ (hend n).inner (C n y)
          (mfderiv I J (C n) y v) (mfderiv I J (C n) y v) ∧
        (hend n).inner (C n y) (mfderiv I J (C n) y v) (mfderiv I J (C n) y v) ≤
          (1 + eps) * gInf.inner y v v := by
    intro eps heps
    let eta := min (eps / 8) (1 / 8)
    have heta : 0 < eta := lt_min (by positivity) (by norm_num)
    have hetaE : eta ≤ eps / 8 := min_le_left _ _
    have heta8 : eta ≤ 1 / 8 := min_le_right _ _
    have hlow : 1 - eps ≤ (1 - eta) / (1 + eta) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + eta)).mpr
      nlinarith only [hetaE, heta, heps, mul_pos heps heta]
    have hhigh : (1 + eta) / (1 - eta) ≤ 1 + eps := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - eta)).mpr
      nlinarith only [hetaE, mul_le_mul_of_nonneg_left heta8 heps.le]
    filter_upwards [hdomain, hBconv eta heta, hAmetric,
      hconv.eventually_quadratic_bounds hcompact heta] with n hn hBn hAn hGn
    intro y hy v
    have hA : ∀ w : TangentSpace I y,
        (1 - eta) * gInf.inner y w w ≤ (Hseq n).inner (A n y)
          (mfderiv I K (A n) y w) (mfderiv I K (A n) y w) ∧
        (Hseq n).inner (A n y) (mfderiv I K (A n) y w) (mfderiv I K (A n) y w) ≤
          (1 + eta) * gInf.inner y w w := by
      intro w
      rw [← hAn y (hsub hy) w]
      exact hGn y (hsub hy) w
    have hb := inverse_composition_inner_bounds gInf (hend n) (Hseq n)
      (A n) (B n) (hn.1 hy) heta.le (by linarith) hA (hBn _ (hn.2.1 y hy)) v
    have hg := metric_inner_self_nonneg gInf y v
    exact ⟨(mul_le_mul_of_nonneg_right hlow hg).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right hhigh hg)⟩
  obtain ⟨r, hr, hrs, hKr, hcaptureC, hdistC⟩ :=
    exists_distance_comparison_of_quadratic_bounds gInf p hend C hs hKs
      (hdomain.mono fun _ hn => hn.1) hmetricC
  refine ⟨r, hr, by linarith, hKr, ?_, ?_, hdistC⟩
  · filter_upwards [hcaptureC, hdomain] with n hcap hn
    exact ⟨hcap.1, hcap.2, hn.2.2.2⟩
  have hdist : Tendsto (fun n => riemannianEDistOf gInf p (u n)) atTop (𝓝 0) := by
    have hh := (Geometry.Riemannian.continuous_riemannianEDist gInf p).continuousAt.tendsto.comp hu
    change Tendsto (fun n => riemannianEDistOf gInf p (u n)) atTop
      (𝓝 (riemannianEDistOf gInf p p)) at hh
    simpa only [riemannianEDistOf_self] using hh
  have hsmall : ∀ᶠ n in atTop,
      riemannianEDistOf gInf p (u n) < ENNReal.ofReal (2 * s) :=
    hdist.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  have hbound : ∀ᶠ n in atTop, riemannianEDistOf (hend n) (C n p) (x n) ≤
      ENNReal.ofReal 2 * riemannianEDistOf gInf p (u n) := by
    filter_upwards [hdomain, hmetricC 1 zero_lt_one, hsmall] with n hn hmn hun
    rw [← hn.2.2.2]
    apply PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      gInf (hend n) (C n) p (u n) (by positivity) (by norm_num) hn.1 _ hun
    intro y hy v
    have hb := (hmn y hy v).2
    have hg := metric_inner_self_nonneg gInf y v
    nlinarith only [hb, hg]
  have hlim : Tendsto (fun n => ENNReal.ofReal 2 * riemannianEDistOf gInf p (u n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hdist
      (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

end DifferentialGeometry.CheegerGromovCompactness
