import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrier

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_spatial_neck_near_high_point_of_canonical_neighborhoods
    (L : G.TerminalLimitMetric) {eps δ q C1 C2 : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (hq : 0 < q)
    (x y : G.terminalRegularOpen)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : CanonicalWitness G.flow eps C1 C2 x.val t, W.capTubeHasNeckChart eps)
    (hx : q < metricScalarAt L.metric x)
    (hy : y.val ∈ connectedComponent x.val)
    (hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x) :
    ∃ (v : G.terminalRegularOpen) (_ : SpatialNeck L.metric δ v),
      metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric v ∧
      metricScalarAt L.metric v < 2 * C2 * metricScalarAt L.metric x ∧
      riemannianEDistOf L.metric x v <
        ENNReal.ofReal ((8 * C1 + 58 * C2) / Real.sqrt (metricScalarAt L.metric x)) := by
  have hxpos := hq.trans hx
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hC1pos : 0 < C1 := by
    have hr := (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
    exact ((div_pos_iff.mp (hr.trans_le W.radius_upper)).resolve_right
      (fun h => (Real.sqrt_pos.mpr W.Q_pos).not_gt h.2)).1
  rcases L.spatial_neck_or_cap_of_canonical_neighborhoods hδ hδsmall hepsδ hfit hq
      x y hcanonical hx hy hscalar with hneck | hcap
  · obtain ⟨nk⟩ := hneck
    refine ⟨x, nk, ?_, ?_, ?_⟩
    · apply (div_lt_iff₀ (by positivity : 0 < 2 * C2)).mpr
      nlinarith
    · nlinarith
    · rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
  · obtain ⟨v, nk, K, _, _, _, hupper, _, hband, hfront, _⟩ := hcap
    have hRv := nk.Q_pos
    have hRvband : metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric v ∧
        metricScalarAt L.metric v < 2 * C2 * metricScalarAt L.metric x := by
      simpa only [nk.center_eq] using hband (nk.center, 0) ⟨mem_univ _, by norm_num⟩
    let z := nk.map (nk.center, (1 / 2 : ℝ))
    have hzK : z ∈ K.carrier := by
      apply K.compact.isClosed.frontier_subset
      rw [hfront]
      exact ⟨nk.center, rfl⟩
    have hdist := hupper hzK
    have hlen : (1 : ℝ) < δ⁻¹ := by
      apply (lt_inv_comm₀ zero_lt_one hδ).mpr
      simpa using hδsmall.trans (by norm_num : (1 : ℝ) / 20000 < 1)
    have hzv := nk.edist_same_fiber_le nk.center
      (a := (1 / 2 : ℝ)) (b := 0) (by constructor <;> linarith)
      (by constructor <;> linarith)
    rw [nk.center_eq] at hzv
    have hsqrt : Real.sqrt (1 + δ) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> linarith
    have hrootx := Real.sqrt_pos.mpr hxpos
    have hrootv := Real.sqrt_pos.mpr hRv
    have hmul : metricScalarAt L.metric x < 2 * C2 * metricScalarAt L.metric v := by
      simpa only [mul_comm] using (div_lt_iff₀ (show 0 < 2 * C2 by positivity)).mp hRvband.1
    have hpower : 2 * C2 * metricScalarAt L.metric v ≤
        (2 * C2) ^ 2 * metricScalarAt L.metric v := by
      apply mul_le_mul_of_nonneg_right _ hRv.le
      nlinarith
    have hroots : Real.sqrt (metricScalarAt L.metric x) ≤
        2 * C2 * Real.sqrt (metricScalarAt L.metric v) := by
      calc
        _ ≤ Real.sqrt ((2 * C2) ^ 2 * metricScalarAt L.metric v) :=
          Real.sqrt_le_sqrt (hmul.le.trans hpower)
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hzv' : riemannianEDistOf L.metric z v ≤
        ENNReal.ofReal (2 * C2 / Real.sqrt (metricScalarAt L.metric x)) := by
      apply hzv.trans (ENNReal.ofReal_le_ofReal ?_)
      norm_num
      apply (div_le_div_iff₀ hrootv hrootx).mpr
      nlinarith
    refine ⟨v, nk, hRvband.1, hRvband.2, ?_⟩
    calc
      _ ≤ riemannianEDistOf L.metric x z + riemannianEDistOf L.metric z v :=
        riemannianEDistOf_triangle L.metric _ _ _
      _ < ENNReal.ofReal ((8 * C1 + 56 * C2) / Real.sqrt (metricScalarAt L.metric x)) +
          ENNReal.ofReal (2 * C2 / Real.sqrt (metricScalarAt L.metric x)) :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzv') hdist hzv'
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring


theorem exists_spatial_neck_centers_of_terminal_scalar_divergence
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x y : ∀ n, (G n).terminalRegularOpen)
    {eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (q Q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hQ : ∀ n, 0 < Q n)
    (hcanonical : ∀ n, ∀ t ∈ Ioo (a n) (s n), q n < (G n).flow.scalar t (x n).val →
      ∃ W : CanonicalWitness (G n).flow eps C1 C2 (x n).val t, W.capTubeHasNeckChart eps)
    (hx : ∀ n, q n < metricScalarAt (L n).metric (x n))
    (hy : ∀ n, (y n).val ∈ connectedComponent (x n).val)
    (hgap : ∀ n, C2 * metricScalarAt (L n).metric (y n) < metricScalarAt (L n).metric (x n))
    (hlarge : Tendsto (fun n => metricScalarAt (L n).metric (x n) / Q n) atTop atTop) :
    ∃ (v : ∀ n, (G n).terminalRegularOpen)
      (_ : ∀ n, SpatialNeck (L n).metric δ (v n)),
      (∀ n, metricScalarAt (L n).metric (x n) / (2 * C2) < metricScalarAt (L n).metric (v n) ∧
        metricScalarAt (L n).metric (v n) < 2 * C2 * metricScalarAt (L n).metric (x n)) ∧
      Tendsto (fun n => metricScalarAt (L n).metric (v n) / Q n) atTop atTop ∧
      (∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) (v n) ≠ ⊤) ∧
      Tendsto (fun n => riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric)
        (x n) (v n)) atTop (𝓝 0) := by
  classical
  choose v nk hlo hhi hd using fun n =>
    (L n).exists_spatial_neck_near_high_point_of_canonical_neighborhoods hδ hδsmall hepsδ hfit
      (hq n) (x n) (y n) (hcanonical n) (hx n) (hy n) (hgap n)
  have hRx (n) : 0 < metricScalarAt (L n).metric (x n) := (hq n).trans (hx n)
  have hC2pos : 0 < C2 := by
    have hRv := (nk 0).Q_pos
    have hprod : 0 < 2 * C2 * metricScalarAt (L 0).metric (x 0) := hRv.trans (hhi 0)
    nlinarith [hRx 0]
  have hblowup : Tendsto (fun n => metricScalarAt (L n).metric (v n) / Q n) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n => (metricScalarAt (L n).metric (x n) / Q n) / (2 * C2))
    · intro n
      have h := div_le_div_of_nonneg_right (hlo n).le (hQ n).le
      convert h using 1
      ring
    · exact (tendsto_div_const_atTop_of_pos (by positivity : 0 < 2 * C2)).mpr hlarge
  let A := 8 * C1 + 58 * C2
  have hbound (n) : riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) (v n) ≤
      ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n) / Q n)) := by
    rw [edistOf_scale]
    apply (mul_le_mul_right (hd n).le _).trans_eq
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    rw [Real.sqrt_div (hRx n).le]
    dsimp only [A]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hQ n)), ne_of_gt (Real.sqrt_pos.mpr (hRx n))]
  have hlimit : Tendsto (fun n => A / Real.sqrt (metricScalarAt (L n).metric (x n) / Q n))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hlarge)
  have hlim' : Tendsto (fun n => ENNReal.ofReal
      (A / Real.sqrt (metricScalarAt (L n).metric (x n) / Q n))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlimit
  refine ⟨v, nk, fun n => ⟨hlo n, hhi n⟩, hblowup,
    fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound n), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun n => bot_le) hbound


private theorem metric_distance_limit_of_nearby_points
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)] [∀ n, IsManifold ThreeModel ∞ (M n)]
    (g : ∀ n, SmoothRiemannianMetric ThreeModel (M n)) (p x v : ∀ n, M n)
    (hfinite : ∀ n, riemannianEDistOf (g n) (p n) (x n) ≠ ⊤)
    (hnear : ∀ n, riemannianEDistOf (g n) (x n) (v n) ≠ ⊤)
    (hzero : Tendsto (fun n => riemannianEDistOf (g n) (x n) (v n)) atTop (𝓝 0))
    {R : ℝ} (hdistance : Tendsto (fun n => (riemannianEDistOf (g n) (p n) (x n)).toReal)
      atTop (𝓝 R)) :
    (∀ n, riemannianEDistOf (g n) (p n) (v n) ≠ ⊤) ∧
    Tendsto (fun n => (riemannianEDistOf (g n) (p n) (v n)).toReal) atTop (𝓝 R) := by
  have hfinite' (n) : riemannianEDistOf (g n) (p n) (v n) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinite n, hnear n⟩)
      (riemannianEDistOf_triangle (g n) (p n) (x n) (v n))
  have hbound (n) : |(riemannianEDistOf (g n) (p n) (v n)).toReal -
      (riemannianEDistOf (g n) (p n) (x n)).toReal| ≤
      (riemannianEDistOf (g n) (x n) (v n)).toReal := by
    have h₁ := ENNReal.toReal_le_add
      (riemannianEDistOf_triangle (g n) (p n) (x n) (v n)) (hfinite n) (hnear n)
    have hrev : riemannianEDistOf (g n) (v n) (x n) ≠ ⊤ := by
      rw [riemannianEDistOf_comm]
      exact hnear n
    have h₂ := ENNReal.toReal_le_add
      (riemannianEDistOf_triangle (g n) (p n) (v n) (x n)) (hfinite' n) hrev
    rw [riemannianEDistOf_comm (g n) (v n) (x n)] at h₂
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hzero' : Tendsto (fun n => (riemannianEDistOf (g n) (x n) (v n)).toReal)
      atTop (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).tendsto.comp hzero
    change Tendsto (fun n => (riemannianEDistOf (g n) (x n) (v n)).toReal) atTop
      (𝓝 (ENNReal.toReal 0)) at ht
    exact ht
  have habs := squeeze_zero (fun n => abs_nonneg _) hbound hzero'
  have hdiff : Tendsto (fun n => (riemannianEDistOf (g n) (p n) (v n)).toReal -
      (riemannianEDistOf (g n) (p n) (x n)).toReal) atTop (𝓝 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  refine ⟨hfinite', ?_⟩
  have hh := hdiff.add hdistance
  simpa only [sub_add_cancel, zero_add] using hh


theorem exists_spatial_neck_centers_at_escape_radius
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x y : ∀ n, (G n).terminalRegularOpen)
    {eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (q Q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hQ : ∀ n, 0 < Q n)
    (hcanonical : ∀ n, ∀ t ∈ Ioo (a n) (s n), q n < (G n).flow.scalar t (x n).val →
      ∃ W : CanonicalWitness (G n).flow eps C1 C2 (x n).val t, W.capTubeHasNeckChart eps)
    (hx : ∀ n, q n < metricScalarAt (L n).metric (x n))
    (hy : ∀ n, (y n).val ∈ connectedComponent (x n).val)
    (hgap : ∀ n, C2 * metricScalarAt (L n).metric (y n) < metricScalarAt (L n).metric (x n))
    (hlarge : Tendsto (fun n => metricScalarAt (L n).metric (x n) / Q n) atTop atTop)
    (p : ∀ n, (G n).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (x n) ≠ ⊤)
    {R : ℝ} (hdistance : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (x n)).toReal) atTop (𝓝 R)) :
    ∃ (v : ∀ n, (G n).terminalRegularOpen)
      (_ : ∀ n, SpatialNeck (L n).metric δ (v n)),
      (∀ n, metricScalarAt (L n).metric (x n) / (2 * C2) < metricScalarAt (L n).metric (v n) ∧
        metricScalarAt (L n).metric (v n) < 2 * C2 * metricScalarAt (L n).metric (x n)) ∧
      Tendsto (fun n => metricScalarAt (L n).metric (v n) / Q n) atTop atTop ∧
      (∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (v n) ≠ ⊤) ∧
      Tendsto (fun n => (riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric)
        (p n) (v n)).toReal) atTop (𝓝 R) := by
  obtain ⟨v, nk, hscalar, hblowup, hnear, hzero⟩ :=
    exists_spatial_neck_centers_of_terminal_scalar_divergence P a s G L x y
      hδ hδsmall hepsδ hfit q Q hq hQ hcanonical hx hy hgap hlarge
  obtain ⟨hfinite', hlimit⟩ := metric_distance_limit_of_nearby_points
    (fun n => scaleMetric (Q n) (hQ n) (L n).metric) p x v hfinite hnear hzero hdistance
  exact ⟨v, nk, hscalar, hblowup, hfinite', hlimit⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
