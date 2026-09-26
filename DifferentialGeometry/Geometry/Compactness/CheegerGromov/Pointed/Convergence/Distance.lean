import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.CompactMapDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}
  {F : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_riemannianEDistOf_map_lt_of_metric_convergence
    (C : MetricConvergenceData F)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (x y : L.M) {r : ℝ} (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal r) :
    ∀ᶠ k in atTop, riemannianEDistOf (X.obj (subseq k)).metric (F.map k x) (F.map k y) <
      ENNReal.ofReal r := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : RiemannianBundle (fun x : L.M => TangentSpace I x) := L.riemBundle
  let : IsContinuousRiemannianBundle E (fun x : L.M => TangentSpace I x) := L.riemBundle_cont
  let : ∀ k, RiemannianBundle (fun x : (X.obj (subseq k)).M => TangentSpace I x) :=
    fun k => (X.obj (subseq k)).riemBundle
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj (subseq k)).M => TangentSpace I x) :=
    fun k => (X.obj (subseq k)).riemBundle_cont
  have hnorm := Geometry.Riemannian.isMetricNorm_of_riemannianBundle L.metric
  have hnorms (k : ℕ) := Geometry.Riemannian.isMetricNorm_of_riemannianBundle (X.obj (subseq k)).metric
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 1 < B →
      ∀ᶠ k in atTop, (∀ z ∈ K, ContMDiffAt I I 1 (F.map k) z) ∧
        ∀ z ∈ K, ∀ v : TangentSpace I z,
          ‖mfderiv I I (F.map k) z v‖ₑ ≤ ENNReal.ofReal B * ‖v‖ₑ := by
    intro K hK B hB
    obtain ⟨N, hN⟩ := PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      C href K hK (B ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with k hk
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ((F.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
        ((F.partialDiffeomorph k).open_source.mem_nhds ((hN k hk).1 hz))).of_le (by simp)
    · intro z hz v
      have h := (abs_le.mp ((hN k hk).2 z hz v)).2
      have hb : 0 ≤ B := by linarith
      have hnv := hnorms k (F.map k z) (mfderiv I I (F.map k) z v)
      have hn := hnorm z v
      erw [hnv, hn, ← ENNReal.ofReal_mul hb]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Real.sqrt (B ^ 2 * L.metric.inner z v v) :=
          Real.sqrt_le_sqrt (by nlinarith)
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hb]
  have hxy' : Manifold.riemannianEDist I x y < ENNReal.ofReal r := by
    exact (riemannianEDistOf_eq_riemannianEDist L.metric hnorm x y).symm.trans_lt hxy
  have h := Geometry.Riemannian.eventually_riemannianEDist_map_lt F.map hupper x y hxy'
  filter_upwards [h] with k hk
  rwa [riemannianEDistOf_eq_riemannianEDist (X.obj (subseq k)).metric (hnorms k)]

omit [NeZero (Module.finrank ℝ E)] in
theorem PointedRiemannianConvergenceMaps.exists_precompact_neighborhood_with_image_in_ball
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hreference : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    {r : ℝ} (hr : 0 < r) :
    ∃ V : TopologicalSpace.Opens P.M, P.basepoint ∈ V ∧ PathConnectedSpace V ∧
      IsCompact (closure (V : Set P.M)) ∧ ∀ᶠ n in atTop,
        closure (V : Set P.M) ⊆ F.source n ∧
        ∀ x ∈ (V : Set P.M), riemannianEDistOf (X.obj (f n)).metric
          (X.obj (f n)).basepoint (F.map n x) < ENNReal.ofReal r := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨R, hR, hcompact, _⟩ :=
    Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds
      P.metric P.basepoint (Filter.univ_mem : (univ : Set P.M) ∈ 𝓝 P.basepoint)
  let d := min R (r / 4)
  have hd : 0 < d := lt_min hR (by positivity)
  have hdR : d ≤ R := min_le_left _ _
  have hdr : d ≤ r / 4 := min_le_right _ _
  have hdcompact : IsCompact (riemannianClosedBallOf P.metric P.basepoint d) :=
    hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ hdR)
  let V : TopologicalSpace.Opens P.M := ⟨riemannianBallOf P.metric P.basepoint d,
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint) continuous_const⟩
  have hclosure : closure (V : Set P.M) ⊆ riemannianClosedBallOf P.metric P.basepoint d := by
    apply closure_minimal
    · intro x hx
      exact le_of_lt (show riemannianEDistOf P.metric P.basepoint x < ENNReal.ofReal d from hx)
    · exact Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _
  refine ⟨V, ?_, ?_, hdcompact.of_isClosed_subset isClosed_closure hclosure, ?_⟩
  · change riemannianEDistOf P.metric P.basepoint P.basepoint < ENNReal.ofReal d
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hd
  · exact isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_riemannianBallOf P.metric P.basepoint hd)
  · have hquadratic : ∀ᶠ n in atTop,
        riemannianClosedBallOf P.metric P.basepoint d ⊆ F.source n ∧
        ∀ z ∈ riemannianClosedBallOf P.metric P.basepoint d, ∀ v : TangentSpace I z,
          (X.obj (f n)).metric.inner (F.map n z) (mfderiv I I (F.map n) z v)
            (mfderiv I I (F.map n) z v) ≤ (2 : ℝ) ^ 2 * P.metric.inner z v v := by
      by_cases hdim : Module.finrank ℝ E = 0
      · obtain ⟨N, hN⟩ := F.source_subset hdcompact
        filter_upwards [eventually_ge_atTop N] with n hn
        refine ⟨hN n hn, ?_⟩
        intro z _ v
        let _ : Subsingleton (TangentSpace I z) := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hdim
        have hv : v = 0 := Subsingleton.elim _ _
        simp only [hv, map_zero, mul_zero, le_refl]
      · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
        obtain ⟨N, hN⟩ :=
          PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
            C hreference _ hdcompact 3 (by norm_num)
        filter_upwards [eventually_ge_atTop N] with n hn
        refine ⟨(hN n hn).1, ?_⟩
        intro z hz v
        have hh := (abs_le.mp ((hN n hn).2 z hz v)).2
        nlinarith only [hh]
    filter_upwards [hquadratic] with n hn
    refine ⟨hclosure.trans hn.1, ?_⟩
    intro x hx
    have hh := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      P.metric (X.obj (f n)).metric (F.partialDiffeomorph n) P.basepoint x hd
      (by norm_num : (0 : ℝ) < 2) hn.1 hn.2 hx
    rw [F.basepoint_map] at hh
    have hb : ENNReal.ofReal (2 : ℝ) * riemannianEDistOf P.metric P.basepoint x <
        ENNReal.ofReal (2 * d) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hx
    exact (hh.trans_lt hb).trans ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

open Filter Set Manifold
open scoped _root_.Topology ContDiff Manifold ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
  (Φ : PointedRiemannianConvergenceMaps X L σ)

omit [FiniteDimensional ℝ E] in
private theorem eventually_edist_map_lt
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    (x y : L.M) {R : ℝ} (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal R) :
    ∀ᶠ n in atTop, riemannianEDistOf (X.obj (σ n)).metric
      (Φ.partialDiffeomorph n x) (Φ.partialDiffeomorph n y) < ENNReal.ofReal R := by
  have hR : 0 < R := ENNReal.ofReal_pos.mp (bot_le.trans_lt hxy)
  obtain ⟨S, hS0, hSxy, hSR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hxy
  have hS : 0 < S := ENNReal.ofReal_pos.mp (bot_le.trans_lt hSxy)
  have hSRreal : S < R := (ENNReal.ofReal_lt_ofReal_iff hR).mp hSR
  let C := (S + R) / (2 * S)
  have hC : 1 < C := (one_lt_div (by positivity : 0 < 2 * S)).mpr (by linarith)
  have hCS : C * S < R := by
    have h := div_mul_cancel₀ (S + R) (by positivity : 2 * S ≠ 0)
    change C * (2 * S) = S + R at h
    nlinarith
  obtain ⟨γ, hzero, hone, hγ, hlength⟩ := exists_lt_of_edistOf_lt L.metric hSxy
  have hK : IsCompact (γ '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨N, hN⟩ := Φ.source_subset hK
  filter_upwards [eventually_ge_atTop N, hupper _ hK C hC] with n hn hbound
  have hsource (t : ℝ) (ht : t ∈ Icc 0 1) : γ t ∈ (Φ.partialDiffeomorph n).source :=
    hN n hn ⟨t, ht, rfl⟩
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ) I 1 ((Φ.partialDiffeomorph n : L.M → _) ∘ γ) (Icc 0 1) :=
    ((Φ.partialDiffeomorph n).contMDiffOn_toFun.of_le (by simp)).comp hγ hsource
  have hd := edistOf_le_metricPathELength (X.obj (σ n)).metric (by norm_num : (0 : ℝ) ≤ 1) hmap
  simp only [Function.comp_apply, hzero, hone] at hd
  have hl := PDE.RicciFlow.Perelman.KappaSolutions.metricPathELength_comp_le
    L.metric (X.obj (σ n)).metric (Φ.partialDiffeomorph n) (by linarith : 0 ≤ C)
    hγ hsource (fun t ht => hbound (γ t) ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
  calc
    _ ≤ ENNReal.ofReal C * metricPathELength L.metric γ 0 1 := hd.trans hl
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal S := mul_le_mul' le_rfl hlength.le
    _ < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ C)]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hCS

theorem PointedRiemannianConvergenceMaps.tendsto_edist_map_zero
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    {x : L.M} {z : ℕ → L.M} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => riemannianEDistOf (X.obj (σ n)).metric
      (Φ.partialDiffeomorph n x) (Φ.partialDiffeomorph n (z n))) atTop (𝓝 0) := by
  let : EMetricSpace L.M := L.emetricSpace
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds x
  obtain ⟨ε, hε, hεK⟩ := Metric.nhds_basis_closedEBall.mem_iff.mp hKnhds
  obtain ⟨R, _, hR0, hRε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  have hRK : riemannianClosedBallOf L.metric x R ⊆ K := by
    intro y hy
    apply hεK
    change edist y x ≤ ε
    rw [edist_comm]
    exact hy.trans hRε.le
  obtain ⟨N, hN⟩ := Φ.source_subset hK
  have hevent : ∀ᶠ n in atTop, riemannianEDistOf (X.obj (σ n)).metric
      (Φ.partialDiffeomorph n x) (Φ.partialDiffeomorph n (z n)) ≤
        ENNReal.ofReal 2 * edist x (z n) := by
    filter_upwards [eventually_ge_atTop N, hupper K hK 2 (by norm_num),
      hz (Metric.eball_mem_nhds x (ENNReal.ofReal_pos.mpr hR))] with n hn hb hzball
    apply PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      L.metric (X.obj (σ n)).metric (Φ.partialDiffeomorph n) x (z n) hR (by norm_num)
      (hRK.trans (hN n hn)) (fun y hy => hb y (hRK hy))
    change edist (z n) x < ENNReal.ofReal R at hzball
    rwa [edist_comm] at hzball
  have hzdist : Tendsto (fun n => edist x (z n)) atTop (𝓝 0) := by
    simpa only [edist_self] using (tendsto_const_nhds (x := x)).edist hz
  have hbound : Tendsto (fun n => ENNReal.ofReal 2 * edist x (z n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hzdist (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) hevent

theorem PointedRiemannianConvergenceMaps.limsup_edist_le
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    {x y : L.M} {z w : ℕ → L.M}
    (hz : Tendsto z atTop (𝓝 x)) (hw : Tendsto w atTop (𝓝 y)) :
    limsup (fun n => riemannianEDistOf (X.obj (σ n)).metric
      (Φ.partialDiffeomorph n (z n)) (Φ.partialDiffeomorph n (w n))) atTop ≤
        riemannianEDistOf L.metric x y := by
  have hfixed : limsup (fun n => riemannianEDistOf (X.obj (σ n)).metric
      (Φ.partialDiffeomorph n x) (Φ.partialDiffeomorph n y)) atTop ≤
        riemannianEDistOf L.metric x y := by
    apply (limsup_le_iff).mpr
    intro b hb
    obtain ⟨R, _, hRxy, hRb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    exact (eventually_edist_map_lt Φ hupper x y hRxy).mono fun _ hn => hn.trans hRb
  let a : ℕ → ℝ≥0∞ := fun n => riemannianEDistOf (X.obj (σ n)).metric
    (Φ.partialDiffeomorph n (z n)) (Φ.partialDiffeomorph n x)
  let b : ℕ → ℝ≥0∞ := fun n => riemannianEDistOf (X.obj (σ n)).metric
    (Φ.partialDiffeomorph n x) (Φ.partialDiffeomorph n y)
  let c : ℕ → ℝ≥0∞ := fun n => riemannianEDistOf (X.obj (σ n)).metric
    (Φ.partialDiffeomorph n y) (Φ.partialDiffeomorph n (w n))
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, riemannianEDistOf_comm] using Φ.tendsto_edist_map_zero hupper hz
  have hc : Tendsto c atTop (𝓝 0) := Φ.tendsto_edist_map_zero hupper hw
  calc
    _ ≤ limsup (a + b + c) atTop := limsup_le_limsup (Eventually.of_forall fun n => by
      exact (riemannianEDistOf_triangle _ _ _ _).trans
        (add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl))
    _ = limsup b atTop := by
      rw [ENNReal.limsup_add_of_right_tendsto_zero hc,
        ENNReal.limsup_add_of_left_tendsto_zero ha]
    _ ≤ _ := hfixed

end DifferentialGeometry.CheegerGromovCompactness
