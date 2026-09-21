import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance

set_option autoImplicit false
noncomputable section
universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set Manifold
open scoped Topology ContDiff Manifold ENNReal

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
