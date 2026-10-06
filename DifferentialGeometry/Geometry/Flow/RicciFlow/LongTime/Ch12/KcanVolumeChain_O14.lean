import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# CH12-O14, group 1a: Bishop–Gromov chain on compact balls (the K-can volume step)

The K-can kernel (`[FROZEN v2] CH12-O14`) takes the volume at the blow-up centre from the
canonical witness and propagates it through the normalized ball by a Bishop–Gromov chain.
Everything here is local: compactness of closed balls replaces completeness (the terminal
regular opens of the KL70.2 chain are incomplete).

* `ballVolume_ratio_of_isCompact_O14`: `vol B(p,r) ≥ e^{-q(n-1)R} (r/2R)^n vol B(p,R)` from
  `Ric ≥ -(n-1)q²` on `B(p,R)` and compactness of `B̄(p,R)`.
* `exists_intermediate_point_O14`: approximate intermediate points of the length structure.
* `ballVolume_step_O14`, `ballVolume_chain_O14`: one step and `k` steps of the chain.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem bishop_gromov_of_isCompact_O14
    (g : SmoothRiemannianMetric I M) (p : M) {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hrR : r ≤ R) (hcpt : IsCompact (riemannianClosedBallOf g p R))
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I) g y v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) r) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hcpt' : IsCompact (Metric.closedEBall p (ENNReal.ofReal R)) := by
    have hset : Metric.closedEBall p (ENNReal.ofReal R) =
        {x : M | riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R} := by
      ext x
      rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) p x]
      rfl
    rw [hset]
    exact hcpt
  have hrel := bishop_gromov_of_isCompact_closedEBall g hEnorm p hq hr hrR hcpt'
    (fun y v hy => hRic y hy v)
  simpa only [riemannianBallOf, riemannianEDistOf] using hrel

/-- Local Bishop–Gromov ratio on a compact ball (completeness replaced by compactness). -/
theorem ballVolume_ratio_of_isCompact_O14
    (g : SmoothRiemannianMetric I M) (p : M) {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hrR : r ≤ R) (hcpt : IsCompact (riemannianClosedBallOf g p R))
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I) g y v v) :
    ENNReal.ofReal (Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * R)) *
        (r / (2 * R)) ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p R) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  set n : ℕ := Module.finrank ℝ E with hndef
  set d : ℕ := n - 1 with hddef
  have hn : d + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hR : 0 < R := hr.trans_le hrR
  have hrel := bishop_gromov_of_isCompact_O14 g p hq hr hrR hcpt hRic
  set Vr := hyperbolicRadialVolume q d r with hVr
  have hVr_pos : 0 < Vr := (pow_pos (half_pos hr) _).trans_le (hyperbolicRadialVolume_ge d hq hr)
  have hratio := hyperbolicRadialVolume_ratio_le d hq hr hrR
  rw [hn] at hratio
  set c : ℝ := Real.exp (-(q * (d : ℝ) * R)) * (r / (2 * R)) ^ n with hc
  have hc0 : 0 ≤ c := by positivity
  have hkey : c * (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n) = 1 := by
    rw [hc, Real.exp_neg]
    have h1 : (r / (2 * R)) ^ n * (R / (r / 2)) ^ n = 1 := by
      rw [← mul_pow]
      have : r / (2 * R) * (R / (r / 2)) = 1 := by field_simp
      rw [this, one_pow]
    have h2 : (Real.exp (q * (d : ℝ) * R))⁻¹ * Real.exp (q * (d : ℝ) * R) = 1 :=
      inv_mul_cancel₀ (Real.exp_pos _).ne'
    calc (Real.exp (q * (d : ℝ) * R))⁻¹ * (r / (2 * R)) ^ n *
          (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n)
        = ((Real.exp (q * (d : ℝ) * R))⁻¹ * Real.exp (q * (d : ℝ) * R)) *
          ((r / (2 * R)) ^ n * (R / (r / 2)) ^ n) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hVR : ENNReal.ofReal (hyperbolicRadialVolume q d R) ≤
      ENNReal.ofReal (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n * Vr) :=
    ENNReal.ofReal_le_ofReal hratio
  have hV0 : ENNReal.ofReal Vr ≠ 0 := (ENNReal.ofReal_pos.mpr hVr_pos).ne'
  have hVt : ENNReal.ofReal Vr ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hV0 hVt).mp
  calc ENNReal.ofReal c * riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal Vr
      = ENNReal.ofReal c * (riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal Vr) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (hyperbolicRadialVolume q d R) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r)) := mul_le_mul' le_rfl hrel
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n * Vr) *
          riemannianVolumeMeasure I M g (riemannianBallOf g p r)) :=
        mul_le_mul' le_rfl (mul_le_mul' hVR le_rfl)
    _ = riemannianVolumeMeasure I M g (riemannianBallOf g p r) * ENNReal.ofReal Vr := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc0, ← mul_assoc, hkey, one_mul, mul_comm]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Approximate intermediate points: if `d(x,y) < D` and `0 ≤ c < D`, some `z` has
`d(x,z) ≤ c` and `d(z,y) < D - c`. -/
theorem exists_intermediate_point_O14 (g : SmoothRiemannianMetric I M) {x y : M} {c D : ℝ}
    (hc : 0 ≤ c) (hcD : c < D) (hxy : riemannianEDistOf g x y < ENNReal.ofReal D) :
    ∃ z : M, riemannianEDistOf g x z ≤ ENNReal.ofReal c ∧
      riemannianEDistOf g z y < ENNReal.ofReal (D - c) := by
  by_cases hle : riemannianEDistOf g x y ≤ ENNReal.ofReal c
  · refine ⟨y, hle, ?_⟩
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  push Not at hle
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt g hxy
  have hφ : ContinuousOn (fun s => riemannianEDistOf g x (γ s)) (Icc 0 1) :=
    (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g x).comp_continuousOn hγ.continuousOn
  have hmem : ENNReal.ofReal c ∈ Icc (riemannianEDistOf g x (γ 0))
      (riemannianEDistOf g x (γ 1)) := by
    rw [hγ0, hγ1, riemannianEDistOf_self]
    exact ⟨bot_le, hle.le⟩
  obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc zero_le_one hφ hmem
  refine ⟨γ t, hφt.le, ?_⟩
  have h1 : riemannianEDistOf g (γ 0) (γ t) ≤ metricPathELength g γ 0 t :=
    edistOf_le_metricPathELength g ht.1 (hγ.mono (Icc_subset_Icc le_rfl ht.2))
  have h2 : riemannianEDistOf g (γ t) (γ 1) ≤ metricPathELength g γ t 1 :=
    edistOf_le_metricPathELength g ht.2 (hγ.mono (Icc_subset_Icc ht.1 le_rfl))
  have hadd : metricPathELength g γ 0 t + metricPathELength g γ t 1 =
      metricPathELength g γ 0 1 := by
    let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
    exact Manifold.pathELength_add ht.1 ht.2
  rw [hγ0] at h1
  rw [hγ1] at h2
  have hφt' : riemannianEDistOf g x (γ t) = ENNReal.ofReal c := hφt
  rw [hφt'] at h1
  have hsum : ENNReal.ofReal c + riemannianEDistOf g (γ t) y < ENNReal.ofReal D :=
    lt_of_le_of_lt (add_le_add h1 h2) (hadd ▸ hlen)
  rw [ENNReal.ofReal_sub _ hc]
  exact (AddLECancellable.lt_tsub_iff_left (ENNReal.cancel_of_ne ENNReal.ofReal_ne_top)).mpr hsum

/-- The chain constant of one step (`r = h`, `R = 3h`). -/
def chainConst_O14 (n : ℕ) (q h : ℝ) : ℝ :=
  Real.exp (-(q * ((n - 1 : ℕ) : ℝ) * (3 * h))) * (1 / 6) ^ n

theorem chainConst_pos_O14 (n : ℕ) (q h : ℝ) : 0 < chainConst_O14 n q h := by
  unfold chainConst_O14; positivity

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem isClosed_riemannianClosedBallOf_O14 (g : SmoothRiemannianMetric I M) (y : M) (R : ℝ) :
    IsClosed (riemannianClosedBallOf g y R) :=
  isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g y)
    continuous_const

/-- One chain step: from `vol B(u,h)` to `vol B(y,h)` when `d(u,y) < 2h`. -/
theorem ballVolume_step_O14 (g : SmoothRiemannianMetric I M) {u y : M} {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (huy : riemannianEDistOf g u y < ENNReal.ofReal (2 * h))
    (hcpt : IsCompact (riemannianClosedBallOf g y (3 * h)))
    (hRic : ∀ z ∈ riemannianBallOf g y (3 * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z v v ≤
        ricciTensor (I := I) g z v v) :
    ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
        riemannianVolumeMeasure I M g (riemannianBallOf g u h) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g y h) := by
  have hrat := ballVolume_ratio_of_isCompact_O14 g y hq hh (by linarith) hcpt hRic
  have h6 : h / (2 * (3 * h)) = 1 / 6 := by field_simp; ring
  rw [h6] at hrat
  refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) hrat
  intro w hw
  change riemannianEDistOf g y w < ENNReal.ofReal (3 * h)
  change riemannianEDistOf g u w < ENNReal.ofReal h at hw
  calc riemannianEDistOf g y w ≤ riemannianEDistOf g y u + riemannianEDistOf g u w :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal (2 * h) + ENNReal.ofReal h :=
        ENNReal.add_lt_add (by rw [riemannianEDistOf_comm]; exact huy) hw
    _ = ENNReal.ofReal (3 * h) := by
        rw [← ENNReal.ofReal_add (by linarith) hh.le]; ring_nf

/-- **Bishop–Gromov chain.** On a compact ball `B̄(x,(N+4)h)` with `Ric ≥ -(n-1)q²`, the volume
of `B(x,h)` controls `vol B(y,h)` for every `y` with `d(x,y) < (k+1)h`, `k ≤ N`. -/
theorem ballVolume_chain_O14 (g : SmoothRiemannianMetric I M) (x : M) {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (N : ℕ)
    (hcpt : IsCompact (riemannianClosedBallOf g x ((N + 4) * h)))
    (hRic : ∀ z ∈ riemannianBallOf g x ((N + 4) * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z v v ≤
        ricciTensor (I := I) g z v v) :
    ∀ k : ℕ, k ≤ N → ∀ y : M, riemannianEDistOf g x y < ENNReal.ofReal ((k + 1) * h) →
      ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g x h) ≤
        riemannianVolumeMeasure I M g (riemannianBallOf g y h) := by
  have hc0 := (chainConst_pos_O14 (Module.finrank ℝ E) q h).le
  -- the step is available at every centre `y` with `d(x,y) < (N+1)h`
  have hstep : ∀ u y : M, riemannianEDistOf g x y < ENNReal.ofReal ((N + 1) * h) →
      riemannianEDistOf g u y < ENNReal.ofReal (2 * h) →
      ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
          riemannianVolumeMeasure I M g (riemannianBallOf g u h) ≤
        riemannianVolumeMeasure I M g (riemannianBallOf g y h) := by
    intro u y hxy huy
    have hin : ∀ z, riemannianEDistOf g y z ≤ ENNReal.ofReal (3 * h) →
        riemannianEDistOf g x z < ENNReal.ofReal ((N + 4) * h) := by
      intro z hz
      calc riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal ((N + 1) * h) + ENNReal.ofReal (3 * h) :=
            ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz) hxy hz
        _ = ENNReal.ofReal ((N + 4) * h) := by
            rw [← ENNReal.ofReal_add (by positivity) (by linarith)]; ring_nf
    refine ballVolume_step_O14 g hq hh huy ?_ ?_
    · refine hcpt.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 g y _) ?_
      intro z hz
      exact (hin z hz).le
    · intro z hz v
      exact hRic z (hin z (le_of_lt hz)) v
  intro k
  induction k with
  | zero =>
    intro _ y hy
    have hy' : riemannianEDistOf g x y < ENNReal.ofReal ((N + 1) * h) :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        push_cast; nlinarith))
    have hxy2 : riemannianEDistOf g x y < ENNReal.ofReal (2 * h) :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by push_cast; linarith))
    simpa using hstep x y hy' hxy2
  | succ k ih =>
    intro hk y hy
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨z, hxz, hzy⟩ := exists_intermediate_point_O14 g (c := (k + 1 / 2) * h)
      (D := ((k + 1 : ℕ) + 1) * h) (by positivity) (by push_cast; nlinarith) hy
    have hxz' : riemannianEDistOf g x z < ENNReal.ofReal ((k + 1) * h) :=
      lt_of_le_of_lt hxz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith))
    have hzy' : riemannianEDistOf g z y < ENNReal.ofReal (2 * h) :=
      lt_of_lt_of_le hzy (ENNReal.ofReal_le_ofReal (by push_cast; nlinarith))
    have hNR : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
    have hy' : riemannianEDistOf g x y < ENNReal.ofReal ((N + 1) * h) :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by nlinarith))
    have h1 := ih hkN z hxz'
    have h2 := hstep z y hy' hzy'
    calc ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1 + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g x h)
        = ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
          (ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1)) *
            riemannianVolumeMeasure I M g (riemannianBallOf g x h)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc0, pow_succ' _ (k + 1)]
      _ ≤ ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
          riemannianVolumeMeasure I M g (riemannianBallOf g z h) := mul_le_mul' le_rfl h1
      _ ≤ _ := h2

end GC.LongTime.Ch12
