import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import DifferentialGeometry.Analysis.Calculus.Compactness.Interval
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

open Set Filter Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem inverse_curve_edist_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {γ : ℝ → N} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) J 1 γ (Icc a b))
    (hstay : ∀ t ∈ Icc a b, γ t ∈ Φ.target)
    (hunit : ∀ t ∈ Ioo a b, h.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) J γ t 1) (mfderiv 𝓘(ℝ, ℝ) J γ t 1) ≤ 1)
    (hlower : ∀ z ∈ Φ.source, ∀ v : TangentSpace I z,
      g.inner z v v ≤ C ^ 2 * h.inner (Φ z)
        (mfderiv I J (Φ : M → N) z v) (mfderiv I J (Φ : M → N) z v)) :
    riemannianEDistOf g (Φ.symm (γ a)) (Φ.symm (γ b)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (b - a) := by
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 ((Φ.symm : N → M) ∘ γ) (Icc a b) :=
    (Φ.symm.contMDiffOn_toFun.of_le (by simp)).comp hγ hstay
  apply Geometry.riemannianEDistOf_le_of_curve_speed_bound g hab hsmooth
  intro t ht
  have hzT := hstay t ⟨ht.1.le, ht.2.le⟩
  have hgd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by decide)
  have heq : (Φ : M → N) ∘ (Φ.symm : N → M) =ᶠ[𝓝 (γ t)] id := by
    filter_upwards [Φ.open_target.mem_nhds hzT] with q hq
    exact Φ.right_inv hq
  have hchain (w : TangentSpace J (γ t)) :
      mfderiv I J (Φ : M → N) (Φ.symm (γ t))
        (mfderiv J I (Φ.symm : N → M) (γ t) w) = w := by
    have hh := (mfderiv_comp (γ t)
      (Φ.mdifferentiableAt (by simp) (Φ.map_target' hzT))
      (Φ.symm.mdifferentiableAt (by simp) hzT)).symm.trans heq.mfderiv_eq
    have hw := DFunLike.congr_fun hh w
    simp only [mfderiv_id] at hw
    exact hw
  let w := mfderiv 𝓘(ℝ, ℝ) J γ t (1 : ℝ)
  have hb := hlower (Φ.symm (γ t)) (Φ.map_target' hzT)
    (mfderiv J I (Φ.symm : N → M) (γ t) w)
  rw [hchain w] at hb
  have heval : h.inner (Φ (Φ.symm (γ t))) w w = h.inner (γ t) w w :=
    congrArg (fun q : N => h.inner q (show F from w) (show F from w)) (Φ.right_inv hzT)
  rw [heval] at hb
  have hbound : g.inner (Φ.symm (γ t))
      (mfderiv J I (Φ.symm : N → M) (γ t) w)
      (mfderiv J I (Φ.symm : N → M) (γ t) w) ≤ C ^ 2 :=
    hb.trans (by
      have hh := mul_le_mul_of_nonneg_left (hunit t ht) (sq_nonneg C)
      rw [mul_one] at hh
      exact hh)
  rw [mfderiv_comp_apply t (Φ.symm.mdifferentiableAt (by simp) hzT) hgd]
  exact (Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_sq hC)


universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianConvergenceMaps.exists_curve_subseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (r n) ⊆ Φ.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        (1 - ε) * L.metric.inner x v v ≤
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (γ : ∀ n, ℝ → (X.obj (σ n)).M)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = (X.obj (σ n)).basepoint)
    (hspeed : ∀ n, ∀ t ∈ Ioo 0 (ell n),
      (X.obj (σ n)).metric.inner (γ n t)
        (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1) ≤ 1) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, L.M)), StrictMono phi ∧ LipschitzWith 1 g ∧
      g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
      ∀ A : Set (Ico 0 rho), IsCompact A →
        TendstoUniformlyOn
          (fun n (t : Ico 0 rho) => (Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t))
          g atTop A := by
  let : EMetricSpace L.M := L.emetricSpace
  let τ : ℕ → ℝ := fun n => max 0 (min (r n - 1 / ((n : ℝ) + 1)) (ell n))
  have hτ (n : ℕ) : 0 ≤ τ n := le_max_left _ _
  have hτr (n : ℕ) : τ n < r n := by
    apply max_lt (hr n)
    exact (min_le_left _ _).trans_lt (sub_lt_self _ (by positivity))
  have hτell (n : ℕ) : τ n ≤ ell n := max_le (hell n) (min_le_right _ _)
  have hτconv : Tendsto τ atTop (𝓝 rho) := by
    simpa only [sub_zero, min_self, max_eq_right hrho.le] using
      (tendsto_const_nhds (x := (0 : ℝ))).max
        ((hrconv.sub tendsto_one_div_add_atTop_nhds_zero_nat).min hellconv)
  have hbaseDist (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (ell n)) :
      riemannianEDistOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (γ n t) ≤
        ENNReal.ofReal t := by
    have hh := Geometry.riemannianEDistOf_le_of_curve_speed_bound (X.obj (σ n)).metric
      (C := 1) ht.1 ((hγ n).mono (Icc_subset_Icc le_rfl ht.2)) (by
        intro s hs
        simpa only [Real.sqrt_one] using
          Real.sqrt_le_sqrt (hspeed n s ⟨hs.1, hs.2.trans_le ht.2⟩))
    simp only [sub_zero, ENNReal.ofReal_one, one_mul, hstart n] at hh
    exact hh
  have hstay (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (τ n)) :
      γ n t ∈ (Φ.partialDiffeomorph n).target := by
    apply htarget n
    exact (hbaseDist n t ⟨ht.1, ht.2.trans (hτell n)⟩).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (hr n)).mpr (ht.2.trans_lt (hτr n)))
  have hmetric (C : ℝ≥0) (hC : 1 < C) : ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        L.metric.inner x v v ≤ (C : ℝ) ^ 2 *
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v) := by
    have hCr : 1 < (C : ℝ) := hC
    have hCsq : 0 < (C : ℝ) ^ 2 := by positivity
    let ε := ((C : ℝ) ^ 2 - 1) / (C : ℝ) ^ 2
    have hε : 0 < ε := div_pos (by nlinarith) hCsq
    filter_upwards [hlower ε hε] with n hn
    intro x hx v
    have heq : (C : ℝ) ^ 2 * (1 - ε) = 1 := by
      dsimp [ε]
      field_simp
      ring
    calc
      _ = (C : ℝ) ^ 2 * ((1 - ε) * L.metric.inner x v v) := by rw [← mul_assoc, heq, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hn x hx v) hCsq.le
  let f : ℕ → ℝ → L.M := fun n t => (Φ.partialDiffeomorph n).symm (γ n t)
  have hfzero (n : ℕ) : f n 0 = L.basepoint := by
    dsimp [f]
    rw [hstart n, ← Φ.basepoint_map n]
    exact (Φ.partialDiffeomorph n).left_inv (Φ.base_mem n)
  have hLip : ∀ C : ℝ≥0, 1 < C → ∀ᶠ n in atTop,
      LipschitzOnWith C (f n) (Icc 0 (τ n)) := by
    intro C hC
    filter_upwards [hmetric C hC] with n hn
    have hordered (s t : ℝ) (hs : s ∈ Icc 0 (τ n)) (ht : t ∈ Icc 0 (τ n)) (hst : s ≤ t) :
        edist (f n s) (f n t) ≤ (C : ℝ≥0∞) * edist s t := by
      have hb := inverse_curve_edist_le L.metric (X.obj (σ n)).metric
        (Φ.partialDiffeomorph n) hst C.coe_nonneg
        ((hγ n).mono (Icc_subset_Icc hs.1 (ht.2.trans (hτell n))))
        (fun t ht' => hstay n t ⟨hs.1.trans ht'.1, ht'.2.trans ht.2⟩)
        (fun t ht' => hspeed n t ⟨hs.1.trans_lt ht'.1, ht'.2.trans_le (ht.2.trans (hτell n))⟩)
        hn
      change riemannianEDistOf L.metric ((Φ.partialDiffeomorph n).symm (γ n s))
        ((Φ.partialDiffeomorph n).symm (γ n t)) ≤ _
      simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hb
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hordered s t hs ht hst
    · rw [edist_comm (f n s), edist_comm s]
      exact hordered t s ht hs hts
  have hpoint (t : ℝ) (ht : t ∈ Ico 0 rho) :
      ∃ Q : Set L.M, IsCompact Q ∧ ∀ᶠ n in atTop, f n t ∈ Q := by
    have ht0 : 0 ≤ t := ht.1
    have htrho : t < rho := ht.2
    let C : ℝ≥0 := ⟨(rho + 1) / (t + 1), by positivity⟩
    have hC : 1 < C := (one_lt_div (by linarith : 0 < t + 1)).mpr (by linarith)
    have heq : (C : ℝ) * (t + 1) = rho + 1 := div_mul_cancel₀ _ (by linarith)
    have hCt : (C : ℝ) * t < rho := by
      have hCr : 1 < (C : ℝ) := hC
      nlinarith
    refine ⟨riemannianClosedBallOf L.metric L.basepoint ((C : ℝ) * t),
      hcompact _ (mul_nonneg C.coe_nonneg ht.1) hCt, ?_⟩
    filter_upwards [hLip C hC, hτconv.eventually (eventually_gt_nhds ht.2)] with n hn htn
    have hb := hn ⟨le_rfl, hτ n⟩ ⟨ht.1, htn.le⟩
    rw [hfzero n] at hb
    change edist L.basepoint (f n t) ≤ ENNReal.ofReal ((C : ℝ) * t)
    simpa only [edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht.1,
      ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hb
  obtain ⟨phi, g, hphi, hgLip, hconv⟩ :=
    ArzelaAscoli.exists_lipschitz_subseq_limit_on_Ico f τ hτ hτconv hLip hpoint
  refine ⟨phi, g, hphi, hgLip, ?_, hconv⟩
  let z : Ico (0 : ℝ) rho := ⟨0, le_rfl, hrho⟩
  have hc := (hconv {z} isCompact_singleton).tendsto_at (mem_singleton z)
  have heq : (fun n => f (phi n) (z : ℝ)) = fun _ => L.basepoint := by
    funext n
    exact hfzero (phi n)
  rw [heq] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianConvergenceMaps.exists_isometric_curve_subseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (r n) ⊆ Φ.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        (1 - ε) * L.metric.inner x v v ≤
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v))
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (γ : ∀ n, ℝ → (X.obj (σ n)).M)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = (X.obj (σ n)).basepoint)
    (hspeed : ∀ n, ∀ t ∈ Ioo 0 (ell n),
      (X.obj (σ n)).metric.inner (γ n t)
        (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1) ≤ 1)
    (hmin : ∀ n, ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
      edist s t ≤ riemannianEDistOf (X.obj (σ n)).metric (γ n s) (γ n t)) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, L.M)), StrictMono phi ∧ Isometry g ∧
      g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
      ∀ A : Set (Ico 0 rho), IsCompact A →
        TendstoUniformlyOn
          (fun n (t : Ico 0 rho) => (Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t))
          g atTop A := by
  let : EMetricSpace L.M := L.emetricSpace
  obtain ⟨phi, g, hphi, hLip, hbase, hconv⟩ :=
    Φ.exists_curve_subseq_limit hrho r ell hr hell hrconv hellconv htarget hlower
      hcompact γ hγ hstart hspeed
  refine ⟨phi, g, hphi, ?_, hbase, hconv⟩
  have hbaseDist (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (ell n)) :
      riemannianEDistOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (γ n t) ≤
        ENNReal.ofReal t := by
    have hh := Geometry.riemannianEDistOf_le_of_curve_speed_bound (X.obj (σ n)).metric
      (C := 1) ht.1 ((hγ n).mono (Icc_subset_Icc le_rfl ht.2)) (by
        intro s hs
        simpa only [Real.sqrt_one] using
          Real.sqrt_le_sqrt (hspeed n s ⟨hs.1, hs.2.trans_le ht.2⟩))
    simp only [sub_zero, ENNReal.ofReal_one, one_mul, hstart n] at hh
    exact hh
  have hstay (t : Ico 0 rho) : ∀ᶠ n in atTop,
      γ n t ∈ (Φ.partialDiffeomorph n).target ∧ (t : ℝ) ∈ Icc 0 (ell n) := by
    filter_upwards [hrconv.eventually (eventually_gt_nhds t.property.2),
      hellconv.eventually (eventually_gt_nhds t.property.2)] with n hn hn'
    refine ⟨htarget n ?_, t.property.1, hn'.le⟩
    exact (hbaseDist n t ⟨t.property.1, hn'.le⟩).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (hr n)).mpr hn)
  let Ψ := Φ.compSubseq phi hphi
  have hupper' : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj ((σ ∘ phi) n)).metric.inner (Ψ.partialDiffeomorph n x)
          (mfderiv I I (Ψ.partialDiffeomorph n) x v)
          (mfderiv I I (Ψ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v := by
    intro K hK C hC
    exact hphi.tendsto_atTop (hupper K hK C hC)
  intro s t
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using hLip s t
  have hs := (hconv {s} isCompact_singleton).tendsto_at (mem_singleton s)
  have ht := (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t)
  have hlim := Ψ.limsup_edist_le hupper' hs ht
  have hevent : ∀ᶠ n in atTop, edist s t ≤
      riemannianEDistOf (X.obj ((σ ∘ phi) n)).metric
        (Ψ.partialDiffeomorph n ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) s)))
        (Ψ.partialDiffeomorph n ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t))) := by
    filter_upwards [hphi.tendsto_atTop (hstay s), hphi.tendsto_atTop (hstay t)] with n hn hn'
    change edist (s : ℝ) (t : ℝ) ≤
      riemannianEDistOf (X.obj (σ (phi n))).metric
        (Φ.partialDiffeomorph (phi n) ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) s)))
        (Φ.partialDiffeomorph (phi n) ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t)))
    have hs_inv : Φ.partialDiffeomorph (phi n)
        ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) s)) = γ (phi n) s :=
      (Φ.partialDiffeomorph (phi n)).right_inv hn.1
    have ht_inv : Φ.partialDiffeomorph (phi n)
        ((Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t)) = γ (phi n) t :=
      (Φ.partialDiffeomorph (phi n)).right_inv hn'.1
    rw [hs_inv, ht_inv]
    exact hmin (phi n) s hn.2 t hn'.2
  have hlower' := limsup_le_limsup hevent
  rw [limsup_const] at hlower'
  exact hlower'.trans hlim

theorem PointedRiemannianConvergenceMaps.exists_isometric_segment_subseq_limit
    [I.Boundaryless]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (r n) ⊆ Φ.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        (1 - ε) * L.metric.inner x v v ≤
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v))
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (γ : ∀ n, ℝ → (X.obj (σ n)).M)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = (X.obj (σ n)).basepoint)
    (hmin : ∀ n, ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
      riemannianEDistOf (X.obj (σ n)).metric (γ n s) (γ n t) = ENNReal.ofReal |s - t|) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, L.M)), StrictMono phi ∧ Isometry g ∧
      g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
      ∀ A : Set (Ico 0 rho), IsCompact A →
        TendstoUniformlyOn
          (fun n (t : Ico 0 rho) => (Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t))
          g atTop A := by
  apply Φ.exists_isometric_curve_subseq_limit hrho r ell hr hell hrconv hellconv
    htarget hlower hupper hcompact γ hγ hstart
  · intro n t ht
    exact (DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_one_of_edist_eq_on_interval
      (X.obj (σ n)).metric (hγ n) ht (hmin n)).le
  · intro n s hs t ht
    rw [hmin n s hs t ht]
    simp only [edist_dist, Real.dist_eq, le_refl]


theorem PointedRiemannianConvergenceMaps.exists_isometric_segment_subseq_limit_with_missing_endpoint
    [I.Boundaryless]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (r n) ⊆ Φ.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        (1 - ε) * L.metric.inner x v v ≤
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v))
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (hradial : ∀ x : L.M,
      riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho)
    (γ : ∀ n, ℝ → (X.obj (σ n)).M)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = (X.obj (σ n)).basepoint)
    (hmin : ∀ n, ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
      riemannianEDistOf (X.obj (σ n)).metric (γ n s) (γ n t) = ENNReal.ofReal |s - t|) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, L.M)), StrictMono phi ∧ Isometry g ∧
      g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
      (∀ A : Set (Ico 0 rho), IsCompact A →
        TendstoUniformlyOn
          (fun n (t : Ico 0 rho) => (Φ.partialDiffeomorph (phi n)).symm (γ (phi n) t))
          g atTop A) ∧
      Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact L.M) ∧
      ∀ x : L.M, ¬ Tendsto g
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x) := by
  let _ : EMetricSpace L.M := L.emetricSpace
  obtain ⟨phi, g, hphi, hg, hbase, hconv⟩ :=
    Φ.exists_isometric_segment_subseq_limit hrho r ell hr hell hrconv hellconv
      htarget hlower hupper hcompact γ hγ hstart hmin
  have hbound (x : L.M) : edist (g ⟨0, le_rfl, hrho⟩) x < ENNReal.ofReal (rho - 0) := by
    rw [hbase, sub_zero]
    exact hradial x
  exact ⟨phi, g, hphi, hg, hbase, hconv,
    hg.tendsto_cocompact_right_endpoint_of_edist_lt hrho hbound,
    fun x => hg.not_tendsto_right_endpoint_of_edist_lt hrho x (hbound x)⟩

theorem PointedRiemannianConvergenceMaps.tendsto_edist_curve_endpoint_zero
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    {a b : ℝ} (hab : a < b) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 b))
    (γ : ∀ n, ℝ → (X.obj (σ n)).M) (C : ℝ≥0)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ n) (Icc a (ell n)))
    (hspeed : ∀ n, ∀ t ∈ Ioo a (ell n),
      Real.sqrt ((X.obj (σ n)).metric.inner (γ n t)
        (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I (γ n) t 1)) ≤ C)
    (g : ℝ → L.M)
    (hconv : ∀ t ∈ Ico a b, Tendsto
      (fun n => (Φ.partialDiffeomorph n).symm (γ n t)) atTop (𝓝 (g t)))
    (hstay : ∀ t ∈ Ico a b, ∀ᶠ n in atTop, γ n t ∈ (Φ.partialDiffeomorph n).target)
    {x : L.M} (hend : Tendsto g (𝓝[<] b) (𝓝 x)) :
    Tendsto (fun n => riemannianEDistOf (X.obj (σ n)).metric
      (γ n (ell n)) (Φ.partialDiffeomorph n x)) atTop (𝓝 0) := by
  let : EMetricSpace L.M := L.emetricSpace
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨R, _, hR0, hRε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  have hhalf : 0 < ENNReal.ofReal (R / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hgdist : Tendsto (fun t => edist (g t) x) (𝓝[<] b) (𝓝 0) := by
    simpa only [edist_self] using hend.edist (tendsto_const_nhds (x := x))
  have hlength : Tendsto (fun t : ℝ => ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (b - t))
      (𝓝[<] b) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => b - t) (𝓝[<] b) (𝓝 0) := by
      have hi : Tendsto (id : ℝ → ℝ) (𝓝[<] b) (𝓝 b) := tendsto_id.mono_left inf_le_left
      simpa only [id_eq, sub_self] using (tendsto_const_nhds (x := b)).sub hi
    have hh := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (C : ℝ))
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht)
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [ENNReal.ofReal_zero, mul_zero] at hh
    exact hh
  have hchoose : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b ∧
      edist (g t) x < ENNReal.ofReal (R / 2) ∧
      ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (b - t) < ENNReal.ofReal (R / 2) := by
    filter_upwards [(eventually_gt_nhds hab).filter_mono inf_le_left, self_mem_nhdsWithin,
      hgdist.eventually (eventually_lt_nhds hhalf),
      hlength.eventually (eventually_lt_nhds hhalf)] with t hta htb hd hl
    exact ⟨⟨hta, htb⟩, hd, hl⟩
  obtain ⟨t, ht, hdist, hlen⟩ := hchoose.exists
  have hlim := Φ.limsup_edist_le hupper (hconv t ⟨ht.1.le, ht.2⟩)
    (tendsto_const_nhds (x := x))
  have hmap : ∀ᶠ n in atTop, riemannianEDistOf (X.obj (σ n)).metric
      (γ n t) (Φ.partialDiffeomorph n x) < ENNReal.ofReal (R / 2) := by
    filter_upwards [eventually_lt_of_limsup_lt (hlim.trans_lt hdist),
      hstay t ⟨ht.1.le, ht.2⟩] with n hn hs
    have heq : Φ.partialDiffeomorph n ((Φ.partialDiffeomorph n).symm (γ n t)) = γ n t :=
      (Φ.partialDiffeomorph n).right_inv hs
    rwa [heq] at hn
  have hremain : Tendsto (fun n => ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (ell n - t))
      atTop (𝓝 (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (b - t))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hell.sub_const t))
      (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hmap, hell.eventually (eventually_gt_nhds ht.2),
    hremain.eventually (eventually_lt_nhds hlen)] with n hn htn hrem
  have hspeedDist := Geometry.riemannianEDistOf_le_of_curve_speed_bound (X.obj (σ n)).metric
    htn.le ((hγ n).mono (Icc_subset_Icc ht.1.le le_rfl))
    (fun s hs => hspeed n s ⟨ht.1.trans hs.1, hs.2⟩)
  have hshort : riemannianEDistOf (X.obj (σ n)).metric (γ n (ell n)) (γ n t) <
      ENNReal.ofReal (R / 2) := by
    rw [riemannianEDistOf_comm]
    exact hspeedDist.trans_lt hrem
  calc
    _ ≤ riemannianEDistOf (X.obj (σ n)).metric (γ n (ell n)) (γ n t) +
        riemannianEDistOf (X.obj (σ n)).metric (γ n t) (Φ.partialDiffeomorph n x) :=
      riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 2) := add_le_add hshort.le hn.le
    _ = ENNReal.ofReal R := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    _ ≤ ε := hRε.le

section

variable [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}

theorem PointedRiemannianConvergenceMaps.exists_isometric_segment_subseq_limit_with_missing_endpoint_of_complete
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (hcomplete : ∀ n, RiemannianMetricComplete (X.obj (σ n)).metric)
    (hconn : ∀ n, PreconnectedSpace (X.obj (σ n)).M)
    {rho : ℝ} (hrho : 0 < rho) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (y : ∀ n, (X.obj (σ n)).M)
    (hellconv : Tendsto (fun n => (riemannianEDistOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (y n)).toReal) atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (X.obj (σ n)).metric
      (X.obj (σ n)).basepoint (r n) ⊆ Φ.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Φ.source n, ∀ v : TangentSpace I x,
        (1 - ε) * L.metric.inner x v v ≤
          (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
            (mfderiv I I (Φ.partialDiffeomorph n) x v)
            (mfderiv I I (Φ.partialDiffeomorph n) x v))
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n x)
          (mfderiv I I (Φ.partialDiffeomorph n) x v)
          (mfderiv I I (Φ.partialDiffeomorph n) x v) ≤ C ^ 2 * L.metric.inner x v v)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (hradial : ∀ x : L.M,
      riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∃ gamma : ∀ n, ℝ → (X.obj (σ n)).M,
      (∀ n,
        let ell := (riemannianEDistOf (X.obj (σ n)).metric
          (X.obj (σ n)).basepoint (y n)).toReal
        gamma n 0 = (X.obj (σ n)).basepoint ∧ gamma n ell = y n ∧
          ContMDiff 𝓘(ℝ, ℝ) I ∞ (gamma n) ∧
          ∀ s ∈ Icc 0 ell, ∀ t ∈ Icc 0 ell,
            riemannianEDistOf (X.obj (σ n)).metric (gamma n s) (gamma n t) =
              ENNReal.ofReal |s - t|) ∧
      ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, L.M)), StrictMono phi ∧ Isometry g ∧
        g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
        (∀ A : Set (Ico 0 rho), IsCompact A →
          TendstoUniformlyOn
            (fun n (t : Ico 0 rho) =>
              (Φ.partialDiffeomorph (phi n)).symm (gamma (phi n) t)) g atTop A) ∧
        Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact L.M) ∧
        ∀ x : L.M, ¬ Tendsto g
          (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x) := by
  classical
  have hsegments (n : ℕ) := by
    let _ : PreconnectedSpace (X.obj (σ n)).M := hconn n
    exact DifferentialGeometry.Geometry.exists_distance_parametrized_minimizer_of_complete
      (X.obj (σ n)).metric (hcomplete n) (X.obj (σ n)).basepoint (y n)
  choose gamma hzero hend hsmooth hmin using hsegments
  let ell := fun n => (riemannianEDistOf (X.obj (σ n)).metric
    (X.obj (σ n)).basepoint (y n)).toReal
  let _ : EMetricSpace L.M := L.emetricSpace
  obtain ⟨phi, g, hphi, hg, hbase, hconv, hescape, hmissing⟩ :=
    Φ.exists_isometric_segment_subseq_limit_with_missing_endpoint hrho r ell hr
      (fun _ => ENNReal.toReal_nonneg) hrconv hellconv htarget hlower hupper hcompact hradial
      gamma (fun n => (hsmooth n).contMDiffOn.of_le (by simp)) hzero hmin
  exact ⟨gamma, fun n => ⟨hzero n, hend n, hsmooth n, hmin n⟩,
    phi, g, hphi, hg, hbase, hconv, hescape, hmissing⟩

end

end DifferentialGeometry.CheegerGromovCompactness
