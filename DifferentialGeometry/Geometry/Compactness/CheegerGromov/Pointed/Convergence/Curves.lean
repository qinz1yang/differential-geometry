import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Metric.Path.Speed
import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
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
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 ((Φ.symm : N → M) ∘ γ) (Icc a b) :=
    (Φ.symm.contMDiffOn_toFun.of_le (by simp)).comp hγ hstay
  apply Manifold.riemannianEDist_le_of_curve_speed_bound hab hsmooth
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
  rw [mfderiv_comp_apply t (Φ.symm.mdifferentiableAt (by simp) hzT) hgd,
    ← ofReal_norm, norm_eq_sqrt_real_inner]
  change ENNReal.ofReal (Real.sqrt (g.inner (Φ.symm (γ t))
    (mfderiv J I (Φ.symm : N → M) (γ t) w)
    (mfderiv J I (Φ.symm : N → M) (γ t) w))) ≤ ENNReal.ofReal C
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_sq hC))


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
    let : RiemannianBundle (TangentSpace I : (X.obj (σ n)).M → Type _) :=
      ⟨(X.obj (σ n)).metric.toRiemannianMetric⟩
    have hh := Manifold.riemannianEDist_le_of_curve_speed_bound (C := 1) ht.1
      ((hγ n).mono (Icc_subset_Icc le_rfl ht.2)) (by
        intro s hs
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        change ENNReal.ofReal (Real.sqrt ((X.obj (σ n)).metric.inner (γ n s)
          (mfderiv 𝓘(ℝ, ℝ) I (γ n) s 1) (mfderiv 𝓘(ℝ, ℝ) I (γ n) s 1))) ≤ 1
        simpa only [Real.sqrt_one, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hspeed n s ⟨hs.1, hs.2.trans_le ht.2⟩)))
    simp only [sub_zero, one_mul, hstart n] at hh
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

end DifferentialGeometry.CheegerGromovCompactness
