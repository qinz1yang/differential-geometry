import DifferentialGeometry.Geometry.Comparison.Busemann.Support.HessianEnergyDecay
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.HessianNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set MeasureTheory
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem nonpos_of_monotone_of_energy_decay
    (B N : ℝ → ℝ → ℝ) (G : ℝ → ℝ) (s R : ℝ) (hsR : s < R)
    (hB : ContinuousAt (B R) s) (hG : ContinuousAt G s)
    (hmono : ∀ t S, t < R → R ≤ S → B R t ≤ B S t)
    (hbound : ∀ t S, t < S → 0 ≤ N S t ∧ |B S t| ≤ Real.sqrt (N S t) * G t)
    (hN : ∀ S, ContinuousOn (N S) (Iio S))
    (henergy : ∀ a b, a ≤ b → Tendsto (fun S => ∫ t in a..b, N S t) atTop (𝓝 0)) :
    B R s ≤ 0 := by
  by_contra! hpos
  let c := B R s / 2
  let C := |G s| + 1
  have hc : 0 < c := half_pos hpos
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnear : ∀ᶠ t in 𝓝 s, c < B R t ∧ G t < C ∧ t < R := by
    have hp := hB.eventually (eventually_gt_nhds (half_lt_self hpos))
    have hg := hG.eventually (eventually_lt_nhds
      ((le_abs_self (G s)).trans_lt (lt_add_one _)))
    filter_upwards [hp, hg, eventually_lt_nhds hsR] with t ht htG htR
    exact ⟨ht, htG, htR⟩
  obtain ⟨l, r, hs, hsub⟩ := hnear.exists_Ioo_subset
  let a := (l + s) / 2
  let b := (s + r) / 2
  have hab : a < b := by dsimp only [a, b]; linarith [hs.1, hs.2]
  have hsmall (t : ℝ) (ht : t ∈ Icc a b) : c < B R t ∧ G t < C ∧ t < R := by
    apply hsub
    dsimp only [a, b] at ht
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hbR : b < R := (hsmall b (right_mem_Icc.mpr hab.le)).2.2
  have hlower : ∀ᶠ S in atTop, (b - a) * c ^ 2 ≤ C ^ 2 * ∫ t in a..b, N S t := by
    filter_upwards [eventually_ge_atTop R] with S hS
    have hNS : ContinuousOn (N S) (Icc a b) :=
      (hN S).mono (fun _ ht => ht.2.trans_lt (hbR.trans_le hS))
    have hpoint (t : ℝ) (ht : t ∈ Icc a b) : c ^ 2 ≤ C ^ 2 * N S t := by
      obtain ⟨htc, htG, htR⟩ := hsmall t ht
      obtain ⟨hn, hnB⟩ := hbound t S (htR.trans_le hS)
      have hle : c ≤ Real.sqrt (N S t) * C :=
        (((htc.le.trans (hmono t S htR hS)).trans (le_abs_self _)).trans hnB).trans
          (mul_le_mul_of_nonneg_left htG.le (Real.sqrt_nonneg _))
      calc c ^ 2 ≤ (Real.sqrt (N S t) * C) ^ 2 :=
            (sq_le_sq₀ hc.le (mul_nonneg (Real.sqrt_nonneg _) hC.le)).2 hle
        _ = C ^ 2 * N S t := by rw [mul_pow, Real.sq_sqrt hn]; ring
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le intervalIntegrable_const
      ((hNS.intervalIntegrable_of_Icc hab.le).const_mul (C ^ 2)) hpoint
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul] using hi
  have hlim : Tendsto (fun S => C ^ 2 * ∫ t in a..b, N S t) atTop (𝓝 0) := by
    simpa only [mul_zero] using (henergy a b hab.le).const_mul (C ^ 2)
  have hle : (b - a) * c ^ 2 ≤ 0 := ge_of_tendsto hlim hlower
  exact not_le_of_gt (mul_pos (sub_pos.mpr hab) (sq_pos_of_pos hc)) hle

private theorem bilin_eq_zero_of_nonpos_of_trace_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hn : ∀ v, B v v ≤ 0)
    (ht : ∑ i, B (b i) (b i) = 0) : B = 0 := by
  classical
  have hd (i : ι) : B (b i) (b i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hn (b i))).mp ht i (Finset.mem_univ i)
  have hc (i j : ι) : B (b i) (b j) = 0 := by
    have hp := hn (b i + b j)
    have hm := hn (b i - b j)
    simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hp hm
    rw [hd i, hd j, hs (b j) (b i)] at hp hm
    linarith
  apply b.ext
  intro i
  apply b.ext
  intro j
  simpa only [LinearMap.zero_apply] using hc i j

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem levi_hessian_apply (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v w : TangentSpace I x) :
    leviHessSec (I := I) g f hf x (vec2 (I := I) v w) = hessFun (I := I) g f x v w := by
  rw [hessFun_eq_cov_grad (I := I) g hf x v w]
  exact hessSec_inner_cov (I := I) (leviCivitaConnectionOfMetric (I := I) g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
    g (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) f hf x v w

omit [NeZero (Module.finrank ℝ E)] in
private theorem hessian_diagonal_continuous_at_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M} (hx : x ∈ U) :
    ContinuousAt (fun y => hessFun (I := I) g f y (X y) (X y)) x := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  have hc := (tensor0SField_eval_smooth_slots_contMDiffAt (I := I)
    (leviHessSec (I := I) g F hF) (fun _ : Fin 2 => X) x).continuousAt
  apply hc.congr
  filter_upwards [hFf.eventuallyEq_nhds] with y hy
  have hvec : (fun _ : Fin 2 => X y) = vec2 (I := I) (X y) (X y) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, levi_hessian_apply g hF, hessFun_congr (I := I) g hy]

omit [NeZero (Module.finrank ℝ E)] in
private theorem hessian_diagonal_bound_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {x : M} (hx : x ∈ U) (v : TangentSpace I x) :
    |hessFun (I := I) g f x v v| ≤
      Real.sqrt (chartHessFrobeniusSq (I := I) g f x) * g.inner x v v := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  have hb := abs_apply_le_norm0S (I := I) g x 2 (leviHessSec (I := I) g F hF x)
    (vec2 (I := I) v v)
  rw [levi_hessian_apply g hF, hessSec_normSq (I := I) g hF x,
    hessFun_congr (I := I) g hFf] at hb
  have hnorm : chartHessFrobeniusSq (I := I) g F x = chartHessFrobeniusSq (I := I) g f x := by
    have heq := hessFun_congr (I := I) g hFf
    have hcomp (i j : Fin (Module.finrank ℝ E)) :
        chartHessianTensor (I := I) g x F i j x = chartHessianTensor (I := I) g x f i j x := by
      rw [← hessFun_basis_apply (I := I) g F x i j,
        ← hessFun_basis_apply (I := I) g f x i j, heq]
    simp only [chartHessFrobeniusSq_def, hcomp]
  rw [hnorm] at hb
  have hv : 0 ≤ g.inner x v v := by
    by_cases hzero : v = 0
    · simp [hzero]
    · exact (g.pos x v hzero).le
  simpa only [Fin.prod_univ_two, vec2, Fin.isValue, ite_true, zero_ne_one,
    one_ne_zero, ite_false, ← sq, Real.sq_sqrt hv] using hb

end Local

section Line

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem lineDistanceSupport_hessian_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s R : ℝ) (hsR : s < R)
    (v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    hessFun (I := I) g (lineDistanceSupport eta R) (eta s) v v ≤ 0 := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (eta s) v
  let B := fun S t => hessFun (I := I) g (lineDistanceSupport eta S) (eta t) (X (eta t)) (X (eta t))
  let N := fun S t => chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta S) (eta t)
  let G := fun t => g.inner (eta t) (X (eta t)) (X (eta t))
  have hdiag : B R s ≤ 0 := by
    apply nonpos_of_monotone_of_energy_decay B N G s R hsR
    · obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
        g hEnorm p u hu hiso s R hsR
      exact (hessian_diagonal_continuous_at_on g hU hf X hx).comp hiso.continuous.continuousAt
    · exact (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g X X).continuousAt.comp
        hiso.continuous.continuousAt
    · intro t S ht hS
      exact lineDistanceSupport_hessian_mono (I := I) g hEnorm p u hu hiso t R S ht hS (X (eta t))
    · intro t S ht
      refine ⟨lineDistanceSupport_hessianNorm_nonneg (I := I) g hEnorm p u hu hiso t S ht, ?_⟩
      obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
        g hEnorm p u hu hiso t S ht
      exact hessian_diagonal_bound_on g hU hf hx (X (eta t))
    · exact continuousOn_lineDistanceSupport_hessianNorm (I := I) g hEnorm p u hu hiso
    · exact fun a b hab => tendsto_lineDistanceSupport_hessian_energy_zero (I := I)
        g hEnorm hRic p u hu hiso a b hab
  dsimp only [B] at hdiag
  rw [hX] at hdiag
  exact hdiag

theorem tendsto_lineDistanceSupport_hessian_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ)
    (v w : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Tendsto (fun R => hessFun (I := I) g (lineDistanceSupport eta R) (eta s) v w)
      atTop (𝓝 0) ∧
    Tendsto (fun R => hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) R)
      (eta s) v w) atTop (𝓝 0) := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨L, hsym, hp, hm, htrace⟩ :=
    exists_lineDistanceSupport_opposite_hessian_limits (I := I) g hEnorm hRic p u hu hiso s
  have hb : ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s)),
      ∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0 :=
    exists_orthonormal_basis (I := I) g (eta s)
  obtain ⟨b, hON⟩ := hb
  have hnonpos (z : TangentSpace I (eta s)) : L z z ≤ 0 := by
    apply le_of_tendsto (hp z z)
    filter_upwards [eventually_gt_atTop s] with R hR
    exact lineDistanceSupport_hessian_nonpos (I := I) g hEnorm hRic p u hu hiso s R hR z
  have hzero : L = 0 := bilin_eq_zero_of_nonpos_of_trace_zero b L hsym hnonpos (htrace b hON)
  constructor
  · simpa only [hzero, LinearMap.zero_apply] using hp v w
  · simpa only [hzero, LinearMap.zero_apply, neg_zero] using hm v w

theorem tendstoUniformlyOn_lineDistanceSupport_hessian_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (b : (s : ℝ) → Module.Basis (Fin (Module.finrank ℝ E)) ℝ
      (TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)))
    (hON : ∀ s i j, g.inner (intrinsicGeodesic (I := I) g hEnorm p u s)
      (b s i) (b s j) = if i = j then 1 else 0) (A : ℝ) (i j : Fin (Module.finrank ℝ E)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    TendstoUniformlyOn (fun R s => hessFun (I := I) g (lineDistanceSupport eta R)
      (eta s) (b s i) (b s j)) (fun _ => 0) atTop (Icc (-A) A) ∧
    TendstoUniformlyOn (fun R s => hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) R)
      (eta s) (b s i) (b s j)) (fun _ => 0) atTop (Icc (-A) A) := by
  obtain ⟨L, _, _, hL⟩ :=
    exists_lineDistanceSupport_hessian_limits_locally_uniform (I := I) g hEnorm hRic p u hu hiso
  obtain ⟨hp, hm⟩ := hL b hON A i j
  have heq : ∀ s ∈ Icc (-A) A, L s (b s i) (b s j) = 0 := by
    intro s hs
    exact tendsto_nhds_unique (hp.tendsto_at hs)
      (tendsto_lineDistanceSupport_hessian_zero (I := I) g hEnorm hRic p u hu hiso s
        (b s i) (b s j)).1
  refine ⟨hp.congr_right (fun s hs => heq s hs), hm.congr_right ?_⟩
  intro s hs
  simp only [heq s hs, neg_zero]

end Line

end DifferentialGeometry.Geometry.Topology

end
