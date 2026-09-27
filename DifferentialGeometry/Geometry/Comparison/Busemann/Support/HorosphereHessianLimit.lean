import DifferentialGeometry.Geometry.Comparison.Busemann.Support.LineDistanceSupport
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Topology

private theorem exists_limit_of_monotone_tail {f : ℝ → ℝ} (a : ℝ)
    (hm : MonotoneOn f (Ici a)) (hb : BddAbove (f '' Ici a)) :
    ∃ c : ℝ, Tendsto f atTop (𝓝 c) := by
  let F : ℝ → ℝ := fun R => f (max a R)
  have hFm : Monotone F := fun R S hRS =>
    hm (mem_Ici.mpr (le_max_left a R)) (mem_Ici.mpr (le_max_left a S))
      (max_le_max_left a hRS)
  obtain ⟨b, hb⟩ := hb
  have hFb : BddAbove (range F) := ⟨b, by
    rintro _ ⟨R, rfl⟩
    exact hb ⟨max a R, mem_Ici.mpr (le_max_left a R), rfl⟩⟩
  refine ⟨⨆ R, F R, (tendsto_atTop_ciSup hFm hFb).congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with R hR
  simp only [F, max_eq_right hR]

private theorem exists_bilin_limit_of_diagonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ᶠ R in atTop, ∀ v w, B R v w = B R w v)
    (hd : ∀ v, ∃ c : ℝ, Tendsto (fun R => B R v v) atTop (𝓝 c)) :
    ∃ L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ v w, L v w = L w v) ∧
      ∀ v w, Tendsto (fun R => B R v w) atTop (𝓝 (L v w)) := by
  classical
  choose q hq using hd
  let l : V → V → ℝ := fun v w => (q (v + w) - q v - q w) / 2
  have hl (v w : V) : Tendsto (fun R => B R v w) atTop (𝓝 (l v w)) := by
    have ht := (((hq (v + w)).sub (hq v)).sub (hq w)).div_const 2
    apply ht.congr'
    filter_upwards [hs] with R hR
    simp only [map_add, LinearMap.add_apply]
    rw [hR w v]
    ring
  let L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ l
    (fun v v' w => by
      apply tendsto_nhds_unique (hl (v + v') w)
      simpa only [map_add, LinearMap.add_apply] using (hl v w).add (hl v' w))
    (fun c v w => by
      apply tendsto_nhds_unique (hl (c • v) w)
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using
        tendsto_const_nhds.mul (hl v w))
    (fun v w w' => by
      apply tendsto_nhds_unique (hl v (w + w'))
      simpa only [map_add] using (hl v w).add (hl v w'))
    (fun c v w => by
      apply tendsto_nhds_unique (hl v (c • w))
      simpa only [map_smul, smul_eq_mul] using tendsto_const_nhds.mul (hl v w))
  refine ⟨L, ?_, hl⟩
  intro v w
  apply tendsto_nhds_unique (hl v w)
  apply (hl w v).congr'
  filter_upwards [hs] with R hR
  exact hR w v

private theorem abs_bilin_apply_le_trace
    {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]
    (e : ι → V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hn : ∀ v, 0 ≤ B v v) (i j : ι) :
    |B (e i) (e j)| ≤ ∑ k, B (e k) (e k) := by
  classical
  have hi := Finset.single_le_sum (fun k _ => hn (e k)) (Finset.mem_univ i)
  have hj := Finset.single_le_sum (fun k _ => hn (e k)) (Finset.mem_univ j)
  have hp := hn (e i + e j)
  have hm := hn (e i - e j)
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hp hm
  rw [hs (e j) (e i)] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem bilin_limit_error_le
    {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]
    (e : ι → V) (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (R c : ℝ)
    (hsL : ∀ v w, L v w = L w v) (hsR : ∀ v w, B R v w = B R w v)
    (hm : ∀ S, R ≤ S → ∀ v, B R v v ≤ B S v v)
    (hl : ∀ v w, Tendsto (fun S => B S v w) atTop (𝓝 (L v w)))
    (htrL : ∑ i, L (e i) (e i) = 0)
    (htrR : -c ≤ ∑ i, B R (e i) (e i)) (i j : ι) :
    |L (e i) (e j) - B R (e i) (e j)| ≤ c := by
  have hn (v : V) : 0 ≤ (L - B R) v v := by
    have hle : B R v v ≤ L v v := by
      apply ge_of_tendsto (hl v v)
      filter_upwards [eventually_ge_atTop R] with S hS
      exact hm S hS v
    exact sub_nonneg.mpr hle
  have hs (v w : V) : (L - B R) v w = (L - B R) w v := by
    change L v w - B R v w = L w v - B R w v
    rw [hsL v w, hsR v w]
  have h := abs_bilin_apply_le_trace e (L - B R) hs hn i j
  change |L (e i) (e j) - B R (e i) (e j)| ≤
    ∑ k, (L (e k) (e k) - B R (e k) (e k)) at h
  rw [Finset.sum_sub_distrib, htrL, zero_sub] at h
  exact h.trans (by linarith)

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem hessian_symm_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w = hessFun (I := I) g f x w v := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  rw [← hessFun_congr (I := I) g hFf]
  exact hessFun_symm_of_boundaryless (I := I) g hF x v w

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem laplacian_eq_sum_hessian (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i, hessFun (I := I) g f x (b i) (b i) := by
  classical
  rw [lap_eq_hess_on (I := I) g hU hf hx,
    metricTracePair0SAt_eq_sum_basis (I := I) g b
      (fun i j => if i = j then 1 else 0)
      (metricInverseInBasis_of_orthonormal (I := I) g b hON)]
  simp only [hessTensorAt_apply, ite_mul, one_mul, zero_mul]
  simp

theorem exists_lineDistanceSupport_hessian_limits
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ Lplus Lminus : TangentSpace I (eta s) →ₗ[ℝ] TangentSpace I (eta s) →ₗ[ℝ] ℝ,
      (∀ v w, Lplus v w = Lplus w v) ∧
      (∀ v w, Lminus v w = Lminus w v) ∧
      (∀ v w, Tendsto (fun R => hessFun (I := I) g
        (lineDistanceSupport eta R) (eta s) v w) atTop (𝓝 (Lplus v w))) ∧
      (∀ v w, Tendsto (fun R => hessFun (I := I) g
        (lineDistanceSupport (fun t => eta (-t)) R) (eta s) v w)
          atTop (𝓝 (Lminus v w))) ∧
      ∀ v, Lplus v v + Lminus v v ≤ 0 := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  let Bplus (R : ℝ) := hessFun (I := I) g (lineDistanceSupport eta R) (eta s)
  let Bminus (R : ℝ) :=
    hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) R) (eta s)
  let a : ℝ := |s| + 1
  have ha : s < a := by dsimp only [a]; linarith [le_abs_self s]
  have hna : -s < a := by dsimp only [a]; linarith [neg_le_abs s]
  have hplus (v : TangentSpace I (eta s)) :
      ∃ c : ℝ, Tendsto (fun R => Bplus R v v) atTop (𝓝 c) := by
    apply exists_limit_of_monotone_tail a
    · intro R hR S _ hRS
      exact lineDistanceSupport_hessian_mono (I := I) g hEnorm p u hu hiso
        s R S (ha.trans_le hR) hRS v
    · refine ⟨-Bminus a v v, ?_⟩
      rintro _ ⟨R, hR, rfl⟩
      have h := lineDistanceSupport_opposite_hessian_nonpos (I := I) g hEnorm
        p u hu hiso s R a (ha.trans_le hR) hna v
      change Bplus R v v + Bminus a v v ≤ 0 at h
      linarith
  have hminus (v : TangentSpace I (eta s)) :
      ∃ c : ℝ, Tendsto (fun R => Bminus R v v) atTop (𝓝 c) := by
    apply exists_limit_of_monotone_tail a
    · intro R hR S _ hRS
      exact reverse_lineDistanceSupport_hessian_mono (I := I) g hEnorm p u hu hiso
        s R S (hna.trans_le hR) hRS v
    · refine ⟨-Bplus a v v, ?_⟩
      rintro _ ⟨R, hR, rfl⟩
      have h := lineDistanceSupport_opposite_hessian_nonpos (I := I) g hEnorm
        p u hu hiso s a R ha (hna.trans_le hR) v
      change Bplus a v v + Bminus R v v ≤ 0 at h
      linarith
  have hsplus : ∀ᶠ R in atTop, ∀ v w, Bplus R v w = Bplus R w v := by
    filter_upwards [eventually_ge_atTop a] with R hR
    obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
      g hEnorm p u hu hiso s R (ha.trans_le hR)
    exact hessian_symm_on g hU hf hx
  have hsminus : ∀ᶠ R in atTop, ∀ v w, Bminus R v w = Bminus R w v := by
    filter_upwards [eventually_ge_atTop a] with R hR
    obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_reverse_lineDistanceSupport (I := I)
      g hEnorm p u hu hiso s R (hna.trans_le hR)
    exact hessian_symm_on g hU hf hx
  obtain ⟨Lplus, hsLplus, hLplus⟩ := exists_bilin_limit_of_diagonal Bplus hsplus hplus
  obtain ⟨Lminus, hsLminus, hLminus⟩ := exists_bilin_limit_of_diagonal Bminus hsminus hminus
  refine ⟨Lplus, Lminus, hsLplus, hsLminus, hLplus, hLminus, fun v => ?_⟩
  apply le_of_tendsto ((hLplus v v).add (hLminus v v))
  filter_upwards [eventually_ge_atTop a] with R hR
  exact lineDistanceSupport_opposite_hessian_nonpos (I := I) g hEnorm
    p u hu hiso s R R (ha.trans_le hR) (hna.trans_le hR) v

theorem exists_lineDistanceSupport_opposite_hessian_limits
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ L : TangentSpace I (eta s) →ₗ[ℝ] TangentSpace I (eta s) →ₗ[ℝ] ℝ,
      (∀ v w, L v w = L w v) ∧
      (∀ v w, Tendsto (fun R => hessFun (I := I) g
        (lineDistanceSupport eta R) (eta s) v w) atTop (𝓝 (L v w))) ∧
      (∀ v w, Tendsto (fun R => hessFun (I := I) g
        (lineDistanceSupport (fun t => eta (-t)) R) (eta s) v w)
          atTop (𝓝 (-L v w))) ∧
      ∀ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s))),
        (∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0) →
          ∑ i, L (b i) (b i) = 0 := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨Lp, Lm, hsp, hsm, hLp, hLm, hsum⟩ :=
    exists_lineDistanceSupport_hessian_limits (I := I) g hEnorm p u hu hiso s
  let n : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
  have hdenp : Tendsto (fun R : ℝ => R - s) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (b + s)] with R hR
    linarith
  have hdenm : Tendsto (fun R : ℝ => R + s) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (b - s)] with R hR
    linarith
  have hlowp : Tendsto (fun R : ℝ => -(n / (R - s))) atTop (𝓝 0) := by
    simpa only [neg_zero] using (hdenp.const_div_atTop n).neg
  have hlowm : Tendsto (fun R : ℝ => -(n / (R + s))) atTop (𝓝 0) := by
    simpa only [neg_zero] using (hdenm.const_div_atTop n).neg
  have htraces (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s)))
      (hON : ∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0) :
      (∑ i, Lp (b i) (b i) = 0) ∧ (∑ i, Lm (b i) (b i) = 0) := by
    have hcp := tendsto_finsetSum Finset.univ (fun i _ => hLp (b i) (b i))
    have hcm := tendsto_finsetSum Finset.univ (fun i _ => hLm (b i) (b i))
    have hp : 0 ≤ ∑ i, Lp (b i) (b i) := by
      apply le_of_tendsto_of_tendsto hlowp hcp
      filter_upwards [eventually_gt_atTop s] with R hR
      obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
        g hEnorm p u hu hiso s R hR
      have h := lineDistanceSupport_laplacian_ge (I := I) g hEnorm hRic p u hu hiso s R hR
      dsimp only at h
      rw [laplacian_eq_sum_hessian g hU hf hx b hON] at h
      exact h
    have hm : 0 ≤ ∑ i, Lm (b i) (b i) := by
      apply le_of_tendsto_of_tendsto hlowm hcm
      filter_upwards [eventually_gt_atTop (-s)] with R hR
      obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_reverse_lineDistanceSupport (I := I)
        g hEnorm p u hu hiso s R hR
      have h := reverse_lineDistanceSupport_laplacian_ge (I := I)
        g hEnorm hRic p u hu hiso s R hR
      dsimp only at h
      rw [laplacian_eq_sum_hessian g hU hf hx b hON] at h
      exact h
    have hs : (∑ i, Lp (b i) (b i)) + (∑ i, Lm (b i) (b i)) ≤ 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_nonpos fun i _ => hsum (b i)
    constructor <;> linarith
  have hb : ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s)),
      ∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0 :=
    exists_orthonormal_basis (I := I) g (eta s)
  obtain ⟨b, hON⟩ := hb
  have hzero : Lp + Lm = 0 := by
    apply bilin_eq_zero_of_nonpos_of_trace_zero b (Lp + Lm)
    · intro v w
      change Lp v w + Lm v w = Lp w v + Lm w v
      rw [hsp v w, hsm v w]
    · exact hsum
    · change ∑ i, (Lp (b i) (b i) + Lm (b i) (b i)) = 0
      rw [Finset.sum_add_distrib, (htraces b hON).1, (htraces b hON).2, add_zero]
  refine ⟨Lp, hsp, hLp, ?_, fun b hON => (htraces b hON).1⟩
  intro v w
  have hvw := congrArg (fun B : TangentSpace I (eta s) →ₗ[ℝ]
      TangentSpace I (eta s) →ₗ[ℝ] ℝ => B v w) hzero
  change Lp v w + Lm v w = 0 at hvw
  have heq : Lm v w = -Lp v w := by linarith
  rw [← heq]
  exact hLm v w

theorem exists_lineDistanceSupport_hessian_limit_rate
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    let n : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
    ∃ L : TangentSpace I (eta s) →ₗ[ℝ] TangentSpace I (eta s) →ₗ[ℝ] ℝ,
      (∀ v w, L v w = L w v) ∧
      ∀ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s))),
        (∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0) →
          (∑ i, L (b i) (b i) = 0) ∧
          (∀ R, s < R → ∀ i j,
            |L (b i) (b j) - hessFun (I := I) g (lineDistanceSupport eta R)
              (eta s) (b i) (b j)| ≤ n / (R - s)) ∧
          (∀ R, -s < R → ∀ i j,
            |-L (b i) (b j) - hessFun (I := I) g
              (lineDistanceSupport (fun t => eta (-t)) R) (eta s) (b i) (b j)| ≤
                n / (R + s)) := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨L, hsL, hp, hm, htr⟩ :=
    exists_lineDistanceSupport_opposite_hessian_limits (I := I)
      g hEnorm hRic p u hu hiso s
  refine ⟨L, hsL, fun b hON => ⟨htr b hON, ?_, ?_⟩⟩
  · intro R hR i j
    obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
      g hEnorm p u hu hiso s R hR
    apply bilin_limit_error_le b
      (fun S => hessFun (I := I) g (lineDistanceSupport eta S) (eta s))
      L R _ hsL (hessian_symm_on g hU hf hx)
      (fun S hRS v => lineDistanceSupport_hessian_mono (I := I)
        g hEnorm p u hu hiso s R S hR hRS v) hp (htr b hON)
    have h := lineDistanceSupport_laplacian_ge (I := I) g hEnorm hRic p u hu hiso s R hR
    dsimp only at h
    rw [laplacian_eq_sum_hessian g hU hf hx b hON] at h
    exact h
  · intro R hR i j
    obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_reverse_lineDistanceSupport (I := I)
      g hEnorm p u hu hiso s R hR
    have hsneg (v w : TangentSpace I (eta s)) : (-L) v w = (-L) w v := by
      change -L v w = -L w v
      rw [hsL v w]
    have htrneg : ∑ i, (-L) (b i) (b i) = 0 := by
      change ∑ i, -(L (b i) (b i)) = 0
      rw [Finset.sum_neg_distrib, htr b hON, neg_zero]
    apply bilin_limit_error_le b
      (fun S => hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) S) (eta s))
      (-L) R _ hsneg (hessian_symm_on g hU hf hx)
      (fun S hRS v => reverse_lineDistanceSupport_hessian_mono (I := I)
        g hEnorm p u hu hiso s R S hR hRS v) hm htrneg
    have h := reverse_lineDistanceSupport_laplacian_ge (I := I)
      g hEnorm hRic p u hu hiso s R hR
    dsimp only at h
    rw [laplacian_eq_sum_hessian g hU hf hx b hON] at h
    exact h

theorem exists_lineDistanceSupport_hessian_limits_locally_uniform
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ L : (s : ℝ) → TangentSpace I (eta s) →ₗ[ℝ] TangentSpace I (eta s) →ₗ[ℝ] ℝ,
      (∀ s v w, L s v w = L s w v) ∧
      (∀ s (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s))),
        (∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0) →
          ∑ i, L s (b i) (b i) = 0) ∧
      ∀ (b : (s : ℝ) → Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s))),
        (∀ s i j, g.inner (eta s) (b s i) (b s j) = if i = j then 1 else 0) →
        ∀ (A : ℝ) (i j : Fin (Module.finrank ℝ E)),
          TendstoUniformlyOn
            (fun R s => hessFun (I := I) g (lineDistanceSupport eta R)
              (eta s) (b s i) (b s j))
            (fun s => L s (b s i) (b s j)) atTop (Icc (-A) A) ∧
          TendstoUniformlyOn
            (fun R s => hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) R)
              (eta s) (b s i) (b s j))
            (fun s => -L s (b s i) (b s j)) atTop (Icc (-A) A) := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hex (s : ℝ) := exists_lineDistanceSupport_hessian_limit_rate (I := I)
    g hEnorm hRic p u hu hiso s
  dsimp only at hex
  choose L hsL hL using hex
  refine ⟨L, hsL, fun s b hb => (hL s b hb).1, ?_⟩
  intro b hON A i j
  let n : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hden : Tendsto (fun R : ℝ => R - A) atTop atTop := by
    refine tendsto_atTop.mpr fun c => ?_
    filter_upwards [eventually_ge_atTop (c + A)] with R hR
    linarith
  have herr : Tendsto (fun R : ℝ => n / (R - A)) atTop (𝓝 0) :=
    hden.const_div_atTop n
  constructor
  · rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [eventually_gt_atTop A, herr.eventually (gt_mem_nhds heps)] with R hRA hReps
    intro s hs
    have hRs : s < R := lt_of_le_of_lt hs.2 hRA
    have hbnd : n / (R - s) ≤ n / (R - A) :=
      div_le_div_of_nonneg_left hn (sub_pos.mpr hRA) (by linarith [hs.2])
    rw [Real.dist_eq]
    exact ((hL s (b s) (hON s)).2.1 R hRs i j).trans_lt (hbnd.trans_lt hReps)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [eventually_gt_atTop A, herr.eventually (gt_mem_nhds heps)] with R hRA hReps
    intro s hs
    have hRs : -s < R := by linarith [hs.1]
    have hbnd : n / (R + s) ≤ n / (R - A) :=
      div_le_div_of_nonneg_left hn (sub_pos.mpr hRA) (by linarith [hs.1])
    rw [Real.dist_eq]
    exact ((hL s (b s) (hON s)).2.2 R hRs i j).trans_lt (hbnd.trans_lt hReps)

end DifferentialGeometry.Geometry.Topology

end
