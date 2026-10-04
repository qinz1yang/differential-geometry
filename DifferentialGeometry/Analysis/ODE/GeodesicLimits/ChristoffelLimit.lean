import DifferentialGeometry.Analysis.ODE.GeodesicLimits.DerivativeLimit
import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# CM4.a: `C¹` subsequential limits of geodesic-type curves under uniform coefficient convergence

Chart kernel of the geodesic-limit package (lane CM-L; D-FOUND's CM4.a, design item G5; blueprint
LC50, A:22511, and LFR18, A:26261, "Arzela–Ascoli on chart intervals" step).

Let `Γ i, ΓInf : F → F →L F →L F` with `Γ i → ΓInf` uniformly on a compact `K` and `ΓInf` continuous
on `K`. Curves `γ i` in `K` on `[0,T]` with `γ i' = γ' i`, `(γ' i)' = -Γ i (γ i) (γ' i, γ' i)` and
`‖γ' i‖ ≤ L` have a subsequence converging in `C¹` (uniformly with the velocities) on `[0,T]` to a
solution of the limit equation, one-sided derivatives at the endpoints included.

No bound on the `Γ i` for small `i` and no Lipschitz bound on any `Γ` is used: the acceleration bound
holds for a tail, and the limit equation is passed through uniform convergence of the accelerations.
The interface statement's hypothesis `0 < T` is dropped (unused; for `T < 0` the claim is vacuous).
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

/-- Uniform convergence of pairs, same filter and same domain (metric form). -/
theorem tendstoUniformlyOn_prodMk {α β β' ι : Type*} [PseudoMetricSpace β]
    [PseudoMetricSpace β'] {p : Filter ι} {F : ι → α → β} {f : α → β} {G : ι → α → β'}
    {g : α → β'} {s : Set α} (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s) :
    TendstoUniformlyOn (fun i x => (F i x, G i x)) (fun x => (f x, g x)) p s := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  filter_upwards [hF ε hε, hG ε hε] with i hi hi' x hx
  rw [Prod.dist_eq]
  exact max_lt (hi x hx) (hi' x hx)

/-- **CM4.a.** Moving-coefficient geodesic limit (Arzelà–Ascoli on position and velocity). -/
theorem exists_C1_subseq_limit_of_christoffel_tendsto
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Set F} (hK : IsCompact K) (Γ : ℕ → F → F →L[ℝ] F →L[ℝ] F)
    (ΓInf : F → F →L[ℝ] F →L[ℝ] F) (hΓInf : ContinuousOn ΓInf K)
    (hconv : TendstoUniformlyOn Γ ΓInf atTop K) {T L : ℝ}
    (γ γ' : ℕ → ℝ → F)
    (hmaps : ∀ i, ∀ t ∈ Icc 0 T, γ i t ∈ K)
    (hvel : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ i) (γ' i t) (Icc 0 T) t)
    (hacc : ∀ i, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (γ' i) (-(Γ i (γ i t) (γ' i t) (γ' i t))) (Icc 0 T) t)
    (hbound : ∀ i, ∀ t ∈ Icc 0 T, ‖γ' i t‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c c' : ℝ → F,
      TendstoUniformlyOn (fun i => γ (φ i)) c atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun i => γ' (φ i)) c' atTop (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, c t ∈ K ∧ HasDerivWithinAt c (c' t) (Icc 0 T) t ∧
        HasDerivWithinAt c' (-(ΓInf (c t) (c' t) (c' t))) (Icc 0 T) t := by
  -- bounds on the coefficients: `ΓInf` on `K`, and `Γ i` for a tail
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := ΓInf) hΓInf
  have hconvM : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, dist (ΓInf x) (Γ n x) < ε :=
    (Metric.tendstoUniformlyOn_iff (F := Γ) (f := ΓInf) (p := atTop) (s := K)).mp hconv
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hconvM 1 one_pos)
  have hΓbd : ∀ i, N ≤ i → ∀ x ∈ K, ‖Γ i x‖ ≤ B + 1 := by
    intro i hi x hx
    have h1 : ‖ΓInf x - Γ i x‖ < 1 := by
      have h := hN i hi x hx
      rwa [dist_eq_norm (ΓInf x) (Γ i x)] at h
    calc ‖Γ i x‖ = ‖ΓInf x - (ΓInf x - Γ i x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖ΓInf x‖ + ‖ΓInf x - Γ i x‖ := norm_sub_le (ΓInf x) (ΓInf x - Γ i x)
      _ ≤ B + 1 := by linarith [hB x hx]
  set A : ℝ := (B + 1) * L * L with hA
  have hacc_bd : ∀ i, N ≤ i → ∀ t ∈ Icc 0 T, ‖-(Γ i (γ i t) (γ' i t) (γ' i t))‖ ≤ A := by
    intro i hi t ht
    rw [norm_neg]
    have hv := hbound i t ht
    have hv0 := norm_nonneg (γ' i t)
    have hΓ := hΓbd i hi _ (hmaps i t ht)
    have hn := norm_nonneg (Γ i (γ i t))
    have hBL : 0 ≤ (B + 1) * L := mul_nonneg (hn.trans hΓ) (hv0.trans hv)
    calc ‖Γ i (γ i t) (γ' i t) (γ' i t)‖
        ≤ ‖Γ i (γ i t) (γ' i t)‖ * ‖γ' i t‖ := (Γ i (γ i t) (γ' i t)).le_opNorm _
      _ ≤ ‖Γ i (γ i t)‖ * ‖γ' i t‖ * ‖γ' i t‖ :=
          mul_le_mul_of_nonneg_right ((Γ i (γ i t)).le_opNorm _) hv0
      _ ≤ (B + 1) * L * L :=
          mul_le_mul (mul_le_mul hΓ hv hv0 (hn.trans hΓ)) hv hv0 hBL
  -- Lipschitz bounds on `[0,T]`
  have hlipγ : ∀ i, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ‖γ i s - γ i t‖ ≤ L * ‖s - t‖ :=
    fun i s hs t ht =>
      (convex_Icc 0 T).norm_image_sub_le_of_norm_hasDerivWithin_le (hvel i) (hbound i) ht hs
  have hlipγ' : ∀ i, N ≤ i → ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖γ' i s - γ' i t‖ ≤ A * ‖s - t‖ :=
    fun i hi s hs t ht =>
      (convex_Icc 0 T).norm_image_sub_le_of_norm_hasDerivWithin_le (hacc i) (hacc_bd i hi) ht hs
  have hcontγ : ∀ i, ContinuousOn (γ i) (Icc 0 T) :=
    fun i t ht => (hvel i t ht).continuousWithinAt
  have hcontγ' : ∀ i, ContinuousOn (γ' i) (Icc 0 T) :=
    fun i t ht => (hacc i t ht).continuousWithinAt
  -- the shifted sequence of continuous maps `[0,T] → F × F`
  let f : ℕ → C(Icc (0 : ℝ) T, F × F) := fun n =>
    ⟨(Icc (0 : ℝ) T).domRestrict (fun t => (γ (n + N) t, γ' (n + N) t)),
      ((hcontγ (n + N)).prodMk (hcontγ' (n + N))).domRestrict⟩
  have hval : ∀ n x, f n x ∈ K ×ˢ closedBall (0 : F) L := by
    intro n x
    exact ⟨hmaps _ x x.2, mem_closedBall_zero_iff.mpr (hbound _ x x.2)⟩
  let Lip : ℝ≥0 := Real.toNNReal (max L A)
  have hLip : ∀ n, LipschitzWith Lip (f n : Icc (0 : ℝ) T → F × F) := by
    intro n
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hxy : dist x y = ‖(x : ℝ) - y‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    rw [Prod.dist_eq, hxy, Real.coe_toNNReal _ ((norm_nonneg _).trans
      ((hbound 0 x x.2).trans (le_max_left L A)))]
    have h1 := hlipγ (n + N) x x.2 y y.2
    have h2 := hlipγ' (n + N) (Nat.le_add_left N n) x x.2 y y.2
    rw [← dist_eq_norm] at h1 h2
    refine max_le (h1.trans ?_) (h2.trans ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_left L A) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (le_max_right L A) (norm_nonneg _)
  have hequi : Equicontinuous (fun n => (f n : Icc (0 : ℝ) T → F × F)) :=
    (LipschitzWith.uniformEquicontinuous _ Lip hLip).equicontinuous
  obtain ⟨φ₀, G, hφ₀, hG⟩ := DifferentialGeometry.Analysis.arzela_subseq_compact
    (K ×ˢ closedBall (0 : F) L) (hK.prod (isCompact_closedBall 0 L)) f hval hequi
  -- the limit curves
  let c : ℝ → F := fun t => if h : t ∈ Icc (0 : ℝ) T then (G ⟨t, h⟩).1 else 0
  let c' : ℝ → F := fun t => if h : t ∈ Icc (0 : ℝ) T then (G ⟨t, h⟩).2 else 0
  let φ : ℕ → ℕ := fun n => φ₀ n + N
  have hφ : StrictMono φ := fun a b hab => Nat.add_lt_add_right (hφ₀ hab) N
  have hφN : ∀ n, N ≤ φ n := fun n => Nat.le_add_left N (φ₀ n)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hconvγ : TendstoUniformlyOn (fun i => γ (φ i)) c atTop (Icc 0 T) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have h := uniformContinuous_fst.comp_tendstoUniformly hG
    have hceq : c ∘ Subtype.val = Prod.fst ∘ (G : Icc (0 : ℝ) T → F × F) := by
      funext x
      exact dite_eq_left_of_eq_true (eq_true x.2)
    rw [hceq]
    exact h
  have hconvγ' : TendstoUniformlyOn (fun i => γ' (φ i)) c' atTop (Icc 0 T) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have h := uniformContinuous_snd.comp_tendstoUniformly hG
    have hceq : c' ∘ Subtype.val = Prod.snd ∘ (G : Icc (0 : ℝ) T → F × F) := by
      funext x
      exact dite_eq_left_of_eq_true (eq_true x.2)
    rw [hceq]
    exact h
  have hcK : ∀ t ∈ Icc 0 T, c t ∈ K := fun t ht =>
    hK.isClosed.mem_of_tendsto (hconvγ.tendsto_at ht)
      (Eventually.of_forall fun i => hmaps (φ i) t ht)
  have hc'L : ∀ t ∈ Icc 0 T, c' t ∈ closedBall (0 : F) L := fun t ht =>
    isClosed_closedBall.mem_of_tendsto (hconvγ'.tendsto_at ht)
      (Eventually.of_forall fun i => mem_closedBall_zero_iff.mpr (hbound (φ i) t ht))
  have hc_cont : ContinuousOn c (Icc 0 T) :=
    hconvγ.continuousOn (Eventually.of_forall fun i => hcontγ (φ i)).frequently
  have hc'_cont : ContinuousOn c' (Icc 0 T) :=
    hconvγ'.continuousOn (Eventually.of_forall fun i => hcontγ' (φ i)).frequently
  -- uniform convergence of the coefficients along the curves
  have hcoefM : ∀ ε > 0, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T,
      dist (ΓInf (c t)) (Γ (φ i) (γ (φ i) t)) < ε := by
    have h1 := hconvγ.comp_continuousOn_of_isCompact (Ψ := ΓInf) hK
      (fun i t ht => hmaps (φ i) t ht) hcK hΓInf
    rw [Metric.tendstoUniformlyOn_iff] at h1
    intro ε hε
    have h2 := hφtop.eventually (hconvM (ε / 2) (by positivity))
    filter_upwards [h1 (ε / 2) (by positivity), h2] with i hi hi' t ht
    calc dist (ΓInf (c t)) (Γ (φ i) (γ (φ i) t))
        ≤ dist (ΓInf (c t)) (ΓInf (γ (φ i) t)) +
            dist (ΓInf (γ (φ i) t)) (Γ (φ i) (γ (φ i) t)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hi t ht) (hi' _ (hmaps (φ i) t ht))
      _ = ε := add_halves ε
  have hpair := tendstoUniformlyOn_prodMk (Metric.tendstoUniformlyOn_iff.mpr hcoefM) hconvγ'
  let Ψ : (F →L[ℝ] F →L[ℝ] F) × F → F := fun q => -(q.1 q.2 q.2)
  have hΨ : Continuous Ψ :=
    ((continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd).neg
  have : ProperSpace (F →L[ℝ] F →L[ℝ] F) := FiniteDimensional.proper ℝ (F →L[ℝ] F →L[ℝ] F)
  have haccconv : TendstoUniformlyOn
      (fun i t => -(Γ (φ i) (γ (φ i) t) (γ' (φ i) t) (γ' (φ i) t)))
      (fun t => -(ΓInf (c t) (c' t) (c' t))) atTop (Icc 0 T) :=
    hpair.comp_continuousAt_of_isCompact (Ψ := Ψ)
      ((isCompact_closedBall (0 : F →L[ℝ] F →L[ℝ] F) B).prod (isCompact_closedBall (0 : F) L))
      (fun t ht => Set.mk_mem_prod (mem_closedBall_zero_iff.mpr (hB _ (hcK t ht))) (hc'L t ht))
      (fun y _ => hΨ.continuousAt)
  have haccInf_cont : ContinuousOn (fun t => -(ΓInf (c t) (c' t) (c' t))) (Icc 0 T) := by
    have hΓc : ContinuousOn (fun t => ΓInf (c t)) (Icc 0 T) :=
      hΓInf.comp hc_cont (fun t ht => hcK t ht)
    exact ((hΓc.clm_apply hc'_cont).clm_apply hc'_cont).neg
  refine ⟨φ, hφ, c, c', hconvγ, hconvγ', fun t ht => ⟨hcK t ht, ?_, ?_⟩⟩
  · exact hasDerivWithinAt_of_tendsto_of_tendstoUniformlyOn_deriv
      (fun i => hvel (φ i)) (fun s hs => hconvγ.tendsto_at hs) hconvγ' hc'_cont t ht
  · exact hasDerivWithinAt_of_tendsto_of_tendstoUniformlyOn_deriv
      (fun i => hacc (φ i)) (fun s hs => hconvγ'.tendsto_at hs) haccconv haccInf_cont t ht

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
