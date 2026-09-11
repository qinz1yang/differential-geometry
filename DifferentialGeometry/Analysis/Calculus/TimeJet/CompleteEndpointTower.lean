import DifferentialGeometry.Analysis.Elliptic.Barrier.SupportComparison
import DifferentialGeometry.Analysis.Parabolic.Energy.CutoffEnergy
import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointTower

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.Analysis

def completeEndpointTowerBound (c K T : ℝ) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => K ^ 2
  | n + 1 =>
    let L := completeEndpointTowerBound c K T A n
    let a := ((n + 2 : ℕ) : ℝ) * c * (K + L)
    let b := ((n + 1 : ℕ) : ℝ) * c * (K + L) * (L + 1)
    L + Real.exp (a * T) *
      (A (n + 1) ^ 2 + 18 * A n ^ 2 + (a + 18 * b + 90 * L) * T)

theorem completeEndpointTowerBound_nonneg (c K T : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ completeEndpointTowerBound c K T A n := by
  induction n with
  | zero => exact sq_nonneg K
  | succ n ih =>
    simp only [completeEndpointTowerBound]
    positivity

theorem completeEndpointTowerBound_congr_initial (c K T : ℝ) (A B : ℕ → ℝ) (N : ℕ)
    (hAB : ∀ k ≤ N, A k = B k) :
    completeEndpointTowerBound c K T A N = completeEndpointTowerBound c K T B N := by
  have hh : ∀ n, n ≤ N → completeEndpointTowerBound c K T A n = completeEndpointTowerBound c K T B n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [completeEndpointTowerBound, ih (by omega), hAB (n + 1) hn, hAB n (by omega)]
  exact hh N le_rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_product_local (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh) (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) (gradientFun_mul g hfy hhy)

private theorem pair_regular (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T ε t : ℝ) (χ : ℝ → M → ℝ) (x : M) (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (u v : ℝ → M → ℝ)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (u t))) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (v t))) x) :
    DifferentiableWithinAt ℝ (fun s => F.phi s x ^ 2 * u s x + 18 * (F.phi s x * v s x)) (Icc 0 T) t ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => F.phi t z ^ 2 * u t z + 18 * (F.phi t z * v t z)) y) ∧
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (fun z => F.phi t z ^ 2 * u t z + 18 * (F.phi t z * v t z)))) x := by
  let φ := F.phi
  let q := fun s y => φ s y * φ s y
  let U := fun s y => q s y * u s y
  let V := fun s y => φ s y * v s y
  have hqtime := F.time_diff.mul F.time_diff
  have hqspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hqgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hUtime := hqtime.mul hu_time
  have hVtime := F.time_diff.mul hv_time
  have hUspace := hqspace.and hu_space |>.mono fun y hy => hy.1.mul hy.2
  have hVspace := F.space_diff_nhds.and hv_space |>.mono fun y hy => hy.1.mul hy.2
  have hUgrad := gradient_product_local (G.metric t) (q t) (u t) x hqspace hu_space hqgrad hu_grad
  have hVgrad := gradient_product_local (G.metric t) (φ t) (v t) x F.space_diff_nhds hv_space F.grad_diff hv_grad
  have h18space := hVspace.mono fun y hy => (mdifferentiableAt_const (c := (18 : ℝ))).mul hy
  have h18grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (fun y => 18 * V t y))) x := by
    apply (hVgrad.smul_const_section (a := (18 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hVspace] with y hy
    exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I))) (gradientFun_const_smul (G.metric t) 18 hy)
  have hsumspace := hUspace.and h18space |>.mono fun y hy => hy.1.add hy.2
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_two]
    exact hUtime.add (hVtime.const_mul 18)
  · simp only [pow_two]
    exact hsumspace
  · have hr := mdifferentiableAt_add_section hUgrad h18grad
    apply hr.congr_of_eventuallyEq
    filter_upwards [hUspace, h18space] with y huy h18y
    apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    simp only [pow_two]
    exact gradientFun_add (G.metric t) huy h18y

variable [I.Boundaryless]

theorem endpoint_tower_bound_complete
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (w : ℕ → ℝ → M → ℝ) (N : ℕ) (c K : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hwnonneg : ∀ k ≤ N + 1, ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w k t x)
    (hwzero : ∀ t ∈ Icc 0 T, ∀ x, w 0 t x ≤ K ^ 2)
    (hcont : ∀ k ≤ N, ContinuousOn (fun p : ℝ × M => w k p.1 p.2) (Icc 0 T ×ˢ univ))
    (htime : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => w k s x) (Icc 0 T) t)
    (hspace : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (w k t))
    (hinit : ∀ k ≤ N, ∀ x, w k 0 x ≤ A k ^ 2)
    (hheat : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      parabolicOperatorWithDrift G T (fun _ _ => 0) (w k) t x ≤
        -2 * w (k + 1) t x + towerReactionSum w c k t x)
    (hgrad : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      (G.metric t).inner x (gradientFun (I := I) (G.metric t) (w k t) x)
        (gradientFun (I := I) (G.metric t) (w k t) x) ≤ 4 * w k t x * w (k + 1) t x)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x, w k t x ≤ completeEndpointTowerBound c K T A N := by
  have hlevels : ∀ n, n ≤ N → ∀ k ≤ n, ∀ t ∈ Icc 0 T, ∀ x,
      w k t x ≤ completeEndpointTowerBound c K T A n := by
    intro n
    induction n with
    | zero =>
      intro _ k hk t ht x
      have he : k = 0 := by omega
      subst k
      exact hwzero t ht x
    | succ n ih =>
      intro hn
      let L := completeEndpointTowerBound c K T A n
      let a := ((n + 2 : ℕ) : ℝ) * c * (K + L)
      let b := ((n + 1 : ℕ) : ℝ) * c * (K + L) * (L + 1)
      let B := a + 18 * b + 90 * L
      let Q := A (n + 1) ^ 2 + 18 * A n ^ 2
      have hL : 0 ≤ L := completeEndpointTowerBound_nonneg c K T A hc hK hT.le n
      have ha : 0 ≤ a := by dsimp only [a]; positivity
      have hb : 0 ≤ b := by dsimp only [b]; positivity
      have hB : 0 ≤ B := by dsimp only [B]; positivity
      have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
      have hlower := ih (by omega : n ≤ N)
      have hsp (j : ℕ) (hj : j ≤ N) (s : ℝ) (hs : s ∈ Icc 0 T) (hp : 0 < s) (x : M) :
          ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (w j s) y :=
        Eventually.of_forall fun y => (hspace j hj s hs hp).mdifferentiable (by simp) y
      have hPu (s : ℝ) (hs : s ∈ Icc 0 T) (hp : 0 < s) (x : M) :
          parabolicOperatorWithDrift G T (fun _ _ => 0) (w (n + 1)) s x ≤
            -2 * w (n + 2) s x + a * (w (n + 1) s x + 1) := by
        have hr := endpoint_tower_reaction_le (fun j => w j s x) c K L (n + 1)
          hc hK hL (fun j hj => hwnonneg j (by omega) s hs x)
          (hwzero s hs x) (fun j hj => hlower j (by omega) s hs x)
        change towerReactionSum w c (n + 1) s x ≤ a * (w (n + 1) s x + 1) at hr
        exact (hheat (n + 1) hn s hs hp x).trans (add_le_add le_rfl hr)
      have hPv (s : ℝ) (hs : s ∈ Icc 0 T) (hp : 0 < s) (x : M) :
          parabolicOperatorWithDrift G T (fun _ _ => 0) (w n) s x ≤
            -2 * w (n + 1) s x + b := by
        have hr := endpoint_tower_reaction_le (fun j => w j s x) c K L n
          hc hK hL (fun j hj => hwnonneg j (by omega) s hs x)
          (hwzero s hs x) (fun j hj => hlower j (by omega) s hs x)
        change towerReactionSum w c n s x ≤ _ at hr
        have hco : 0 ≤ ((n + 1 : ℕ) : ℝ) * c * (K + L) := by positivity
        have hh := mul_le_mul_of_nonneg_left (add_le_add (hlower n le_rfl s hs x) (le_refl (1 : ℝ))) hco
        exact (hheat n (by omega) s hs hp x).trans (add_le_add le_rfl (hr.trans hh))
      have hnew (t : ℝ) (ht : t ∈ Icc 0 T) (O : M) :
          w (n + 1) t O ≤ Real.exp (a * T) * (Q + B * T) := by
        obtain ⟨cut⟩ := hcut O
        obtain ⟨m, hε, hchi⟩ :=
          ((cut.err_tendsto.eventually_lt_const zero_lt_one).and (cut.center_exhausts t ht)).exists
        let Ecut := fun s y => cut.chi m s y ^ 2 * w (n + 1) s y + 18 * (cut.chi m s y * w n s y)
        have hEc : ContinuousOn (fun p : ℝ × M => Ecut p.1 p.2) (Icc 0 T ×ˢ cut.support m) :=
          (((cut.joint_cont m).pow 2).mul ((hcont (n + 1) hn).mono (prod_mono subset_rfl (subset_univ _)))).add
            (continuousOn_const.mul ((cut.joint_cont m).mul ((hcont n (by omega)).mono (prod_mono subset_rfl (subset_univ _)))))
        have hE0 (x : M) : Ecut 0 x ≤ Q := by
          have hx := cut.range m 0 x ⟨le_rfl, hT.le⟩
          have hsq : cut.chi m 0 x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
          have htop := (mul_le_mul_of_nonneg_right hsq (hwnonneg (n + 1) (by omega) 0 ⟨le_rfl, hT.le⟩ x)).trans
            (by simpa only [one_mul] using hinit (n + 1) hn x)
          have hlow := (mul_le_mul_of_nonneg_right hx.2 (hwnonneg n (by omega) 0 ⟨le_rfl, hT.le⟩ x)).trans
            (by simpa only [one_mul] using hinit n (by omega) x)
          dsimp only [Ecut, Q]
          linarith only [htop, hlow]
        have hbound := scalar_linear_reaction_bound_support G T hT (fun _ _ => 0) Ecut
          (cut.support m) (cut.support_compact m) a B Q ha hB hQ hEc
          (fun s hs x hx => by simp only [Ecut, cut.support_zero m s hs x hx, zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, add_zero, le_refl])
          hE0 (fun s hs hp x hpos => by
            have hcpos : 0 < cut.chi m s x := by
              by_contra hnpos
              have hc0 : cut.chi m s x = 0 := le_antisymm (le_of_not_gt hnpos) (cut.range m s x hs).1
              simp only [Ecut, hc0, zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, add_zero, lt_self_iff_false] at hpos
            let F := cut.lowerSupport m s hs hp x hcpos
            let v := fun r y => F.phi r y ^ 2 * w (n + 1) r y + 18 * (F.phi r y * w n r y)
            have hgU := gradientFun_mdiffAt (G.metric s) (hspace (n + 1) hn s hs hp) x
            have hgV := gradientFun_mdiffAt (G.metric s) (hspace n (by omega) s hs hp) x
            have hr := pair_regular G T (cut.err m) s (cut.chi m) x F (w (n + 1)) (w n)
              (htime (n + 1) hn s hs hp x) (htime n (by omega) s hs hp x)
              (hsp (n + 1) hn s hs hp x) (hsp n (by omega) s hs hp x) hgU hgV
            refine ⟨v, ?_, ?_, hr.1, hr.2.1, hr.2.2, ?_⟩
            · simp only [v, Ecut, F.eq_at]
            · filter_upwards [F.lower_nhds, self_mem_nhdsWithin] with q hq hsl
              have hqs : q.1 ∈ Icc 0 T := hsl.1
              have hh1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq.1 hq.2 2)
                (hwnonneg (n + 1) (by omega) q.1 hqs q.2)
              have hh0 := mul_le_mul_of_nonneg_right hq.2 (hwnonneg n (by omega) q.1 hqs q.2)
              dsimp only [v, Ecut]
              linarith only [hh1, hh0]
            · exact parabolic_cutoff_pair_le G T (cut.err m) s (cut.chi m) x F
                ((uniqueDiffOn_Icc hT) s hs) (cut.err_nonneg m) hε.le (cut.range m s x hs)
                (w (n + 1)) (w n) (w (n + 2) s x) a b L
                (hwnonneg (n + 1) (by omega) s hs x) (hwnonneg n (by omega) s hs x)
                (hwnonneg (n + 2) (by omega) s hs x) (hlower n le_rfl s hs x) ha hb
                (htime (n + 1) hn s hs hp x) (htime n (by omega) s hs hp x)
                (hsp (n + 1) hn s hs hp x) (hsp n (by omega) s hs hp x) hgU hgV
                (hgrad (n + 1) hn s hs hp x) (hgrad n (by omega) s hs hp x) (hPu s hs hp x) (hPv s hs hp x))
        have hh := hbound t ht O
        have hlo : w (n + 1) t O ≤ Real.exp (a * t) * (Q + B * t) := by
          simp only [Ecut, hchi, one_pow, one_mul] at hh
          linarith only [hh, hwnonneg n (by omega) t ht O]
        have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 ha)
        have htB : Q + B * t ≤ Q + B * T := add_le_add le_rfl (mul_le_mul_of_nonneg_left ht.2 hB)
        exact hlo.trans (mul_le_mul he htB (add_nonneg hQ (mul_nonneg hB ht.1)) (Real.exp_pos _).le)
      intro k hk t ht x
      change w k t x ≤ L + Real.exp (a * T) * (Q + B * T)
      by_cases hkn : k ≤ n
      · have hlarge : 0 ≤ Real.exp (a * T) * (Q + B * T) := by positivity
        exact (hlower k hkn t ht x).trans (le_add_of_nonneg_right hlarge)
      · have he : k = n + 1 := by omega
        subst k
        exact (hnew t ht x).trans (le_add_of_nonneg_left hL)
  exact hlevels N le_rfl
end DifferentialGeometry.Analysis
