import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology


def localCubicBarrierRate (D ℓ ρ : ℝ) : ℝ :=
  (3 * D + 24 * ℓ) ^ 2 / (96 * ℓ * ρ ^ 2)

private theorem cubic_coefficient_bound {D ℓ ρ z L e : ℝ}
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hz : 0 ≤ z)
    (hL : -D ≤ L) (he : 4 * ℓ * (ρ ^ 2 - z) ≤ e) :
    -(localCubicBarrierRate D ℓ ρ) * z ^ 3 ≤
      3 * z ^ 2 * L + 6 * z * e := by
  let a : ℝ := 24 * ℓ * ρ ^ 2
  let b : ℝ := 3 * D + 24 * ℓ
  have ha : 0 < a := by dsimp [a]; positivity
  have hrate : localCubicBarrierRate D ℓ ρ = b ^ 2 / (4 * a) := by
    dsimp [localCubicBarrierRate, a, b]
    congr 1
    ring
  have hid :
      4 * a * (a + b ^ 2 / (4 * a) * z ^ 2 - b * z) =
        (b * z - 2 * a) ^ 2 := by
    field_simp
    ring
  have hquad : 0 ≤ a + b ^ 2 / (4 * a) * z ^ 2 - b * z :=
    nonneg_of_mul_nonneg_right (hid.symm ▸ sq_nonneg (b * z - 2 * a))
      (by positivity)
  have hcubic := mul_nonneg hz hquad
  have hfirst := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 3 * z ^ 2)
  have hsecond := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 6 * z)
  rw [hrate]
  dsimp [a, b] at hcubic
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem heatDrift_cubic_cutoff_lower_bound
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (t : ℝ) (X : (x : M) → TangentSpace I x) {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D ℓ ρ : ℝ}
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hx : 0 ≤ f x)
    (hL : -D ≤ heatOperatorWithDrift (I := I) G t X f x)
    (he : 4 * ℓ * (ρ ^ 2 - f x) ≤
      (G.metric t).inner x (gradientAt G t f x) (gradientAt G t f x)) :
    -(localCubicBarrierRate D ℓ ρ) * f x ^ 3 ≤
      heatOperatorWithDrift (I := I) G t X (fun y => f y ^ 3) x := by
  have hderiv : deriv (fun s : ℝ => s ^ 3) = fun s => 3 * s ^ 2 := by
    funext s
    simp
  have hsecond : ∀ s : ℝ, deriv (fun r : ℝ => 3 * r ^ 2) s = 6 * s := by
    intro s
    simp
    ring
  have hchain := heatDrift_comp (I := I) G t X
    (φ := fun s : ℝ => s ^ 3) (f := f) (x := x)
    (differentiable_id.pow 3)
    (by rw [hderiv]; fun_prop)
    (fun y => hf.mdifferentiable (by simp) y)
    (gradientFun_mdiffAt (G.metric t) hf x)
  rw [hderiv, hsecond] at hchain
  rw [hchain]
  exact cubic_coefficient_bound hℓ hρ hx hL he

private theorem gradient_sub_mdiffAt
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDiffAt (T% fun y : M => gradientFun g f y) x)
    (hgh : MDiffAt (T% fun y : M => gradientFun g h y) x) :
    MDiffAt (T% fun y : M => gradientFun g (fun z => f z - h z) y) x := by
  refine (mdifferentiableAt_sub_section hgf hgh).congr_of_eventuallyEq ?_
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun v => (⟨y, v⟩ : TotalSpace E (TangentSpace I : M → Type _)))
    (gradientFun_sub g hfy hhy)

private theorem parabolic_sub_local
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    {u v : ℝ → M → ℝ} {t : ℝ} {x : M}
    (hut : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hvt : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hvs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hug : MDiffAt (T% fun y : M => gradientFun (G.metric t) (u t) y) x)
    (hvg : MDiffAt (T% fun y : M => gradientFun (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift G T X (fun s y => u s y - v s y) t x =
      parabolicOperatorWithDrift G T X u t x -
        parabolicOperatorWithDrift G T X v t x := by
  have heq : (fun y : M => gradientFun (G.metric t) (fun z => u t z - v t z) y)
      =ᶠ[𝓝 x] (fun y => gradientFun (G.metric t) (u t) y -
        gradientFun (G.metric t) (v t) y) := by
    filter_upwards [hus, hvs] with y huy hvy
    exact gradientFun_sub (G.metric t) huy hvy
  have hcov := (G.connection t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (gradient_sub_mdiffAt (G.metric t) hus hvs hug hvg)
    (mdifferentiableAt_sub_section hug hvg) Filter.univ_mem heq
  have hlap : laplacianAt G t (fun y => u t y - v t y) x =
      laplacianAt G t (u t) x - laplacianAt G t (v t) x := by
    change divergence (G.connection t)
      (fun y => gradientFun (G.metric t) (fun z => u t z - v t z) y) x = _
    calc
      _ = divergence (G.connection t)
          ((fun y => gradientFun (G.metric t) (u t) y) -
            fun y => gradientFun (G.metric t) (v t) y) x := by
            unfold divergence
            rw [hcov]
      _ = _ := divergence_sub (G.connection t) hug hvg
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_sub hut hvt, hlap]
  unfold driftTerm gradientAt
  rw [gradientFun_sub (G.metric t) hus.self_of_nhds hvs.self_of_nhds]
  simp only [map_sub]
  ring

private theorem exponential_cubic_parabolic
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (X : ℝ → (x : M) → TangentSpace I x) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (ε C : ℝ) (x : M) :
    parabolicOperatorWithDrift G T X
        (fun s y => ε * Real.exp (-C * s) * f y ^ 3) t x =
      ε * Real.exp (-C * t) *
        (-C * f x ^ 3 - heatOperatorWithDrift G t (X t) (fun y => f y ^ 3) x) := by
  have hd : HasDerivAt (fun s : ℝ => ε * Real.exp (-C * s) * f x ^ 3)
      (ε * (Real.exp (-C * t) * -C) * f x ^ 3) t := by
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id t).const_mul (-C)).exp).const_mul ε).mul_const (f x ^ 3)
  have hspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => f y ^ 3) := hf.pow 3
  unfold parabolicOperatorWithDrift
  rw [hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT) t ht)]
  have hh := heatOperatorWithDrift_const_smul (I := I) G t (X t)
    (ε * Real.exp (-C * t)) (f := fun y : M => f y ^ 3) (x := x)
    (fun y => hspace.mdifferentiable (by simp) y)
    (gradientFun_mdiffAt (G.metric t) hspace x)
  have hfun : ((ε * Real.exp (-C * t)) • fun y : M => f y ^ 3) =
      (fun y => ε * Real.exp (-C * t) * f y ^ 3) := rfl
  rw [hfun] at hh
  rw [hh]
  ring


theorem exponential_cubic_cutoff_subsolution
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (X : ℝ → (x : M) → TangentSpace I x) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε D ℓ ρ : ℝ} (c : ℝ)
    (hε : 0 ≤ ε) (hℓ : 0 < ℓ) (hρ : 0 < ρ) {x : M} (hx : 0 ≤ f x)
    (hL : -D ≤ heatOperatorWithDrift G t (X t) f x)
    (he : 4 * ℓ * (ρ ^ 2 - f x) ≤
      (G.metric t).inner x (gradientAt G t f x) (gradientAt G t f x)) :
    parabolicOperatorWithDrift G T X
        (fun s y => ε * Real.exp (-(localCubicBarrierRate D ℓ ρ + c) * s) * f y ^ 3) t x ≤
      -c * (ε * Real.exp (-(localCubicBarrierRate D ℓ ρ + c) * t) * f x ^ 3) := by
  have hbound := heatDrift_cubic_cutoff_lower_bound G t (X t) hf hℓ hρ hx hL he
  rw [exponential_cubic_parabolic G hT ht X hf ε (localCubicBarrierRate D ℓ ρ + c) x]
  calc
    _ ≤ ε * Real.exp (-(localCubicBarrierRate D ℓ ρ + c) * t) * (-c * f x ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hε (Real.exp_pos _).le)
    _ = _ := by ring


theorem exists_initial_cubic_barrier
    {f u : M → ℝ} (K : Set M) (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn f K) (hu : ContinuousOn u K)
    (hu_pos : ∀ x ∈ K, 0 < u x) (hu_out : ∀ x ∉ K, 0 ≤ u x)
    (hf_out : ∀ x ∉ K, f x ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * f x ^ 3 ≤ u x := by
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hu
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne (hf.pow 3)
  let B : ℝ := max (f q ^ 3) 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let ε : ℝ := u p / B
  have hε : 0 < ε := div_pos (hu_pos p hp) hB
  refine ⟨ε, hε, fun x => ?_⟩
  by_cases hx : x ∈ K
  · calc
      ε * f x ^ 3 ≤ ε * B :=
        mul_le_mul_of_nonneg_left ((hmax hx).trans (le_max_left _ _)) hε.le
      _ = u p := div_mul_cancel₀ _ (ne_of_gt hB)
      _ ≤ u x := hmin hx
  · have hcubic : f x ^ 3 ≤ 0 := by nlinarith [hf_out x hx, sq_nonneg (f x)]
    exact (mul_nonpos_of_nonneg_of_nonpos hε.le hcubic).trans (hu_out x hx)

private def upperSupport_sub_subsolution
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    {u v : ℝ → M → ℝ} {t : ℝ} {x : M}
    (U : ParabolicUpperSupportAt G T X u t x)
    (hvt : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hvs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hvg : MDiffAt (T% fun y : M => gradientFun (G.metric t) (v t) y) x)
    (hvP : parabolicOperatorWithDrift G T X v t x ≤ 0) :
    ParabolicUpperSupportAt G T X (fun s y => u s y - v s y) t x := by
  refine {
    upperSupport := fun s y => U.upperSupport s y - v s y
    eq_at := congrArg (fun r => r - v t x) U.eq_at
    upper_nhds := ?_
    time_diff := U.time_diff.sub hvt
    space_diff_nhds := ?_
    grad_diff := gradient_sub_mdiffAt (G.metric t) U.space_diff_nhds hvs U.grad_diff hvg
    operator_nonneg := ?_ }
  · filter_upwards [U.upper_nhds] with p hp
    exact sub_le_sub_right hp (v p.1 p.2)
  · filter_upwards [U.space_diff_nhds, hvs] with y huy hvy
    exact huy.sub hvy
  · rw [parabolic_sub_local G T X U.time_diff hvt U.space_diff_nhds hvs U.grad_diff hvg]
    exact sub_nonneg.mpr (hvP.trans U.operator_nonneg)


theorem local_cubic_barrier_lower_bound_before_terminal
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) {T ε D ℓ ρ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (K : Set M) (hK : IsCompact K) (hf_out : ∀ x ∉ K, f x ≤ 0)
    {u : ℝ → M → ℝ}
    (hu_cont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Ico 0 T ×ˢ K))
    (hu_nonneg : ∀ t ∈ Ico 0 T, ∀ x, 0 ≤ u t x)
    (hu0 : ∀ x, ε * f x ^ 3 ≤ u 0 x)
    (hsupport : ∀ S ∈ Ioo 0 T, ∀ t ∈ Ioc 0 S, ∀ x,
      Nonempty (ParabolicUpperSupportAt G S X u t x))
    (hL : ∀ t ∈ Ioo 0 T, ∀ x, 0 < f x →
      -D ≤ heatOperatorWithDrift G t (X t) f x)
    (he : ∀ t ∈ Ioo 0 T, ∀ x, 0 < f x →
      4 * ℓ * (ρ ^ 2 - f x) ≤
        (G.metric t).inner x (gradientAt G t f x) (gradientAt G t f x)) :
    ∀ t ∈ Ico 0 T, ∀ x,
      ε * Real.exp (-localCubicBarrierRate D ℓ ρ * t) * f x ^ 3 ≤ u t x := by
  classical
  let C := localCubicBarrierRate D ℓ ρ
  let v : ℝ → M → ℝ := fun t x => ε * Real.exp (-C * t) * f x ^ 3
  have hvcont : Continuous (fun p : ℝ × M => v p.1 p.2) := by
    dsimp [v]
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_fst))).mul ((hf.continuous.comp continuous_snd).pow 3)
  have hvspace (t : ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (v t) :=
    contMDiff_const.mul (hf.pow 3)
  have htrunc : ∀ S ∈ Ioo 0 T, ∀ t ∈ Icc 0 S, ∀ x, v t x ≤ u t x := by
    intro S hS
    have hsubset : Icc (0 : ℝ) S ×ˢ K ⊆ Ico 0 T ×ˢ K := by
      intro p hp
      exact ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 hS.2⟩, hp.2⟩
    have hcomparison := strict_barrier_compact_of_upperSupport G S X
      (fun t x => u t x - v t x) K hK
      (by
        intro t ht x hx
        have hu := hu_nonneg t ⟨ht.1, lt_of_le_of_lt ht.2 hS.2⟩ x
        have hv : v t x ≤ 0 := by
          dsimp [v]
          exact mul_nonpos_of_nonneg_of_nonpos
            (le_of_lt (mul_pos hε (Real.exp_pos _)))
            (by nlinarith [sq_nonneg (f x), hf_out x hx])
        exact sub_nonneg.mpr (hv.trans hu))
      ((hu_cont.mono hsubset).sub hvcont.continuousOn)
      (by intro x; simpa [v] using sub_nonneg.mpr (hu0 x))
      (by
        intro t ht htpos x hneg
        have htT : t ∈ Ioo 0 T := ⟨htpos, lt_of_le_of_lt ht.2 hS.2⟩
        have hfx : 0 < f x := by
          have hu := hu_nonneg t ⟨ht.1, htT.2⟩ x
          have hvpos : 0 < v t x := by linarith
          have hcube : 0 < f x ^ 3 :=
            (mul_pos_iff_of_pos_left (mul_pos hε (Real.exp_pos _))).mp hvpos
          nlinarith [sq_nonneg (f x)]
        have hvP : parabolicOperatorWithDrift G S X v t x ≤ 0 := by
          simpa only [add_zero, neg_zero, zero_mul] using
            exponential_cubic_cutoff_subsolution G hS.1 ht X hf 0 hε.le hℓ hρ
              (le_of_lt hfx) (hL t htT x hfx) (he t htT x hfx)
        exact upperSupport_sub_subsolution G S X
          (Classical.choice (hsupport S hS t ⟨htpos, ht.2⟩ x))
          (by dsimp [v]; fun_prop)
          (Filter.Eventually.of_forall fun y => (hvspace t).mdifferentiable (by simp) y)
          (gradientFun_mdiffAt (G.metric t) (hvspace t) x) hvP)
    intro t ht x
    exact sub_nonneg.mp (hcomparison t ht x)
  intro t ht x
  by_cases ht0 : t = 0
  · simpa [ht0] using hu0 x
  · exact htrunc t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩ t
      (right_mem_Icc.mpr ht.1) x


theorem local_cubic_barrier_positive_at_terminal
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) {T ε D ℓ ρ : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (K : Set M) (hK : IsCompact K) (hf_out : ∀ x ∉ K, f x ≤ 0)
    {u : ℝ → M → ℝ}
    (hu_cont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Ico 0 T ×ˢ K))
    (hu_nonneg : ∀ t ∈ Ico 0 T, ∀ x, 0 ≤ u t x)
    (hu0 : ∀ x, ε * f x ^ 3 ≤ u 0 x)
    (hsupport : ∀ S ∈ Ioo 0 T, ∀ t ∈ Ioc 0 S, ∀ x,
      Nonempty (ParabolicUpperSupportAt G S X u t x))
    (hL : ∀ t ∈ Ioo 0 T, ∀ x, 0 < f x →
      -D ≤ heatOperatorWithDrift G t (X t) f x)
    (he : ∀ t ∈ Ioo 0 T, ∀ x, 0 < f x →
      4 * ℓ * (ρ ^ 2 - f x) ≤
        (G.metric t).inner x (gradientAt G t f x) (gradientAt G t f x))
    {x : M} (hx : 0 < f x)
    (hu_terminal : ContinuousWithinAt (fun s => u s x) (Iio T) T) :
    ε * Real.exp (-localCubicBarrierRate D ℓ ρ * T) * f x ^ 3 ≤ u T x ∧
      0 < u T x := by
  have hbefore := local_cubic_barrier_lower_bound_before_terminal G X hε hℓ hρ
    hf K hK hf_out hu_cont hu_nonneg hu0 hsupport hL he
  have hbarrier : Continuous
      (fun t : ℝ => ε * Real.exp (-localCubicBarrierRate D ℓ ρ * t) * f x ^ 3) := by
    fun_prop
  have hbound : ε * Real.exp (-localCubicBarrierRate D ℓ ρ * T) * f x ^ 3 ≤ u T x := by
    apply le_of_tendsto_of_tendsto hbarrier.continuousAt.continuousWithinAt hu_terminal
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hT), self_mem_nhdsWithin] with t ht htT
    exact hbefore t ⟨le_of_lt ht, htT⟩ x
  exact ⟨hbound, lt_of_lt_of_le (by positivity) hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
