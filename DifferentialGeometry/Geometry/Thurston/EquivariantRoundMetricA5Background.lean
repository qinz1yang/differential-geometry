import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Tower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.CurvatureBlowupRate
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

/-!
# Derivative decay along the normalised surface flow: window estimates

Chapter 7, surface lemma U1, route (a), step a5.3 (lane U1E2), work file for the derivative
decay D of `R̂ - 2` and for the Bernstein step of a5.2 (iii) (design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`).

* `flow_heat_subsolution_window_le`: the weak maximum principle on a time window
  `[t₁, t₂] ⊂ (0, T)` of a Ricci flow on a closed manifold: if `∂ₜu ≤ Δ_{g(t)} u + K` on
  `(t₁, t₂)` and `u(t₁, ·) ≤ B`, then `u(t₂, ·) ≤ B + K (t₂ - t₁)`. It is the comparison principle
  `scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot` applied to
  `u - K (t - t₁)`, after the time shift `isHeatPotSubsolutionOn_timeShift_flowG`.
* `flow_linear_tower_decay`: the window step for a linear derivative tower (review 18 §2). If
  nonnegative jointly smooth `u q` satisfy
  `∂ₜ u_q ≤ Δ u_q + (-2 u_{q+1} + C_q Σ_{j ≤ q} u_j) / (2 (T* - t))` on `(t₀, T)` (`T ≤ T*`) and
  `u_0 ≤ K (T* - t)^c` on `[t₀, T)`, then every `u_q ≤ K_q (T* - t)^c` there, with the same
  exponent `c`. Away from `T*` (`t ≤ (T* + t₀)/2`) an exponentially weighted Gronwall bound from
  the data at `t₀`; near `T*` the window `[t₁, t]` with `T* - t₁ = 2 (T* - t)` and
  `F = (s - t₁)/(2 (T* - t)) u_{q+1} + (1 + C) u_q`. In normalised time these are windows of fixed
  length.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
private theorem contMDiff_slice_of_joint {u : ℝ → M → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (U ×ˢ univ))
    {t : ℝ} (ht : t ∈ U) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := by
  intro x
  have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (t, x) :=
    hu.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  exact hat.comp x hpair

omit [T2Space M] in
theorem flow_heat_subsolution_window_le
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t₁ t₂ K B : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (ht₂ : t₂ < T)
    (hevol : ∀ t ∈ Ioo t₁ t₂, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => u s x) d t ∧
      d ≤ laplacianAt (flowG S) t (u t) x + K)
    (hinit : ∀ y, u t₁ y ≤ B) :
    ∀ x, u t₂ x ≤ B + K * (t₂ - t₁) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hslice : ∀ t ∈ Ioo 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := fun t ht =>
    contMDiff_slice_of_joint isOpen_Ioo hu ht
  have hIcc : ∀ s ∈ Icc t₁ t₂, s ∈ Ioo 0 T := fun s hs =>
    ⟨ht₁.trans_le hs.1, hs.2.trans_lt ht₂⟩
  let w : ℝ → M → ℝ := fun s y => u s y - K * (s - t₁)
  have hlin : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => K * (q.1 - t₁)) :=
    contMDiff_const.mul (contMDiff_fst.sub contMDiff_const)
  have hsub : IsHeatPotSubsolutionOn (RealTimeInterval.closed t₁ t₂ h12) (flowG S)
      (fun _ _ => 0) w :=
    { jointSmooth := (hu.mono (prod_mono (fun s hs =>
          (⟨ht₁.trans hs.1, hs.2.trans ht₂⟩ : s ∈ Ioo 0 T)) le_rfl)).sub hlin.contMDiffOn
      jointCont := (hu.continuousOn.mono (prod_mono (fun s hs => hIcc s hs) le_rfl)).sub
          hlin.continuous.continuousOn
      sliceSmooth := fun s hs => (hslice s (hIcc s hs)).sub contMDiff_const
      timeDiff := fun s hs y => by
        obtain ⟨d, hd, -⟩ := hevol s hs y
        exact hd.differentiableAt.sub
          ((differentiableAt_id.sub_const t₁).const_mul K)
      equation_le := fun s hs y => by
        obtain ⟨d, hd, hle⟩ := hevol s hs y
        have hw : HasDerivAt (fun r => w r y) (d - K) s := by
          have h2 : HasDerivAt (fun r : ℝ => K * (r - t₁)) K s := by
            simpa using ((hasDerivAt_id s).sub_const t₁).const_mul K
          exact hd.sub h2
        rw [hw.deriv]
        have hlap : laplacianAt (flowG S) s (w s) y = laplacianAt (flowG S) s (u s) y := by
          unfold laplacianAt
          exact laplacian_sub_const _ _ (K * (s - t₁))
            (fun z => ((hslice s ⟨ht₁.trans hs.1, hs.2.trans ht₂⟩).mdifferentiableAt
              (by simp))) y
        rw [hlap]
        linarith }
  have hT' : (0 : ℝ) ≤ t₂ - t₁ := sub_nonneg.mpr h12
  have hsh := isHeatPotSubsolutionOn_timeShift_flowG
    (Dsub' := RealTimeInterval.closed 0 (t₂ - t₁) hT') S (fun _ _ => 0) w t₁ hsub
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + t₁ ∈ Icc t₁ t₂))
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + t₁ ∈ Ioo t₁ t₂))
  have hcmp := scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot
    (flowG (S.timeShift t₁)) (t₂ - t₁) hT' (fun s y => w (s + t₁) y) (fun _ => B)
    (fun _ _ => 0) 0 (fun _ _ => 0) hsh continuousOn_const
    (fun _ _ _ => differentiableWithinAt_const B)
    (fun _ _ _ => by simp)
    (fun s hs hs0 => by simp)
    (fun y => by
      change u (0 + t₁) y - K * (0 + t₁ - t₁) ≤ B
      rw [zero_add, sub_self, mul_zero, sub_zero]
      exact hinit y)
    (fun _ _ => LipschitzWith.lipschitzOnWith (LipschitzWith.const 0))
  intro x
  have h := hcmp (t₂ - t₁) ⟨hT', le_rfl⟩ x
  change u (t₂ - t₁ + t₁) x - K * (t₂ - t₁ + t₁ - t₁) ≤ B at h
  rw [sub_add_cancel] at h
  linarith

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem laplacianAt_lincomb
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (t : ℝ)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (a b : ℝ)
    (x : M) :
    laplacianAt (flowG S) t (fun y => a * f y + b * h y) x =
      a * laplacianAt (flowG S) t f x + b * laplacianAt (flowG S) t h x := by
  have haf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => a * f y) := contMDiff_const.mul hf
  have hbh : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => b * h y) := contMDiff_const.mul hh
  rw [laplacianAt_add _ _ (fun y => (haf y).mdifferentiableAt (by simp))
    (fun y => (hbh y).mdifferentiableAt (by simp)) (gradientFun_mdiffAt _ haf x)
    (gradientFun_mdiffAt _ hbh x)]
  have h1 := laplacianAt_smul (flowG S) t a (fun y => (hf y).mdifferentiableAt (by simp))
    (gradientFun_mdiffAt _ hf x)
  have h2 := laplacianAt_smul (flowG S) t b (fun y => (hh y).mdifferentiableAt (by simp))
    (gradientFun_mdiffAt _ hh x)
  exact congrArg₂ (· + ·) h1 h2

private theorem window_arith {u₁ u₂ S₀ d₁ d₀ Δ₁ Δ₀ θ A Cp C₁ C₀ w w₂ Q' : ℝ}
    (hle₁ : d₁ ≤ Δ₁ + (-2 * u₂ + C₁ * (S₀ + u₁)) * w)
    (hle₀ : d₀ ≤ Δ₀ + (-2 * u₁ + C₀ * S₀) * w)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (hA : A = 1 + Cp) (hCp0 : 0 ≤ Cp) (hC1 : C₁ ≤ Cp)
    (hC0 : C₀ ≤ Cp) (hu1 : 0 ≤ u₁) (hu2 : 0 ≤ u₂) (hS0 : 0 ≤ S₀) (hw0 : 0 ≤ w)
    (hw₂w : w₂ ≤ 2 * w) (hfin : (Cp / 2 + A * Cp) * S₀ * w ≤ Q') :
    w₂ * u₁ + θ * d₁ + A * d₀ ≤ θ * Δ₁ + A * Δ₀ + Q' := by
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hX : 0 ≤ S₀ + u₁ := add_nonneg hS0 hu1
  have i1 := mul_le_mul_of_nonneg_left hle₁ hθ0
  have i2 := mul_le_mul_of_nonneg_left hle₀ hA0
  have a1 : -2 * u₂ + C₁ * (S₀ + u₁) ≤ Cp * (S₀ + u₁) := by
    have := mul_le_mul_of_nonneg_right hC1 hX
    linarith
  have a2 := mul_le_mul_of_nonneg_left a1 hθ0
  have a3 : θ * (Cp * (S₀ + u₁)) ≤ 1 / 2 * (Cp * (S₀ + u₁)) :=
    mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hCp0 hX)
  have j1 := mul_le_mul_of_nonneg_right (a2.trans a3) hw0
  have b1 : -2 * u₁ + C₀ * S₀ ≤ -2 * u₁ + Cp * S₀ := by
    have := mul_le_mul_of_nonneg_right hC0 hS0
    linarith
  have j2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right b1 hw0) hA0
  have j3 : w₂ * u₁ ≤ 2 * w * u₁ := mul_le_mul_of_nonneg_right hw₂w hu1
  have j4 : 0 ≤ Cp * u₁ * w := mul_nonneg (mul_nonneg hCp0 hu1) hw0
  subst hA
  linarith

omit [T2Space M] in
private theorem tower_first_region [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {Tst c : ℝ}
    (hTT : T ≤ Tst) (hc : 0 ≤ c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (u : ℕ → ℝ → M → ℝ)
    (hu : ∀ q, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u q p.1 p.2)
      (Ioo 0 T ×ˢ univ))
    (hnonneg : ∀ q, ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ u q t x) (C : ℕ → ℝ)
    (htower : ∀ q, ∀ t ∈ Ioo t₀ T, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => u q s x) d t ∧
      d ≤ laplacianAt (flowG S) t (u q t) x +
        (-2 * u (q + 1) t x + C q * ∑ j ∈ Finset.range (q + 1), u j t x) / (2 * (Tst - t)))
    (q : ℕ) {Kq : ℝ} (hKq0 : 0 ≤ Kq)
    (hKq : ∀ j ≤ q, ∀ t ∈ Ico t₀ T, ∀ x, u j t x ≤ Kq * (Tst - t) ^ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ico t₀ T, t ≤ (Tst + t₀) / 2 → ∀ x,
      u (q + 1) t x ≤ K * (Tst - t) ^ c := by
  have hslice : ∀ q, ∀ t ∈ Ioo 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u q t) := fun q t ht =>
    contMDiff_slice_of_joint isOpen_Ioo (hu q) ht
  have hTst : 0 < Tst := by linarith [ht₀.1, ht₀.2]
  obtain ⟨Cp, hCp0, hC1, hC0⟩ : ∃ Cp : ℝ, 0 ≤ Cp ∧ C (q + 1) ≤ Cp ∧ C q ≤ Cp :=
    ⟨max (max (C (q + 1)) (C q)) 0, le_max_right _ _, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  have hq1 : (0 : ℝ) ≤ q + 1 := by positivity
  have hsum : ∀ t ∈ Ico t₀ T, ∀ x, ∑ j ∈ Finset.range (q + 1), u j t x ≤
      (q + 1) * (Kq * (Tst - t) ^ c) := by
    intro t ht x
    calc ∑ j ∈ Finset.range (q + 1), u j t x
        ≤ ∑ _j ∈ Finset.range (q + 1), Kq * (Tst - t) ^ c :=
          Finset.sum_le_sum fun j hj =>
            hKq j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) t ht x
      _ = (q + 1) * (Kq * (Tst - t) ^ c) := by simp
  have hsum0 : ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ ∑ j ∈ Finset.range (q + 1), u j t x :=
    fun t ht x => Finset.sum_nonneg fun j _ => hnonneg j t ht x
  obtain ⟨τm, hτm⟩ : ∃ τm : ℝ, τm = (Tst - t₀) / 2 := ⟨_, rfl⟩
  have hτm0 : 0 < τm := by rw [hτm]; linarith [ht₀.2]
  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (hslice (q + 1) t₀ ht₀).continuous.continuousOn
  obtain ⟨B₀, hB₀0, hB₀⟩ : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ y, u (q + 1) t₀ y ≤ B₀ :=
    ⟨max (u (q + 1) t₀ xm) 0, le_max_right _ _,
      fun y => (hxm (mem_univ y)).trans (le_max_left _ _)⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Cp / (2 * τm) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hTc : 0 ≤ Tst ^ c := Real.rpow_nonneg hTst.le _
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = Cp * ((q + 1) * (Kq * Tst ^ c)) / (2 * τm) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hτmc : 0 < τm ^ c := Real.rpow_pos_of_pos hτm0 _
  refine ⟨Real.exp (L * Tst) * (B₀ + K₂ * Tst) / τm ^ c, by positivity, fun t ht hreg x => ?_⟩
  have htpos : 0 < Tst - t := by linarith [ht.2]
  let e : ℝ → ℝ := fun r => Real.exp (-(L * (r - t₀)))
  have he : ContDiff ℝ ∞ e := by fun_prop
  let v : ℝ → M → ℝ := fun r y => e r * u (q + 1) r y
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => v p.1 p.2)
      (Ioo 0 T ×ˢ univ) :=
    (he.contMDiff.comp contMDiff_fst).contMDiffOn.mul (hu (q + 1))
  have hwin := flow_heat_subsolution_window_le S v hv (K := K₂) (B := B₀) ht₀.1 ht.1
    ht.2 (fun s hs y => ?_) (fun y => ?_)
  · have hvt := hwin x
    have het : e t * Real.exp (L * (t - t₀)) = 1 := by
      simp only [e]
      rw [← Real.exp_add]
      simp
    have hu1 : u (q + 1) t x = Real.exp (L * (t - t₀)) * v t x := by
      simp only [v]
      rw [← mul_assoc, mul_comm (Real.exp _) (e t), het, one_mul]
    have hexp : Real.exp (L * (t - t₀)) ≤ Real.exp (L * Tst) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht₀.1]) hL0)
    have hvt' : v t x ≤ B₀ + K₂ * Tst := by
      have : K₂ * (t - t₀) ≤ K₂ * Tst :=
        mul_le_mul_of_nonneg_left (by linarith [ht₀.1, ht.2]) hK₂0
      linarith
    have hτge : τm ≤ Tst - t := by rw [hτm]; linarith
    have hpowge : τm ^ c ≤ (Tst - t) ^ c := Real.rpow_le_rpow hτm0.le hτge hc
    have hvnn : 0 ≤ v t x :=
      mul_nonneg (Real.exp_pos _).le (hnonneg _ t ⟨ht₀.1.trans_le ht.1, ht.2⟩ x)
    have hKnn : 0 ≤ Real.exp (L * Tst) * (B₀ + K₂ * Tst) / τm ^ c := by positivity
    calc u (q + 1) t x = Real.exp (L * (t - t₀)) * v t x := hu1
      _ ≤ Real.exp (L * Tst) * (B₀ + K₂ * Tst) :=
          mul_le_mul hexp hvt' hvnn (Real.exp_pos _).le
      _ = Real.exp (L * Tst) * (B₀ + K₂ * Tst) / τm ^ c * τm ^ c := by field_simp
      _ ≤ Real.exp (L * Tst) * (B₀ + K₂ * Tst) / τm ^ c * (Tst - t) ^ c :=
          mul_le_mul_of_nonneg_left hpowge hKnn
  · have hsT : s ∈ Ioo t₀ T := ⟨hs.1, hs.2.trans ht.2⟩
    have hs0 : s ∈ Ioo 0 T := ⟨ht₀.1.trans hsT.1, hsT.2⟩
    obtain ⟨d, hd, hle⟩ := htower (q + 1) s hsT y
    have hde : HasDerivAt e (e s * -(L * 1)) s := by
      simpa [e] using (((hasDerivAt_id s).sub_const t₀).const_mul L).neg.exp
    refine ⟨e s * -(L * 1) * u (q + 1) s y + e s * d, hde.mul hd, ?_⟩
    have hlap : laplacianAt (flowG S) s (v s) y =
        e s * laplacianAt (flowG S) s (u (q + 1) s) y :=
      laplacianAt_smul (flowG S) s (e s)
        (fun z => (hslice (q + 1) s hs0 z).mdifferentiableAt (by simp))
        (gradientFun_mdiffAt _ (hslice (q + 1) s hs0) y)
    rw [hlap]
    have hτs : τm ≤ Tst - s := by rw [hτm]; linarith [hs.2]
    have hτs0 : 0 < Tst - s := by linarith
    have he0 : 0 < e s := Real.exp_pos _
    have he1 : e s ≤ 1 := by
      simp only [e]
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hL0 (by linarith [hs.1])
    have hu1 := hnonneg (q + 1) s hs0 y
    have hu2 := hnonneg (q + 1 + 1) s hs0 y
    have hS0 := hsum0 s hs0 y
    have hSb := hsum s ⟨hsT.1.le, hsT.2⟩ y
    rw [Finset.sum_range_succ] at hle
    have hpows : (Tst - s) ^ c ≤ Tst ^ c :=
      Real.rpow_le_rpow hτs0.le (by linarith [hs0.1]) hc
    have hnum : -2 * u (q + 1 + 1) s y +
        C (q + 1) * (∑ j ∈ Finset.range (q + 1), u j s y + u (q + 1) s y) ≤
        Cp * (∑ j ∈ Finset.range (q + 1), u j s y + u (q + 1) s y) := by
      have := mul_le_mul_of_nonneg_right hC1 (add_nonneg hS0 hu1)
      linarith
    have hdiv := (div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ 2 * (Tst - s))).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by linarith : 2 * τm ≤ 2 * (Tst - s)))
    have hsplit : Cp * (∑ j ∈ Finset.range (q + 1), u j s y + u (q + 1) s y) / (2 * τm) =
        Cp * (∑ j ∈ Finset.range (q + 1), u j s y) / (2 * τm) + L * u (q + 1) s y := by
      rw [hL]
      ring
    have hS₀b : Cp * (∑ j ∈ Finset.range (q + 1), u j s y) / (2 * τm) ≤ K₂ := by
      rw [hK₂]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hCp0
      exact hSb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpows hKq0) hq1)
    have hbr : d - L * u (q + 1) s y ≤ laplacianAt (flowG S) s (u (q + 1) s) y + K₂ := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbr he0.le
    have hK₂e : e s * K₂ ≤ K₂ := by
      have := mul_le_mul_of_nonneg_right he1 hK₂0
      linarith
    rw [mul_sub, mul_add] at hmul
    linarith
  · change e t₀ * u (q + 1) t₀ y ≤ B₀
    have : e t₀ = 1 := by simp [e]
    rw [this, one_mul]
    exact hB₀ y

omit [T2Space M] in
private theorem tower_second_region [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {Tst c : ℝ}
    (hTT : T ≤ Tst) (hc : 0 ≤ c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (u : ℕ → ℝ → M → ℝ)
    (hu : ∀ q, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u q p.1 p.2)
      (Ioo 0 T ×ˢ univ))
    (hnonneg : ∀ q, ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ u q t x) (C : ℕ → ℝ)
    (htower : ∀ q, ∀ t ∈ Ioo t₀ T, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => u q s x) d t ∧
      d ≤ laplacianAt (flowG S) t (u q t) x +
        (-2 * u (q + 1) t x + C q * ∑ j ∈ Finset.range (q + 1), u j t x) / (2 * (Tst - t)))
    (q : ℕ) {Kq : ℝ} (hKq0 : 0 ≤ Kq)
    (hKq : ∀ j ≤ q, ∀ t ∈ Ico t₀ T, ∀ x, u j t x ≤ Kq * (Tst - t) ^ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ico t₀ T, (Tst + t₀) / 2 < t → ∀ x,
      u (q + 1) t x ≤ K * (Tst - t) ^ c := by
  have hslice : ∀ q, ∀ t ∈ Ioo 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u q t) := fun q t ht =>
    contMDiff_slice_of_joint isOpen_Ioo (hu q) ht
  have hTst : 0 < Tst := by linarith [ht₀.1, ht₀.2]
  obtain ⟨Cp, hCp0, hC1, hC0⟩ : ∃ Cp : ℝ, 0 ≤ Cp ∧ C (q + 1) ≤ Cp ∧ C q ≤ Cp :=
    ⟨max (max (C (q + 1)) (C q)) 0, le_max_right _ _, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  have hq1 : (0 : ℝ) ≤ q + 1 := by positivity
  have hsum : ∀ t ∈ Ico t₀ T, ∀ x, ∑ j ∈ Finset.range (q + 1), u j t x ≤
      (q + 1) * (Kq * (Tst - t) ^ c) := by
    intro t ht x
    calc ∑ j ∈ Finset.range (q + 1), u j t x
        ≤ ∑ _j ∈ Finset.range (q + 1), Kq * (Tst - t) ^ c :=
          Finset.sum_le_sum fun j hj =>
            hKq j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) t ht x
      _ = (q + 1) * (Kq * (Tst - t) ^ c) := by simp
  have hsum0 : ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ ∑ j ∈ Finset.range (q + 1), u j t x :=
    fun t ht x => Finset.sum_nonneg fun j _ => hnonneg j t ht x
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + Cp := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (Cp / 2 + A * Cp) * ((q + 1) * Kq) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have h2c : 0 < (2 : ℝ) ^ c := Real.rpow_pos_of_pos two_pos _
  refine ⟨2 * (A * Kq + Q / 2) * 2 ^ c, by positivity, fun t ht hreg x => ?_⟩
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ₂ : ℝ, τ₂ = Tst - t := ⟨_, rfl⟩
  have hτ₂0 : 0 < τ₂ := by rw [hτ₂]; linarith [ht.2]
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = Tst - 2 * τ₂ := ⟨_, rfl⟩
  have ht₀₁ : t₀ < t₁ := by rw [ht₁, hτ₂]; linarith
  have ht₁t : t₁ < t := by rw [ht₁, hτ₂]; linarith
  have ht₁T : t₁ ∈ Ico t₀ T := ⟨ht₀₁.le, ht₁t.trans ht.2⟩
  have hc2 : (2 * τ₂) ^ c = 2 ^ c * τ₂ ^ c := Real.mul_rpow (by norm_num) hτ₂0.le
  have h2τc : 0 ≤ (2 * τ₂) ^ c := Real.rpow_nonneg (by positivity) _
  let F : ℝ → M → ℝ := fun r y => (r - t₁) * (2 * τ₂)⁻¹ * u (q + 1) r y + A * u q r y
  have hθs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (p.1 - t₁) * (2 * τ₂)⁻¹) :=
    (contMDiff_fst.sub contMDiff_const).mul contMDiff_const
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2)
      (Ioo 0 T ×ˢ univ) :=
    (hθs.contMDiffOn.mul (hu (q + 1))).add (contMDiffOn_const.mul (hu q))
  have hwin := flow_heat_subsolution_window_le S F hF (K := Q * (2 * τ₂) ^ c * (2 * τ₂)⁻¹)
    (B := A * (Kq * (2 * τ₂) ^ c)) (ht₀.1.trans ht₀₁) ht₁t.le ht.2 (fun s hs y => ?_)
    (fun y => ?_)
  · have hFt := hwin x
    have htt : t - t₁ = τ₂ := by rw [ht₁, hτ₂]; ring
    have hτne : τ₂ ≠ 0 := hτ₂0.ne'
    have hθt : (t - t₁) * (2 * τ₂)⁻¹ = 1 / 2 := by
      rw [htt]
      field_simp
    have hFx : F t x = 1 / 2 * u (q + 1) t x + A * u q t x := by
      simp only [F, hθt]
    have hu0 := hnonneg q t ⟨ht₀.1.trans_le ht.1, ht.2⟩ x
    have hAu : 0 ≤ A * u q t x := mul_nonneg hA0 hu0
    rw [hFx, htt] at hFt
    have hK : Q * (2 * τ₂) ^ c * (2 * τ₂)⁻¹ * τ₂ = Q / 2 * (2 * τ₂) ^ c := by
      field_simp
    rw [hK] at hFt
    rw [← hτ₂]
    calc u (q + 1) t x ≤ 2 * (A * (Kq * (2 * τ₂) ^ c) + Q / 2 * (2 * τ₂) ^ c) := by linarith
      _ = 2 * (A * Kq + Q / 2) * 2 ^ c * τ₂ ^ c := by rw [hc2]; ring
  · have hsT : s ∈ Ioo t₀ T := ⟨ht₀₁.trans hs.1, hs.2.trans ht.2⟩
    have hs0 : s ∈ Ioo 0 T := ⟨ht₀.1.trans hsT.1, hsT.2⟩
    obtain ⟨d₁, hd₁, hle₁⟩ := htower (q + 1) s hsT y
    obtain ⟨d₀, hd₀, hle₀⟩ := htower q s hsT y
    have hθd : HasDerivAt (fun r : ℝ => (r - t₁) * (2 * τ₂)⁻¹) (1 * (2 * τ₂)⁻¹) s :=
      ((hasDerivAt_id s).sub_const t₁).mul_const _
    refine ⟨1 * (2 * τ₂)⁻¹ * u (q + 1) s y + (s - t₁) * (2 * τ₂)⁻¹ * d₁ + A * d₀,
      (hθd.mul hd₁).add (hd₀.const_mul A), ?_⟩
    have hlap : laplacianAt (flowG S) s (F s) y =
        (s - t₁) * (2 * τ₂)⁻¹ * laplacianAt (flowG S) s (u (q + 1) s) y +
          A * laplacianAt (flowG S) s (u q s) y :=
      laplacianAt_lincomb S s (hslice (q + 1) s hs0) (hslice q s hs0) _ A y
    rw [hlap]
    have hst : s - t₁ ≤ τ₂ := by rw [ht₁, hτ₂]; linarith [hs.2]
    have hτne : τ₂ ≠ 0 := hτ₂0.ne'
    have hθ0 : 0 ≤ (s - t₁) * (2 * τ₂)⁻¹ := mul_nonneg (by linarith [hs.1]) (by positivity)
    have hθ1 : (s - t₁) * (2 * τ₂)⁻¹ ≤ 1 / 2 := by
      calc (s - t₁) * (2 * τ₂)⁻¹ ≤ τ₂ * (2 * τ₂)⁻¹ :=
            mul_le_mul_of_nonneg_right hst (by positivity)
        _ = 1 / 2 := by field_simp
    have hτs : τ₂ ≤ Tst - s := by rw [hτ₂]; linarith [hs.2]
    have hτs2 : Tst - s ≤ 2 * τ₂ := by rw [ht₁] at hs; linarith [hs.1]
    have hτs0 : 0 < Tst - s := by linarith
    have hw0 : 0 ≤ (2 * (Tst - s))⁻¹ := by positivity
    have hww₂ : (2 * (Tst - s))⁻¹ ≤ (2 * τ₂)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have hw₂w : 1 * (2 * τ₂)⁻¹ ≤ 2 * (2 * (Tst - s))⁻¹ := by
      have h2w : 2 * (2 * (Tst - s))⁻¹ = (Tst - s)⁻¹ := by field_simp
      rw [h2w, one_mul]
      exact inv_anti₀ hτs0 (by linarith)
    rw [div_eq_mul_inv] at hle₁ hle₀
    rw [Finset.sum_range_succ] at hle₁
    have hu1 := hnonneg (q + 1) s hs0 y
    have hu2 := hnonneg (q + 1 + 1) s hs0 y
    have hS0 := hsum0 s hs0 y
    have hSb : ∑ j ∈ Finset.range (q + 1), u j s y ≤ (q + 1) * (Kq * (2 * τ₂) ^ c) :=
      (hsum s ⟨hsT.1.le, hsT.2⟩ y).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hτs0.le hτs2 hc) hKq0) hq1)
    have hcoef : 0 ≤ Cp / 2 + A * Cp := by positivity
    have hfin : (Cp / 2 + A * Cp) * (∑ j ∈ Finset.range (q + 1), u j s y) *
        (2 * (Tst - s))⁻¹ ≤ Q * (2 * τ₂) ^ c * (2 * τ₂)⁻¹ := by
      rw [hQ]
      calc (Cp / 2 + A * Cp) * (∑ j ∈ Finset.range (q + 1), u j s y) * (2 * (Tst - s))⁻¹
          ≤ (Cp / 2 + A * Cp) * ((q + 1) * (Kq * (2 * τ₂) ^ c)) * (2 * (Tst - s))⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSb hcoef) hw0
        _ ≤ (Cp / 2 + A * Cp) * ((q + 1) * (Kq * (2 * τ₂) ^ c)) * (2 * τ₂)⁻¹ :=
            mul_le_mul_of_nonneg_left hww₂ (by positivity)
        _ = (Cp / 2 + A * Cp) * ((q + 1) * Kq) * (2 * τ₂) ^ c * (2 * τ₂)⁻¹ := by ring
    exact window_arith hle₁ hle₀ hθ0 hθ1 hA hCp0 hC1 hC0 hu1 hu2 hS0 hw0 hw₂w hfin
  · change (t₁ - t₁) * (2 * τ₂)⁻¹ * u (q + 1) t₁ y + A * u q t₁ y ≤ A * (Kq * (2 * τ₂) ^ c)
    rw [sub_self, zero_mul, zero_mul, zero_add]
    have h := hKq q le_rfl t₁ ht₁T y
    have h2 : Tst - t₁ = 2 * τ₂ := by rw [ht₁]; ring
    rw [h2] at h
    exact mul_le_mul_of_nonneg_left h hA0

omit [T2Space M] in
theorem flow_linear_tower_decay [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {Tst c : ℝ}
    (hTT : T ≤ Tst) (hc : 0 ≤ c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (u : ℕ → ℝ → M → ℝ)
    (hu : ∀ q, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u q p.1 p.2)
      (Ioo 0 T ×ˢ univ))
    (hnonneg : ∀ q, ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ u q t x) (C : ℕ → ℝ)
    (htower : ∀ q, ∀ t ∈ Ioo t₀ T, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => u q s x) d t ∧
      d ≤ laplacianAt (flowG S) t (u q t) x +
        (-2 * u (q + 1) t x + C q * ∑ j ∈ Finset.range (q + 1), u j t x) / (2 * (Tst - t)))
    (h0 : ∃ K : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, u 0 t x ≤ K * (Tst - t) ^ c) :
    ∀ q, ∃ K : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, u q t x ≤ K * (Tst - t) ^ c := by
  have hslice : ∀ q, ∀ t ∈ Ioo 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u q t) := fun q t ht =>
    contMDiff_slice_of_joint isOpen_Ioo (hu q) ht
  have hmemT : ∀ t ∈ Ico t₀ T, t ∈ Ioo 0 T := fun t ht => ⟨ht₀.1.trans_le ht.1, ht.2⟩
  have hτpos : ∀ t ∈ Ico t₀ T, 0 < Tst - t := fun t ht => by linarith [ht.2]
  have hTst : 0 < Tst := by linarith [ht₀.1, ht₀.2]
  suffices hall : ∀ q, ∃ K : ℝ, 0 ≤ K ∧
      ∀ j ≤ q, ∀ t ∈ Ico t₀ T, ∀ x, u j t x ≤ K * (Tst - t) ^ c by
    intro q
    obtain ⟨K, -, hK⟩ := hall q
    exact ⟨K, hK q le_rfl⟩
  intro q
  induction q with
  | zero =>
    obtain ⟨K, hK⟩ := h0
    refine ⟨max K 0, le_max_right _ _, fun j hj t ht x => ?_⟩
    rw [Nat.le_zero.mp hj]
    exact (hK t ht x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (hτpos t ht).le _))
  | succ q ih =>
    obtain ⟨Kq, hKq0, hKq⟩ := ih
    obtain ⟨K', hK'0, hK'⟩ : ∃ K' : ℝ, 0 ≤ K' ∧
        ∀ t ∈ Ico t₀ T, ∀ x, u (q + 1) t x ≤ K' * (Tst - t) ^ c := by
      obtain ⟨K₁, hK₁0, hK₁⟩ := tower_first_region S hTT hc ht₀ u hu hnonneg C htower q hKq0 hKq
      obtain ⟨K₂, hK₂0, hK₂⟩ := tower_second_region S hTT hc ht₀ u hu hnonneg C htower q hKq0 hKq
      refine ⟨max K₁ K₂, le_max_of_le_left hK₁0, fun t ht x => ?_⟩
      have hpow : 0 ≤ (Tst - t) ^ c := Real.rpow_nonneg (hτpos t ht).le _
      by_cases hreg : t ≤ (Tst + t₀) / 2
      · exact (hK₁ t ht hreg x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
      · exact (hK₂ t ht (not_le.mp hreg) x).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
    refine ⟨max Kq K', le_max_of_le_left hKq0, fun j hj t ht x => ?_⟩
    have hpow : 0 ≤ (Tst - t) ^ c := Real.rpow_nonneg (hτpos t ht).le _
    rcases Nat.lt_or_ge j (q + 1) with hlt | hge
    · exact (hKq j (Nat.lt_succ_iff.mp hlt) t ht x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · rw [le_antisymm hj hge]
      exact (hK' t ht x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

end GC.Geometry
