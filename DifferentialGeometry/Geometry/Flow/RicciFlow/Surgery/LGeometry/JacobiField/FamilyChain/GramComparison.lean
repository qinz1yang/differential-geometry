import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.JacobiField.FamilyChain.IndexTrace

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u

private theorem ricciAt_congr_point {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (t : ℝ) {p q : X} (h : p = q)
    (a b : TangentSpace ThreeModel p) (a' b' : TangentSpace ThreeModel q)
    (ha : (a : ThreeSpace) = a') (hb : (b : ThreeSpace) = b') :
    S.ricciAt t p (vec2 a b) = S.ricciAt t q (vec2 a' b') := by
  subst h
  rw [show a = a' from ha, show b = b' from hb]

private theorem inner_smul_left_real {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) (x : N) (c : ℝ)
    (a b : TangentSpace ThreeModel x) : g.inner x (c • a) b = c * g.inner x a b := by
  rw [map_smul]
  rfl

private theorem inner_smul_right_real {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) (x : N) (c : ℝ)
    (a b : TangentSpace ThreeModel x) : g.inner x a (c • b) = c * g.inner x a b := by
  rw [map_smul]
  rfl

private theorem lGramDeriv_eq_of_eq {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (T : ℝ) {ι : Type*} (γ : ℝ → X)
    (Y : ι → ∀ q, TangentSpace ThreeModel (γ q)) (τ c : ℝ)
    (C : ι → TangentSpace ThreeModel (γ τ))
    (hC : ∀ i, covDerivAlong (I := ThreeModel) (S.base.metric (T - τ)) γ (Y i) τ = c • C i) :
    lGramDeriv S T γ Y τ = c • ((Matrix.of fun i j => (S.base.metric (T - τ)).inner (γ τ) (C i)
        (Y j τ)) + (Matrix.of fun i j => (S.base.metric (T - τ)).inner (γ τ) (C i)
        (Y j τ)).transpose) +
      (2 : ℝ) • Matrix.of fun i j => S.ricciAt (T - τ) (γ τ) (vec2 (Y i τ) (Y j τ)) := by
  ext i j
  simp only [lGramDeriv, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  rw [hC i, hC j, inner_smul_left_real, (S.base.metric (T - τ)).symm (γ τ) (Y i τ) (c • C j),
    inner_smul_left_real]
  ring

variable {H : ObservedHistory.{u}} {first last fst : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {hfst : first ≤ fst} {T w v : ℝ} {p : (H.stage last).Carrier}
  {Z₀ : H.historyLExpDomain hle T w p}

namespace LFamilyChain

variable {ch : H.LFamilyChain hle hfst T w v p Z₀}
  {P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field}

private theorem isHistoryLJacobi_jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) :
    ch.toLWindowChain.IsHistoryLJacobi (ch.jacobiField i) := by
  refine ⟨fun k hk s hs => ?_, ch.isGlued_jacobiField i, ch.isGlued_covDerivField_jacobiField i⟩
  obtain ⟨a, b, ha, hb, hJ⟩ := ch.isLRegularizedJacobi_jacobiField i hk
  rw [uIcc_of_le (ch.lt k hk).le] at hs
  exact hJ s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩

private theorem isGlued_scaled (hP : ch.IsAdaptedFrame P) (l : Fin (Module.finrank ℝ ThreeSpace))
    (b : ℝ) : ch.toLWindowChain.IsGlued (fun k s => (s / b) • P l k s) := by
  intro k hk
  have h := hP.2.1 l k hk
  change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)))
      (ch.γ k (ch.c (k + 1))) ((ch.c (k + 1) / b) • P l k (ch.c (k + 1))) : ThreeSpace) =
    mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1)))
      ((ch.c (k + 1) / b) • P l (k + 1) (ch.c (k + 1)))
  rw [map_smul, map_smul]
  exact congrArg _ h

private theorem contMDiff_of_mem_span {G : Set ch.toLWindowChain.Field}
    (hG : ∀ Y ∈ G, ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t) (Y k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    {Y : ch.toLWindowChain.Field} (hY : Y ∈ Submodule.span ℝ G) :
    ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t) (Y k t) :
        TangentBundle ThreeModel (ch.W k).X)) := by
  induction hY using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => exact fun k _ t => contMDiffAt_totalSpace_zero (ch.contMDiff k).contMDiffAt
  | add x y _ _ hx hy => exact fun k hk t => contMDiffAt_totalSpace_add (hx k hk t) (hy k hk t)
  | smul r x _ hx =>
    exact fun k hk t => (contMDiffAt_totalSpace_smul (ρ := fun _ => r) contMDiffAt_const
      (hx k hk t) :)

private theorem trace_inv_gram_le (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) (hv : 0 < v)
    (hli : LinearIndependent ℝ fun i => ch.jacobiField i (ch.n - 1) v)
    (hnn : ∀ V : ch.toLWindowChain.Field, (∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8
      (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t) (V k t) :
        TangentBundle ThreeModel (ch.W k).X))) → ch.toLWindowChain.IsGlued V → V 0 0 = 0 →
      V (ch.n - 1) v = 0 → 0 ≤ ch.toLWindowChain.historyLIndex V V) :
    trace ((Matrix.of fun i i' => ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner
        (ch.γ (ch.n - 1) v) (ch.jacobiField i (ch.n - 1) v) (ch.jacobiField i' (ch.n - 1) v))⁻¹ *
      Matrix.of fun i i' => ch.toLWindowChain.boundaryForm (ch.jacobiField i) (ch.n - 1) v
        (ch.jacobiField i' (ch.n - 1) v)) ≤
      2 * ∑ l, ch.toLWindowChain.historyLIndex (fun k s => (s / v) • P l k s)
        (fun k s => (s / v) • P l k s) := by
  have hcn : ch.c ch.n = v := ch.c_n
  have hON := hP.2.2
  rw [hcn] at hON
  let Y : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field :=
    fun l k s => (s / v) • P l k s
  have hsm : ∀ X ∈ range ch.jacobiField ∪ range Y, ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ)
      ThreeModel.tangent ∞ (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t) (X k t) :
        TangentBundle ThreeModel (ch.W k).X)) := by
    rintro X (⟨i, rfl⟩ | ⟨l, rfl⟩) k hk
    · exact ch.contMDiff_jacobiField i hk
    · exact ch.contMDiff_scaled hP l hk v
  have hYv : ∀ l, Y l (ch.n - 1) v = P l (ch.n - 1) v := fun l => by
    change (v / v) • P l (ch.n - 1) v = _
    rw [div_self hv.ne', one_smul]
  have hspan : ∀ l, Y l (ch.n - 1) v ∈ Submodule.span ℝ
      (range fun i => ch.jacobiField i (ch.n - 1) v) := by
    intro l
    rw [hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; rfl)]
    exact Submodule.mem_top
  refine ch.toLWindowChain.trace_inv_gram_mul_boundaryForm_le_sum_historyLIndex ch.jacobiField Y
    isHistoryLJacobi_jacobiField (fun l k hk s _ => differentiableAt_chartRepAt_of_contMDiff_two
      (I := ThreeModel) ((ch.contMDiff_scaled hP l hk v).of_le (natCast_le_infty 2)) s)
    (fun l => isGlued_scaled hP l v) ?_ ?_ (fun i => ch.jacobiField_zero hn i) (fun l => ?_) hspan
    (fun l l' => by rw [hYv, hYv]; exact hON l l')
  · intro X hX X' hX' k hk
    exact intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff (ch.W k).S (ch.W k).solution
      T _ _ (ch.γ k) _ _ ((hsm X hX k hk).of_le (natCast_le_infty 2))
      ((hsm X' hX' k hk).of_le (natCast_le_infty 2)) fun s hs => by
        obtain ⟨a, b, ha, hb, hreg⟩ := ch.regular_of_mem_piece hk
        rw [uIcc_of_le (ch.lt k hk).le] at hs
        exact hreg s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  · intro X hX hX0 hXv
    have hG : ∀ Y' ∈ range ch.jacobiField ∪ range Y, ch.toLWindowChain.IsGlued Y' := by
      rintro _ (⟨i, rfl⟩ | ⟨l, rfl⟩)
      · exact ch.isGlued_jacobiField i
      · exact isGlued_scaled hP l v
    exact hnn X (fun k hk => (contMDiff_of_mem_span hsm hX k hk).of_le (natCast_le_infty 8))
      (ch.toLWindowChain.isGlued_of_mem_span hG hX) hX0 hXv
  · change (0 / v) • P l 0 0 = 0
    rw [zero_div, zero_smul]

theorem bump_last (hn : 0 < ch.n) : ∀ᶠ s in 𝓝 v, ch.bump (ch.n - 1) s = 1 := by
  have hk : ch.n - 1 < ch.n := Nat.sub_lt hn one_pos
  obtain ⟨δ, hδ, -, hone, -, -⟩ := ch.bump_spec hk
  have hc : ch.c (ch.n - 1 + 1) = v := by rw [Nat.sub_add_cancel hn, ch.c_n]
  rw [hc] at hone
  exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith [ch.lt (ch.n - 1) hk, hc]
    ) (by linarith)) hone

theorem mem_K_last (hn : 0 < ch.n) : v ∈ ch.K (ch.n - 1) := by
  have hk : ch.n - 1 < ch.n := Nat.sub_lt hn one_pos
  have h := ch.piece_K (ch.n - 1) hk (right_mem_Icc.2 (ch.lt (ch.n - 1) hk).le)
  rwa [Nat.sub_add_cancel hn, ch.c_n] at h

theorem lGram_last (hn : 0 < ch.n) (hv : 0 < v) :
    lGram (ch.W (ch.n - 1)).S T (fun q => ch.β (ch.n - 1) (Z₀.1, Real.sqrt q))
      (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt q))
        Z₀.1 (chartModelBasis ThreeSpace i)) (v ^ 2) =
      Matrix.of fun i i' => ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner
        (ch.γ (ch.n - 1) v) (ch.jacobiField i (ch.n - 1) v) (ch.jacobiField i' (ch.n - 1) v) := by
  have hsq : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.le
  have hpt : ch.β (ch.n - 1) (Z₀.1, Real.sqrt (v ^ 2)) = ch.γ (ch.n - 1) v := by
    rw [hsq]; exact ch.curve _ v (ch.mem_K_last hn)
  have hone := (ch.bump_last hn).self_of_nhds
  have hFd : ∀ i, (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
      (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt (v ^ 2))) Z₀.1 (chartModelBasis ThreeSpace i) :
        ThreeSpace) = ch.jacobiField i (ch.n - 1) v := by
    intro i
    rw [hsq]
    change _ = ch.bump (ch.n - 1) v • ch.familyDeriv (ch.n - 1) (chartModelBasis ThreeSpace i) v
    rw [hone, one_smul]
    rfl
  ext i i'
  exact inner_congr_point' _ hpt _ _ _ _ (hFd i) (hFd i')

private theorem covDerivAlong_last (hn : 0 < ch.n) (hv : 0 < v)
    (i : Fin (Module.finrank ℝ ThreeSpace)) :
    (covDerivAlong (I := ThreeModel) ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2))
      (fun q => ch.β (ch.n - 1) (Z₀.1, Real.sqrt q))
      (fun q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt q))
        Z₀.1 (chartModelBasis ThreeSpace i)) (v ^ 2) : ThreeSpace) =
      (1 / (2 * v)) •
        (ch.toLWindowChain.covDerivField (ch.jacobiField i) (ch.n - 1) v : ThreeSpace) := by
  set k₀ := ch.n - 1 with hk₀
  have hsq : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.le
  have hvK := ch.mem_K_last hn
  have hone := ch.bump_last hn
  set g := (ch.W k₀).S.base.metric (T - v ^ 2) with hg
  have hJ := isLRegularizedJacobi_mfderiv_of_contMDiffOn (ch.W k₀).S T (ch.isOpen_V k₀)
    (ch.isOpen_K k₀) (ch.smooth k₀) (ch.family k₀) (ch.mem_V k₀)
    (chartModelBasis ThreeSpace i) v hvK
  have hsqrt := Real.hasDerivAt_sqrt (pow_pos hv 2).ne'
  have hcomp := covDerivAlong_comp (I := ThreeModel) g (fun r => ch.β k₀ (Z₀.1, r))
    (fun r => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k₀ (Z, r)) Z₀.1
      (chartModelBasis ThreeSpace i)) Real.sqrt (v ^ 2) (by rw [hsq]; exact hJ.1)
    (by rw [hsq]; exact hJ.2.1) hsqrt.differentiableAt
  rw [hsqrt.deriv, hsq] at hcomp
  rw [hcomp]
  have hc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := ThreeModel) g (fun r => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
      (fun Z => ch.β k₀ (Z, r)) Z₀.1 (chartModelBasis ThreeSpace i)) (ch.jacobiField i k₀)
    (t := v) (Filter.eventually_of_mem ((ch.isOpen_K k₀).mem_nhds hvK) fun r hr =>
      ch.curve _ r hr)
    (by
      filter_upwards [hone] with r hr
      change _ = ch.bump k₀ r • ch.familyDeriv k₀ (chartModelBasis ThreeSpace i) r
      rw [hr, one_smul]
      rfl)
  rw [hsq]
  change (1 / (2 * v)) • (covDerivAlong (I := ThreeModel) g _ _ v : ThreeSpace) = _
  rw [hc]
  rfl

private theorem lGramDeriv_last (hn : 0 < ch.n) (hv : 0 < v) :
    lGramDeriv (ch.W (ch.n - 1)).S T (fun q => ch.β (ch.n - 1) (Z₀.1, Real.sqrt q))
      (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt q))
        Z₀.1 (chartModelBasis ThreeSpace i)) (v ^ 2) =
      (1 / (2 * v)) • ((Matrix.of fun i i' => ch.toLWindowChain.boundaryForm (ch.jacobiField i)
          (ch.n - 1) v (ch.jacobiField i' (ch.n - 1) v)) +
        (Matrix.of fun i i' => ch.toLWindowChain.boundaryForm (ch.jacobiField i)
          (ch.n - 1) v (ch.jacobiField i' (ch.n - 1) v)).transpose) +
      (2 : ℝ) • Matrix.of fun i i' => (ch.W (ch.n - 1)).S.ricciAt (T - v ^ 2) (ch.γ (ch.n - 1) v)
        (vec2 (ch.jacobiField i (ch.n - 1) v) (ch.jacobiField i' (ch.n - 1) v)) := by
  have hsq : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.le
  have hpt : ch.β (ch.n - 1) (Z₀.1, Real.sqrt (v ^ 2)) = ch.γ (ch.n - 1) v := by
    rw [hsq]; exact ch.curve _ v (ch.mem_K_last hn)
  have hone := (ch.bump_last hn).self_of_nhds
  have hFd : ∀ i, (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
      (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt (v ^ 2))) Z₀.1 (chartModelBasis ThreeSpace i) :
        ThreeSpace) = ch.jacobiField i (ch.n - 1) v := by
    intro i
    rw [hsq]
    change _ = ch.bump (ch.n - 1) v • ch.familyDeriv (ch.n - 1) (chartModelBasis ThreeSpace i) v
    rw [hone, one_smul]
    rfl
  rw [lGramDeriv_eq_of_eq _ T _ _ (v ^ 2) (1 / (2 * v))
    (fun i => (ch.toLWindowChain.covDerivField (ch.jacobiField i) (ch.n - 1) v : ThreeSpace))
    (fun i => ch.covDerivAlong_last hn hv i)]
  have hN : (Matrix.of fun i j => ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner
      (ch.β (ch.n - 1) (Z₀.1, Real.sqrt (v ^ 2)))
      (ch.toLWindowChain.covDerivField (ch.jacobiField i) (ch.n - 1) v : ThreeSpace)
      (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt (v ^ 2)))
        Z₀.1 (chartModelBasis ThreeSpace j))) =
      Matrix.of fun i i' => ch.toLWindowChain.boundaryForm (ch.jacobiField i)
        (ch.n - 1) v (ch.jacobiField i' (ch.n - 1) v) := by
    ext i j
    exact inner_congr_point' _ hpt _ _ _ _ rfl (hFd j)
  have hR : (Matrix.of fun i j => (ch.W (ch.n - 1)).S.ricciAt (T - v ^ 2)
      (ch.β (ch.n - 1) (Z₀.1, Real.sqrt (v ^ 2)))
      (vec2 (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
        (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt (v ^ 2))) Z₀.1 (chartModelBasis ThreeSpace i))
        (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
        (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt (v ^ 2))) Z₀.1 (chartModelBasis ThreeSpace j)))) =
      Matrix.of fun i i' => (ch.W (ch.n - 1)).S.ricciAt (T - v ^ 2) (ch.γ (ch.n - 1) v)
        (vec2 (ch.jacobiField i (ch.n - 1) v) (ch.jacobiField i' (ch.n - 1) v)) := by
    ext i j
    exact ricciAt_congr_point _ _ hpt _ _ _ _ (hFd i) (hFd j)
  rw [hN, hR]

theorem half_trace_le (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) (hv : 0 < v)
    (hli : LinearIndependent ℝ fun i => ch.jacobiField i (ch.n - 1) v)
    (hnn : ∀ V : ch.toLWindowChain.Field, (∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8
      (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t) (V k t) :
        TangentBundle ThreeModel (ch.W k).X))) → ch.toLWindowChain.IsGlued V → V 0 0 = 0 →
      V (ch.n - 1) v = 0 → 0 ≤ ch.toLWindowChain.historyLIndex V V) :
    (1 / 2) * trace ((lGram (ch.W (ch.n - 1)).S T (fun q => ch.β (ch.n - 1) (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
          (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt q)) Z₀.1 (chartModelBasis ThreeSpace i))
          (v ^ 2))⁻¹ *
      lGramDeriv (ch.W (ch.n - 1)).S T (fun q => ch.β (ch.n - 1) (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel
          (fun Z => ch.β (ch.n - 1) (Z, Real.sqrt q)) Z₀.1 (chartModelBasis ThreeSpace i))
          (v ^ 2)) ≤
      lRegularizedLagrangian (ch.W (ch.n - 1)).S T (ch.γ (ch.n - 1)) v / (4 * v ^ 2) -
        (∑ k ∈ Finset.range ch.n,
          lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1))) / (4 * v ^ 3) +
        3 / (2 * v ^ 2) := by
  rw [ch.lGram_last hn hv, ch.lGramDeriv_last hn hv]
  set k₀ := ch.n - 1 with hk₀
  set g := (ch.W k₀).S.base.metric (T - v ^ 2) with hg
  set x := ch.γ k₀ v with hx
  set G : Matrix (Fin (Module.finrank ℝ ThreeSpace)) (Fin (Module.finrank ℝ ThreeSpace)) ℝ :=
    Matrix.of fun i i' => g.inner x (ch.jacobiField i k₀ v) (ch.jacobiField i' k₀ v) with hG
  set N : Matrix (Fin (Module.finrank ℝ ThreeSpace)) (Fin (Module.finrank ℝ ThreeSpace)) ℝ :=
    Matrix.of fun i i' => ch.toLWindowChain.boundaryForm (ch.jacobiField i) k₀ v
      (ch.jacobiField i' k₀ v) with hN
  set Rm : Matrix (Fin (Module.finrank ℝ ThreeSpace)) (Fin (Module.finrank ℝ ThreeSpace)) ℝ :=
    Matrix.of fun i i' => (ch.W k₀).S.ricciAt (T - v ^ 2) x
      (vec2 (ch.jacobiField i k₀ v) (ch.jacobiField i' k₀ v)) with hRm
  have hmain : trace (G⁻¹ * N) ≤ 2 * ∑ l, ch.toLWindowChain.historyLIndex
      (fun k s => (s / v) • P l k s) (fun k s => (s / v) • P l k s) :=
    trace_inv_gram_le hP hn hv hli hnn
  have hGs : G.transpose = G := by
    ext i j
    exact g.symm x _ _
  have htrT : trace (G⁻¹ * N.transpose) = trace (G⁻¹ * N) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hGs, Matrix.trace_mul_comm]
  have hON := hP.2.2
  rw [ch.c_n] at hON
  have hspan : ∀ l, P l k₀ v ∈ Submodule.span ℝ (range fun i => ch.jacobiField i k₀ v) := by
    intro l
    rw [hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; rfl)]
    exact Submodule.mem_top
  have hRtr : trace (G⁻¹ * Rm) = (ch.W k₀).S.scalar (T - v ^ 2) x := by
    have hRm' : Rm = Matrix.of fun i i' => ricciTensor (I := ThreeModel) g x
        (ch.jacobiField i k₀ v) (ch.jacobiField i' k₀ v) := by
      ext i j
      exact metricRicciAt_apply_eq_ricciTensor (I := ThreeModel) g x _ _
    have h := trace_inv_gram_mul_eq_sum_orthonormal
      (ContinuousLinearMap.toLinearMap₁₂ (g.inner x))
      (ContinuousLinearMap.toLinearMap₁₂ (ricciTensor (I := ThreeModel) g x))
      (fun i => ch.jacobiField i k₀ v) (fun l => P l k₀ v) hspan hON
    rw [hRm']
    refine h.trans ?_
    rw [← sum_ricciAt_eq_scalar (ch.W k₀).S (T - v ^ 2) x (fun l => P l k₀ v) hON]
    exact Finset.sum_congr rfl fun l _ =>
      (metricRicciAt_apply_eq_ricciTensor (I := ThreeModel) g x _ _).symm
  have hsum := sum_historyLIndex hP hn hv
  rw [ch.c_n] at hsum
  simp only [energy] at hsum
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add, htrT, hRtr, smul_eq_mul, smul_eq_mul]
  rw [hsum] at hmain
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hc : 0 ≤ 1 / (2 * v) := by positivity
  have key := mul_le_mul_of_nonneg_left hmain hc
  have e : (1 / (2 * v)) * (2 * ((v * lRegularizedLagrangian (ch.W k₀).S T (ch.γ k₀) v / 4 -
      v ^ 3 * (ch.W k₀).S.scalar (T - v ^ 2) (ch.γ k₀ v) -
      (∑ k ∈ Finset.range ch.n, lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k)
        (ch.c (k + 1))) / 4) / v ^ 2 + 3 * v / (2 * v ^ 2))) =
      lRegularizedLagrangian (ch.W k₀).S T (ch.γ k₀) v / (4 * v ^ 2) -
        (∑ k ∈ Finset.range ch.n,
          lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1))) / (4 * v ^ 3) +
        3 / (2 * v ^ 2) - (ch.W k₀).S.scalar (T - v ^ 2) (ch.γ k₀ v) := by
    field_simp
    ring
  rw [e] at key
  nlinarith [key]

end LFamilyChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
