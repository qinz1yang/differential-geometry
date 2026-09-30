import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.JacobiField.FamilyChain.VariationFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u

theorem inner_congr_point' {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) {p q : N} (h : p = q)
    (a b : TangentSpace ThreeModel p) (a' b' : TangentSpace ThreeModel q)
    (ha : (a : ThreeSpace) = a') (hb : (b : ThreeSpace) = b') :
    g.inner p a b = g.inner q a' b' := by
  subst h
  rw [show a = a' from ha, show b = b' from hb]

private theorem finrank_threeSpace : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]

private theorem lVelocity_congr_eventually {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] {γ δ : ℝ → N} {t : ℝ} (h : γ =ᶠ[𝓝 t] δ) :
    (lVelocity (I := ThreeModel) γ t : ThreeSpace) = lVelocity (I := ThreeModel) δ t := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) h
  with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf

variable {H : ObservedHistory.{u}} {first last fst : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {hfst : first ≤ fst} {T w v : ℝ} {p : (H.stage last).Carrier}
  {Z₀ : H.historyLExpDomain hle T w p}

namespace LFamilyChain

variable (ch : H.LFamilyChain hle hfst T w v p Z₀)

def IsAdaptedFrame (P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field) : Prop :=
  (∀ l, ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun s => (TotalSpace.mk' ThreeSpace (ch.γ k s) (P l k s) :
        TangentBundle ThreeModel (ch.W k).X)) ∧
    ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧ IsLAdapted (ch.W k).S T (ch.γ k) (P l k) (Ioo a b)) ∧
  (∀ l, ch.toLWindowChain.IsGlued (P l)) ∧
  ∀ l l', ((ch.W (ch.n - 1)).S.base.metric (T - ch.c ch.n ^ 2)).inner
    (ch.γ (ch.n - 1) (ch.c ch.n)) (P l (ch.n - 1) (ch.c ch.n))
      (P l' (ch.n - 1) (ch.c ch.n)) = if l = l' then 1 else 0

theorem exists_isAdaptedFrame (hn : 0 < ch.n) : ∃ P, ch.IsAdaptedFrame P :=
  ch.exists_adaptedFrame hn

private theorem inner_node {A B : ch.toLWindowChain.Field} {k : ℕ} (hk : k + 1 < ch.n)
    (hA : ch.toLWindowChain.GluedAt A hk) (hB : ch.toLWindowChain.GluedAt B hk) :
    ((ch.W k).S.base.metric (T - ch.c (k + 1) ^ 2)).inner (ch.γ k (ch.c (k + 1)))
        (A k (ch.c (k + 1))) (B k (ch.c (k + 1))) =
      ((ch.W (k + 1)).S.base.metric (T - ch.c (k + 1) ^ 2)).inner
        (ch.γ (k + 1) (ch.c (k + 1))) (A (k + 1) (ch.c (k + 1))) (B (k + 1) (ch.c (k + 1))) := by
  rw [(ch.W k).metric (ch.bottom (Nat.lt_of_succ_lt hk)) _ (ch.node k hk).1,
    (ch.W (k + 1)).metric (ch.top hk) _ (ch.node k hk).2, localPullMetric_inner,
    localPullMetric_inner]
  exact inner_congr_point' _ (ch.toLWindowChain.bottom_eq_top hk) _ _ _ _ hA hB

theorem regular_of_mem_piece {k : ℕ} (hk : k < ch.n) :
    ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧ ∀ s ∈ Ioo a b, T - s ^ 2 ∈ (ch.W k).D.regular := by
  obtain ⟨a, b, ha, hb, hgeo⟩ := ch.geodesic k hk
  exact ⟨a, b, ha, hb, fun s hs => (hgeo s hs).1⟩

variable {ch}

private theorem IsAdaptedFrame.inner_eq
    {P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field}
    (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) : ∀ k < ch.n, ∀ s ∈ Icc (ch.c k) (ch.c (k + 1)),
      ∀ l l', ((ch.W k).S.base.metric (T - s ^ 2)).inner (ch.γ k s) (P l k s) (P l' k s) =
        if l = l' then 1 else 0 := by
  obtain ⟨hPs, hPg, hPon⟩ := hP
  have step : ∀ k (hk : k < ch.n), ∀ s ∈ Icc (ch.c k) (ch.c (k + 1)), ∀ l l',
      ((ch.W k).S.base.metric (T - s ^ 2)).inner (ch.γ k s) (P l k s) (P l' k s) =
        ((ch.W k).S.base.metric (T - ch.c (k + 1) ^ 2)).inner (ch.γ k (ch.c (k + 1)))
          (P l k (ch.c (k + 1))) (P l' k (ch.c (k + 1))) := by
    intro k hk s hs l l'
    obtain ⟨a, b, ha, hb, hreg⟩ := ch.regular_of_mem_piece hk
    obtain ⟨a₁, b₁, ha₁, hb₁, had₁⟩ := (hPs l k hk).2
    obtain ⟨a₂, b₂, ha₂, hb₂, had₂⟩ := (hPs l' k hk).2
    have hsub : ∀ r ∈ Icc s (ch.c (k + 1)), r ∈ Icc (ch.c k) (ch.c (k + 1)) :=
      fun r hr => ⟨hs.1.trans hr.1, hr.2⟩
    exact metric_inner_eq_of_isLAdapted (ch.W k).S (ch.W k).solution T (ch.γ k) (P l k) (P l' k)
      hs.2 (fun r hr => hreg r ⟨ha.trans_le (hsub r hr).1, (hsub r hr).2.trans_lt hb⟩)
      (fun r _ => (ch.contMDiff k).mdifferentiableAt (by simp))
      (fun r _ => differentiableAt_chartRepAt_of_contMDiff_two (I := ThreeModel)
        ((hPs l k hk).1.of_le (natCast_le_infty 2)) r)
      (fun r _ => differentiableAt_chartRepAt_of_contMDiff_two (I := ThreeModel)
        ((hPs l' k hk).1.of_le (natCast_le_infty 2)) r)
      (fun r hr => had₁ r ⟨ha₁.trans_le (hsub r hr).1, (hsub r hr).2.trans_lt hb₁⟩)
      (fun r hr => had₂ r ⟨ha₂.trans_le (hsub r hr).1, (hsub r hr).2.trans_lt hb₂⟩)
  have key : ∀ d, d < ch.n → ∀ l l', ((ch.W (ch.n - 1 - d)).S.base.metric
      (T - ch.c (ch.n - 1 - d + 1) ^ 2)).inner (ch.γ (ch.n - 1 - d) (ch.c (ch.n - 1 - d + 1)))
        (P l (ch.n - 1 - d) (ch.c (ch.n - 1 - d + 1)))
        (P l' (ch.n - 1 - d) (ch.c (ch.n - 1 - d + 1))) = if l = l' then 1 else 0 := by
    intro d
    induction d with
    | zero =>
      intro _ l l'
      have h : ch.n - 1 - 0 + 1 = ch.n := by omega
      simp only [Nat.sub_zero]
      rw [show ch.n - 1 + 1 = ch.n by omega]
      exact hPon l l'
    | succ d ih =>
      intro hd l l'
      set k := ch.n - 1 - (d + 1) with hkdef
      have hk1 : k + 1 < ch.n := by omega
      have hkd : ch.n - 1 - d = k + 1 := by omega
      have h := ih (Nat.lt_of_succ_lt hd)
      rw [hkd] at h
      rw [ch.inner_node hk1 (hPg l k hk1) (hPg l' k hk1),
        step (k + 1) hk1 _ (left_mem_Icc.2 (ch.lt (k + 1) hk1).le)]
      exact h l l'
  intro k hk s hs l l'
  rw [step k hk s hs]
  have h := key (ch.n - 1 - k) (by omega) l l'
  rwa [show ch.n - 1 - (ch.n - 1 - k) = k by omega] at h

variable (ch) in
def energy (k : ℕ) (s : ℝ) : ℝ :=
  s * lRegularizedLagrangian (ch.W k).S T (ch.γ k) s / 4 -
    s ^ 3 * (ch.W k).S.scalar (T - s ^ 2) (ch.γ k s)

private theorem isLRegularizedCurveOn_of_geodesic {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] {D : RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := X) D} {γ : ℝ → X} {J : Set ℝ}
    (h : IsLRegularizedGeodesicOn S T γ J) :
    IsLRegularizedCurveOn S T γ J (γ 0)
      ((2 : ℝ)⁻¹ • lVelocity (I := ThreeModel) γ 0) := by
  refine ⟨rfl, ?_, h⟩
  rw [two_nsmul, ← add_smul]
  norm_num

theorem sum_ricciAt_eq_scalar {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (t : ℝ) (x : X)
    (B : Fin (Module.finrank ℝ ThreeSpace) → TangentSpace ThreeModel x)
    (hB : ∀ i j, (S.base.metric t).inner x (B i) (B j) = if i = j then 1 else 0) :
    ∑ i, S.ricciAt t x (vec2 (B i) (B i)) = S.scalar t x := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  calc ∑ i, S.ricciAt t x (vec2 (B i) (B i)) =
        ∑ i, ricciTensor (I := ThreeModel) (S.base.metric t) x (B i) (B i) :=
          Finset.sum_congr rfl fun i _ => metricRicciAt_apply_eq_ricciTensor (I := ThreeModel)
            (S.base.metric t) x (B i) (B i)
    _ = scalarCurv (I := ThreeModel) (S.base.metric t) x :=
      (scalarCurv_eq_orthonormal_trace (I := ThreeModel) (S.base.metric t) x B hB).symm
    _ = metricScalarAt (I := ThreeModel) (S.base.metric t) x :=
      (metricScalar_eq_scal (I := ThreeModel) (S.base.metric t) x).symm

variable {P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field}

private theorem IsAdaptedFrame.isLAdaptedAt (hP : ch.IsAdaptedFrame P)
    (l : Fin (Module.finrank ℝ ThreeSpace))
    {k : ℕ} (hk : k < ch.n) {s : ℝ} (hs : s ∈ Icc (ch.c k) (ch.c (k + 1))) :
    IsLAdaptedAt (ch.W k).S T (ch.γ k) (P l k) s := by
  obtain ⟨a, b, ha, hb, had⟩ := (hP.1 l k hk).2
  exact had s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩

private theorem sum_integrand_eq (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) {k : ℕ} (hk : k < ch.n)
    {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : s ∈ Icc (ch.c k) (ch.c (k + 1))) :
    ∑ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (fun r => (r / b) • P l k r)
        (fun r => (r / b) • P l k r) s =
      (s / b) ^ 2 * ∑ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (P l k) (P l k) s +
        3 / (2 * b ^ 2) - (2 * s ^ 2 / b ^ 2) * (ch.W k).S.scalar (T - s ^ 2) (ch.γ k s) := by
  have hON := hP.inner_eq hn k hk s hs
  have hf : ∀ r : ℝ, HasDerivAt (fun r : ℝ => r / b) (1 / b) r := fun r => by
    simpa using (hasDerivAt_id r).div_const b
  have hterm : ∀ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (fun r => (r / b) • P l k r)
      (fun r => (r / b) • P l k r) s =
      (s / b) ^ 2 * lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (P l k) (P l k) s +
        1 / (2 * b ^ 2) - 2 * s * (s / b) * (1 / b) *
          (ch.W k).S.ricciAt (T - s ^ 2) (ch.γ k s) (vec2 (P l k s) (P l k s)) := by
    intro l
    rw [lRegularizedIndexIntegrand_smul_function_self_of_isLAdaptedAt (ch.W k).S T (ch.γ k)
      (P l k) (fun r => r / b) s (hf s).differentiableAt
      (differentiableAt_chartRepAt_of_contMDiff_two (I := ThreeModel)
        ((hP.1 l k hk).1.of_le (natCast_le_infty 2)) s) (hP.isLAdaptedAt l hk hs),
      (hf s).deriv, hON l l, ite_eq_left rfl]
    field_simp
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    sum_ricciAt_eq_scalar (ch.W k).S _ _ (fun l => P l k s) hON, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  have h3 : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by exact_mod_cast finrank_threeSpace
  simp only [nsmul_eq_mul]
  rw [h3]
  ring

private theorem hasDerivAt_energy (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) {k : ℕ} (hk : k < ch.n)
    {s : ℝ} (hs : s ∈ Icc (ch.c k) (ch.c (k + 1))) :
    HasDerivAt (ch.energy k) (lRegularizedLagrangian (ch.W k).S T (ch.γ k) s / 4 +
      (s ^ 2 * ∑ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (P l k) (P l k) s -
        2 * s ^ 2 * (ch.W k).S.scalar (T - s ^ 2) (ch.γ k s))) s := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨a, b, ha, hb, hgeo⟩ := ch.geodesic k hk
  have hsab : s ∈ Ioo a b := ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hL := (lLagMul_deriv (ch.W k).S (ch.W k).solution T
    (isLRegularizedCurveOn_of_geodesic hgeo) hsab).div_const 4
  have hR := lTrace_deriv (ch.W k).S (ch.W k).solution T (ch.γ k) (fun l => P l k) s
    (hgeo s hsab).1 ((ch.contMDiff k).mdifferentiableAt (by simp))
    (fun l => hP.isLAdaptedAt l hk hs) (hP.inner_eq hn k hk s hs)
  refine (hL.sub hR).congr_deriv ?_
  ring

theorem contMDiff_scaled (hP : ch.IsAdaptedFrame P) (l : Fin (Module.finrank ℝ ThreeSpace))
    {k : ℕ} (hk : k < ch.n) (b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun r => (TotalSpace.mk' ThreeSpace (ch.γ k r)
      ((r / b) • P l k r) : TangentBundle ThreeModel (ch.W k).X)) := fun t =>
  contMDiffAt_totalSpace_smul (contDiff_id.div_const b).contMDiff.contMDiffAt
    ((hP.1 l k hk).1 t)

private theorem intervalIntegrable_lagrangian {k : ℕ} (hk : k < ch.n) :
    IntervalIntegrable (lRegularizedLagrangian (ch.W k).S T (ch.γ k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (ch.γ k) := (ch.contMDiff k).of_le (by decide)
  have hc := lRegularizedLagrangian_continuousOn_carrier (ch.W k).S (ch.W k).solution (ch.γ k) hγ
  have hh := hc.comp (s := Icc (ch.c k) (ch.c (k + 1)))
    (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => (ch.W k).mem_carrier (ch.piece k hk ht))
  exact hh.intervalIntegrable_of_Icc (ch.lt k hk).le

private theorem sum_lRegularizedIndex_piece (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) {k : ℕ}
    (hk : k < ch.n) {b : ℝ} (hb : 0 < b) :
    ∑ l, lRegularizedIndex (ch.W k).S T (ch.γ k) (fun r => (r / b) • P l k r)
        (fun r => (r / b) • P l k r) (ch.c k) (ch.c (k + 1)) =
      (ch.energy k (ch.c (k + 1)) - ch.energy k (ch.c k) -
          lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) / 4) / b ^ 2 +
        3 * (ch.c (k + 1) - ch.c k) / (2 * b ^ 2) := by
  have hlt := ch.lt k hk
  have huIcc : uIcc (ch.c k) (ch.c (k + 1)) = Icc (ch.c k) (ch.c (k + 1)) := uIcc_of_le hlt.le
  obtain ⟨a, a', ha, ha', hreg⟩ := ch.regular_of_mem_piece hk
  have hreg' : ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)), T - s ^ 2 ∈ (ch.W k).D.regular := by
    intro s hs
    rw [huIcc] at hs
    exact hreg s ⟨ha.trans_le hs.1, hs.2.trans_lt ha'⟩
  have hInt : ∀ l, IntervalIntegrable (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k)
      (fun r => (r / b) • P l k r) (fun r => (r / b) • P l k r)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)) := fun l =>
    intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff (ch.W k).S (ch.W k).solution T
      _ _ (ch.γ k) _ _ ((ch.contMDiff_scaled hP l hk b).of_le (natCast_le_infty 2))
      ((ch.contMDiff_scaled hP l hk b).of_le (natCast_le_infty 2)) hreg'
  have hLag := ch.intervalIntegrable_lagrangian hk
  set F : ℝ → ℝ := fun s => ∑ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k)
    (fun r => (r / b) • P l k r) (fun r => (r / b) • P l k r) s with hF
  set L : ℝ → ℝ := lRegularizedLagrangian (ch.W k).S T (ch.γ k) with hL
  set D' : ℝ → ℝ := fun s => L s / 4 +
    (s ^ 2 * ∑ l, lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (P l k) (P l k) s -
      2 * s ^ 2 * (ch.W k).S.scalar (T - s ^ 2) (ch.γ k s)) with hD'
  have hpt : ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)),
      F s = (D' s - L s / 4) / b ^ 2 + 3 / (2 * b ^ 2) := by
    intro s hs
    rw [huIcc] at hs
    simp only [hF, hD']
    rw [ch.sum_integrand_eq hP hn hk hb hs]
    field_simp
    ring
  have hFint : IntervalIntegrable F MeasureTheory.volume (ch.c k) (ch.c (k + 1)) := by
    have h := IntervalIntegrable.sum Finset.univ fun l _ => hInt l
    rw [Finset.sum_fn] at h
    exact h
  have hD'int : IntervalIntegrable D' MeasureTheory.volume (ch.c k) (ch.c (k + 1)) := by
    refine (intervalIntegrable_congr (fun s hs => ?_)).mp
      (((hFint.sub (intervalIntegrable_const : IntervalIntegrable (fun _ => (3 / (2 * b ^ 2) : ℝ))
        MeasureTheory.volume (ch.c k) (ch.c (k + 1)))).const_mul (b ^ 2)).add (hLag.div_const 4))
    have h := hpt s (uIoc_subset_uIcc hs)
    rw [h]
    field_simp
    ring
  have hFTC : ∫ s in (ch.c k)..(ch.c (k + 1)), D' s =
      ch.energy k (ch.c (k + 1)) - ch.energy k (ch.c k) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => ch.hasDerivAt_energy hP hn hk (huIcc ▸ hs)) hD'int
  have hsum : ∑ l, lRegularizedIndex (ch.W k).S T (ch.γ k) (fun r => (r / b) • P l k r)
      (fun r => (r / b) • P l k r) (ch.c k) (ch.c (k + 1)) =
      ∫ s in (ch.c k)..(ch.c (k + 1)), F s := by
    simp only [lRegularizedIndex, hF]
    exact (intervalIntegral.integral_finsetSum fun l _ => hInt l).symm
  rw [hsum, intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_add ((hD'int.sub (hLag.div_const 4)).div_const _)
      intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_sub hD'int (hLag.div_const 4),
    intervalIntegral.integral_div, hFTC, intervalIntegral.integral_const, smul_eq_mul]
  simp only [lRegularizedAction, hL]
  ring

private theorem comp_eventuallyEq_node {k : ℕ} (hk : k + 1 < ch.n) :
    (fun r => (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (ch.γ k r)) =ᶠ[𝓝 (ch.c (k + 1))]
      fun r => (ch.W (k + 1)).f (ch.top hk) (ch.γ (k + 1) r) := by
  filter_upwards [isOpen_Ioo.mem_nhds (ch.node k hk).1, isOpen_Ioo.mem_nhds (ch.node k hk).2]
    with r h1 h2
  exact (ch.eqOn k (Nat.lt_of_succ_lt hk) (ch.bottom (Nat.lt_of_succ_lt hk))
    (Ioo_subset_Icc_self h1)).trans
    (ch.eqOn (k + 1) hk (ch.top hk) (Ioo_subset_Icc_self h2)).symm

private theorem energy_node {k : ℕ} (hk : k + 1 < ch.n) :
    ch.energy k (ch.c (k + 1)) = ch.energy (k + 1) (ch.c (k + 1)) := by
  have hk' : k < ch.n := Nat.lt_of_succ_lt hk
  set c := ch.c (k + 1) with hc
  have hR : (ch.W k).S.scalar (T - c ^ 2) (ch.γ k c) =
      (ch.W (k + 1)).S.scalar (T - c ^ 2) (ch.γ (k + 1) c) := by
    change metricScalarAt ((ch.W k).S.base.metric (T - c ^ 2)) (ch.γ k c) =
      metricScalarAt ((ch.W (k + 1)).S.base.metric (T - c ^ 2)) (ch.γ (k + 1) c)
    rw [(ch.W k).metric (ch.bottom hk') _ (ch.node k hk).1,
      (ch.W (k + 1)).metric (ch.top hk) _ (ch.node k hk).2, metricScalarAt_localPull,
      metricScalarAt_localPull]
    exact congrArg _ (ch.toLWindowChain.bottom_eq_top hk)
  have hvel := (lVelocity_comp_of_isLocalDiffeomorph ((ch.W k).localDiffeomorph (ch.bottom hk'))
    ((ch.contMDiff k).mdifferentiableAt (by simp) (x := c))).symm.trans
    ((lVelocity_congr_eventually (ch.comp_eventuallyEq_node hk)).trans
      (lVelocity_comp_of_isLocalDiffeomorph ((ch.W (k + 1)).localDiffeomorph (ch.top hk))
        ((ch.contMDiff (k + 1)).mdifferentiableAt (by simp) (x := c))))
  have hI : ((ch.W k).S.base.metric (T - c ^ 2)).inner (ch.γ k c)
      (lVelocity (I := ThreeModel) (ch.γ k) c) (lVelocity (I := ThreeModel) (ch.γ k) c) =
      ((ch.W (k + 1)).S.base.metric (T - c ^ 2)).inner (ch.γ (k + 1) c)
        (lVelocity (I := ThreeModel) (ch.γ (k + 1)) c)
        (lVelocity (I := ThreeModel) (ch.γ (k + 1)) c) := by
    rw [(ch.W k).metric (ch.bottom hk') _ (ch.node k hk).1,
      (ch.W (k + 1)).metric (ch.top hk) _ (ch.node k hk).2, localPullMetric_inner,
      localPullMetric_inner]
    exact inner_congr_point' _ (ch.toLWindowChain.bottom_eq_top hk) _ _ _ _ hvel hvel
  simp only [energy, lRegularizedLagrangian]
  rw [hI, hR]

private theorem energy_zero_zero : ch.energy 0 (ch.c 0) = 0 := by
  simp [energy, ch.c_zero]

private theorem sum_range_energy :
    ∑ k ∈ Finset.range ch.n, (ch.energy k (ch.c (k + 1)) - ch.energy k (ch.c k)) =
      ch.energy (ch.n - 1) (ch.c ch.n) := by
  let G : ℕ → ℝ := fun m => ch.energy (m - 1) (ch.c m)
  have hstep : ∀ k < ch.n, ch.energy k (ch.c (k + 1)) - ch.energy k (ch.c k) = G (k + 1) - G k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rfl
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      change _ = ch.energy (j + 1) (ch.c (j + 1 + 1)) - ch.energy j (ch.c (j + 1))
      rw [ch.energy_node (k := j) hk]
  rw [Finset.sum_congr rfl fun k hk => hstep k (Finset.mem_range.1 hk), Finset.sum_range_sub]
  change ch.energy (ch.n - 1) (ch.c ch.n) - ch.energy 0 (ch.c 0) = _
  rw [ch.energy_zero_zero, sub_zero]

private theorem sum_range_sub_c : ∑ k ∈ Finset.range ch.n, (ch.c (k + 1) - ch.c k) = v := by
  rw [Finset.sum_range_sub, ch.c_n, ch.c_zero, sub_zero]

theorem sum_historyLIndex (hP : ch.IsAdaptedFrame P) (hn : 0 < ch.n) {b : ℝ} (hb : 0 < b) :
    ∑ l, ch.toLWindowChain.historyLIndex (fun k s => (s / b) • P l k s)
        (fun k s => (s / b) • P l k s) =
      (ch.energy (ch.n - 1) (ch.c ch.n) - (∑ k ∈ Finset.range ch.n,
          lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1))) / 4) / b ^ 2 +
        3 * v / (2 * b ^ 2) := by
  simp only [LWindowChain.historyLIndex]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun k hk =>
    ch.sum_lRegularizedIndex_piece hP hn (Finset.mem_range.1 hk) hb]
  have hc : ∑ k ∈ Finset.range ch.n, 3 * (ch.c (k + 1) - ch.c k) / (2 * b ^ 2) =
      3 * v / (2 * b ^ 2) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, ch.sum_range_sub_c]
  rw [Finset.sum_add_distrib, hc, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div,
    ch.sum_range_energy]

end LFamilyChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
