import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.AdaptedFieldIcc
import DifferentialGeometry.Bundle.PartialMfderiv.Regularity

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

theorem exists_bump_eq_one {K : Set ℝ} (hK : IsOpen K) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ K) :
    ∃ ρ : ℝ → ℝ, ∃ δ > 0, ContDiff ℝ ∞ ρ ∧ (∀ s ∈ Ioo (a - δ) (b + δ), ρ s = 1) ∧
      (∀ s, s ∉ K → ∀ᶠ r in 𝓝 s, ρ r = 0) ∧ Ioo (a - δ) (b + δ) ⊆ K := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hK a (hsub (left_mem_Icc.2 hab))
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.1 hK b (hsub (right_mem_Icc.2 hab))
  set ε := min ε₁ ε₂ with hε
  have hε0 : 0 < ε := lt_min hε₁ hε₂
  have hIoo : Ioo (a - ε) (b + ε) ⊆ K := by
    intro s hs
    by_cases hsa : s < a
    · apply h₁
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, min_le_left ε₁ ε₂]
    by_cases hsb : b < s
    · apply h₂
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.2, min_le_right ε₁ ε₂]
    exact hsub ⟨not_lt.1 hsa, not_lt.1 hsb⟩
  set m := (a + b) / 2 with hm
  let χ : ContDiffBump m := ⟨(b - a) / 2 + ε / 3, (b - a) / 2 + 2 * ε / 3, by linarith,
    by linarith⟩
  refine ⟨χ, ε / 3, by positivity, χ.contDiff, fun s hs => ?_, fun s hs => ?_,
    (Ioo_subset_Ioo (by linarith) (by linarith)).trans hIoo⟩
  · apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |s - m| ≤ (b - a) / 2 + ε / 3
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  · have hfar : (b - a) / 2 + ε ≤ |s - m| := by
      by_contra h
      apply hs
      apply hIoo
      rw [not_le, abs_lt] at h
      constructor <;> linarith [h.1, h.2]
    filter_upwards [Metric.ball_mem_nhds s (show 0 < ε / 3 by positivity)] with r hr
    apply χ.zero_of_le_dist
    rw [Metric.mem_ball, Real.dist_eq] at hr
    rw [Real.dist_eq]
    have h3 := abs_sub_abs_le_abs_sub (s - m) (r - m)
    have h4 : |s - m - (r - m)| = |r - s| := by rw [abs_sub_comm]; ring_nf
    change (b - a) / 2 + 2 * ε / 3 ≤ |r - m|
    linarith

theorem natCast_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := by
  change (↑(m : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
  exact WithTop.coe_le_coe.mpr le_top

private theorem totalSpace_mk_eq_of_eq {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    {x y : X} (h : x = y) (v : ThreeSpace) :
    (TotalSpace.mk' ThreeSpace x v : TangentBundle ThreeModel X) =
      TotalSpace.mk' ThreeSpace y v := by
  subst h
  rfl

private theorem mfderiv_apply_congr_point {X N : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] {F : X → N} {x y : X} (h : x = y)
    (a : TangentSpace ThreeModel x) (b : TangentSpace ThreeModel y)
    (hab : (a : ThreeSpace) = b) :
    (mfderiv ThreeModel ThreeModel F x a : ThreeSpace) = mfderiv ThreeModel ThreeModel F y b := by
  subst h
  rw [show a = b from hab]

private theorem isLAdaptedAt_congr {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := X) D} {T : ℝ} {γ : ℝ → X}
    {P Q : ∀ s, TangentSpace ThreeModel (γ s)} {s : ℝ}
    (h : ∀ᶠ r in 𝓝 s, (P r : ThreeSpace) = Q r) (hP : IsLAdaptedAt S T γ P s) :
    IsLAdaptedAt S T γ Q s := by
  have hc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve (I := ThreeModel)
    (S.base.metric (T - s ^ 2)) Q P (Filter.EventuallyEq.refl _ _) (h.mono fun r hr => hr.symm)
  unfold IsLAdaptedAt at hP ⊢
  rw [show covDerivAlong (I := ThreeModel) (S.base.metric (T - s ^ 2)) γ Q s =
    covDerivAlong (I := ThreeModel) (S.base.metric (T - s ^ 2)) γ P s from hc, hP,
    show P s = Q s from h.self_of_nhds]

variable {H : ObservedHistory.{u}} {first last fst : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {hfst : first ≤ fst} {T w v : ℝ} {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T w p}

namespace LFamilyChain

variable (ch : H.LFamilyChain hle hfst T w v p Z₀)

open Classical in
def bump (k : ℕ) : ℝ → ℝ :=
  if hk : k < ch.n then
    Classical.choose (exists_bump_eq_one (ch.isOpen_K k) (ch.lt k hk).le (ch.piece_K k hk))
  else 0

theorem bump_spec {k : ℕ} (hk : k < ch.n) : ∃ δ > 0, ContDiff ℝ ∞ (ch.bump k) ∧
    (∀ s ∈ Ioo (ch.c k - δ) (ch.c (k + 1) + δ), ch.bump k s = 1) ∧
    (∀ s, s ∉ ch.K k → ∀ᶠ r in 𝓝 s, ch.bump k r = 0) ∧
    Ioo (ch.c k - δ) (ch.c (k + 1) + δ) ⊆ ch.K k := by
  have h := Classical.choose_spec
    (exists_bump_eq_one (ch.isOpen_K k) (ch.lt k hk).le (ch.piece_K k hk))
  simp only [bump, dif_pos hk]
  exact h

def familyDeriv (k : ℕ) (B : ThreeSpace) (s : ℝ) : ThreeSpace :=
  mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, s)) Z₀.1 B

def jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) : ch.toLWindowChain.Field :=
  fun k s => ch.bump k s • ch.familyDeriv k (chartModelBasis ThreeSpace i) s

theorem contMDiffAt_familyDeriv {k : ℕ} (B : ThreeSpace) {s : ℝ} (hs : s ∈ ch.K k) :
    ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t)
      (ch.familyDeriv k B t : TangentSpace ThreeModel (ch.γ k t)) :
        TangentBundle ThreeModel (ch.W k).X)) s := by
  have hβ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ThreeSpace)) ThreeModel ∞
      (Function.uncurry fun (t : ℝ) (Z : ThreeSpace) => ch.β k (Z, t))
        (s, (show ThreeSpace from Z₀.1)) := by
    have hat : ContMDiffAt (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (ch.β k)
        ((show ThreeSpace from Z₀.1), s) :=
      (ch.smooth k (Z₀.1, s) ⟨ch.mem_V k, hs⟩).contMDiffAt
        (((ch.isOpen_V k).prod (ch.isOpen_K k)).mem_nhds ⟨ch.mem_V k, hs⟩)
    exact hat.comp (s, (show ThreeSpace from Z₀.1)) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := ContMDiffAt.tangentMap_const_apply (m := ∞) (I := 𝓘(ℝ, ThreeSpace))
    (J := 𝓘(ℝ, ℝ)) (I' := ThreeModel) (M := ThreeSpace) (N := ℝ)
    (f := fun (t : ℝ) (Z : ThreeSpace) => ch.β k (Z, t)) (x := s) (show ThreeSpace from Z₀.1) B
    hβ (by simp)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(ch.isOpen_K k).mem_nhds hs] with t ht
  exact totalSpace_mk_eq_of_eq (ch.curve k t ht).symm _

theorem contMDiff_jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) {k : ℕ} (hk : k < ch.n) :
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t)
      (ch.jacobiField i k t) : TangentBundle ThreeModel (ch.W k).X)) := by
  obtain ⟨δ, -, hρ, -, hzero, -⟩ := ch.bump_spec hk
  intro t
  by_cases ht : t ∈ ch.K k
  · exact contMDiffAt_totalSpace_smul
      (V := fun t => (ch.familyDeriv k (chartModelBasis ThreeSpace i)
        t : TangentSpace ThreeModel (ch.γ k t))) hρ.contMDiff.contMDiffAt
      (ch.contMDiffAt_familyDeriv _ ht)
  · refine (contMDiffAt_totalSpace_zero (ch.contMDiff k).contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [hzero t ht] with r hr
    simp only [jacobiField, hr, zero_smul]
    rfl

theorem isLRegularizedJacobi_jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) {k : ℕ}
    (hk : k < ch.n) : ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧
      IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (ch.jacobiField i k) (Ioo a b) := by
  obtain ⟨δ, hδ, -, hone, -, hsub⟩ := ch.bump_spec hk
  refine ⟨ch.c k - δ, ch.c (k + 1) + δ, by linarith, by linarith, fun s hs => ?_⟩
  have hJ := isLRegularizedJacobi_mfderiv_of_contMDiffOn (ch.W k).S T (ch.isOpen_V k)
    (ch.isOpen_K k) (ch.smooth k) (ch.family k) (ch.mem_V k) (chartModelBasis ThreeSpace i) s
    (hsub hs)
  refine HasLRegularizedJacobiAt.congr_of_eqOn _ _ _ _ s _ isOpen_Ioo hs
    (fun r hr => ch.curve k r (hsub hr)) (fun r hr => ?_) hJ
  change _ = ch.bump k r • ch.familyDeriv k (chartModelBasis ThreeSpace i) r
  rw [hone r hr, one_smul]
  rfl

private theorem bump_zero (hn : 0 < ch.n) : ch.bump 0 0 = 1 := by
  obtain ⟨δ, hδ, -, hone, -, -⟩ := ch.bump_spec hn
  refine hone 0 ⟨?_, ?_⟩
  · rw [ch.c_zero]; linarith
  · have := ch.lt 0 hn
    rw [ch.c_zero] at this
    linarith

theorem jacobiField_zero (hn : 0 < ch.n) (i : Fin (Module.finrank ℝ ThreeSpace)) :
    ch.jacobiField i 0 0 = 0 := by
  obtain ⟨x, L, -, hbase⟩ := ch.base
  have h0K : (0 : ℝ) ∈ ch.K 0 := by
    have h := ch.piece_K 0 hn (left_mem_Icc.2 (ch.lt 0 hn).le)
    rwa [ch.c_zero] at h
  have hconst : (fun Z : ThreeSpace => ch.β 0 (Z, 0)) =ᶠ[𝓝 (show ThreeSpace from Z₀.1)]
      fun _ => x := by
    filter_upwards [(ch.isOpen_V 0).mem_nhds (ch.mem_V 0)] with Z hZ
    exact (hbase Z hZ 0 h0K).2.trans (lRegularizedCurve_zero _ _ _ _)
  have h0 : mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z : ThreeSpace => ch.β 0 (Z, 0))
      (show ThreeSpace from Z₀.1) = 0 :=
    hconst.mfderiv_eq.trans (mfderiv_const (x := show ThreeSpace from Z₀.1) (c := x))
  change ch.bump 0 0 • ch.familyDeriv 0 (chartModelBasis ThreeSpace i) 0 = 0
  simp only [familyDeriv, h0]
  change ch.bump 0 0 • (0 : ThreeSpace) = 0
  exact smul_zero _

private theorem familyDeriv_eq_historyLJacobiField {k : ℕ} (j : H.StageInterval (ch.lo k) (ch.hi k))
    (i : Fin (Module.finrank ℝ ThreeSpace)) {r : ℝ} (hrK : r ∈ ch.K k) (hr0 : 0 < r)
    (hr : r ∈ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val)) :
    (H.historyLJacobiField hle T w p Z₀ ⟨j.val, (hfst.trans (ch.first_le k)).trans j.property.1,
        j.property.2.trans (ch.le_last k)⟩ i r : ThreeSpace) =
      mfderiv ThreeModel ThreeModel ((ch.W k).f j) (ch.β k (Z₀.1, r))
        (ch.familyDeriv k (chartModelBasis ThreeSpace i) r) :=
  historyLJacobiField_eq_mfderiv (hlo := hfst.trans (ch.first_le k)) (hhi := ch.le_last k)
    (K := ch.K k ∩ Ioi 0) (ch.isOpen_V k) (ch.mem_V k) (ch.V_sub k)
    ((ch.isOpen_K k).inter isOpen_Ioi)
    ((ch.smooth k).mono (prod_mono subset_rfl inter_subset_left))
    (fun Z hZ j r hr => ch.rep k Z hZ j r ⟨hr.1.1, hr.2⟩) j i ⟨⟨hrK, hr0⟩, hr⟩

theorem mfderiv_jacobiField_eq {k : ℕ} (j : H.StageInterval (ch.lo k) (ch.hi k))
    (i : Fin (Module.finrank ℝ ThreeSpace)) {r : ℝ} (hrK : r ∈ ch.K k) (hr0 : 0 < r)
    (hr : r ∈ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val)) (hone : ch.bump k r = 1) :
    (mfderiv ThreeModel ThreeModel ((ch.W k).f j) (ch.γ k r) (ch.jacobiField i k r) :
      ThreeSpace) =
    H.historyLJacobiField hle T w p Z₀ ⟨j.val, (hfst.trans (ch.first_le k)).trans j.property.1,
        j.property.2.trans (ch.le_last k)⟩ i r := by
  rw [ch.familyDeriv_eq_historyLJacobiField j i hrK hr0 hr]
  refine mfderiv_apply_congr_point (ch.curve k r hrK).symm _ _ ?_
  change ch.bump k r • ch.familyDeriv k (chartModelBasis ThreeSpace i) r = _
  rw [hone, one_smul]

theorem node_facts {k : ℕ} (hk : k + 1 < ch.n) :
    ch.c (k + 1) ∈ ch.K k ∧ ch.c (k + 1) ∈ ch.K (k + 1) ∧ 0 < ch.c (k + 1) ∧
      (∀ᶠ s in 𝓝 (ch.c (k + 1)), ch.bump k s = 1) ∧
      (∀ᶠ s in 𝓝 (ch.c (k + 1)), ch.bump (k + 1) s = 1) := by
  have hk' : k < ch.n := Nat.lt_of_succ_lt hk
  obtain ⟨δ, hδ, -, hone, -, -⟩ := ch.bump_spec hk'
  obtain ⟨δ', hδ', -, hone', -, -⟩ := ch.bump_spec hk
  have hlt := ch.lt k hk'
  have hlt' := ch.lt (k + 1) hk
  refine ⟨ch.piece_K k hk' (right_mem_Icc.2 hlt.le), ch.piece_K (k + 1) hk
    (left_mem_Icc.2 hlt'.le), (ch.c_nonneg hk').trans_lt hlt, ?_, ?_⟩
  · exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hone
  · exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hone'

theorem isGlued_jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) :
    ch.toLWindowChain.IsGlued (ch.jacobiField i) := by
  intro k hk
  obtain ⟨hK, hK', h0, hone, hone'⟩ := ch.node_facts hk
  have hk' : k < ch.n := Nat.lt_of_succ_lt hk
  change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom hk')) (ch.γ k (ch.c (k + 1)))
      (ch.jacobiField i k (ch.c (k + 1))) : ThreeSpace) =
    mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1)))
      (ch.jacobiField i (k + 1) (ch.c (k + 1)))
  rw [ch.mfderiv_jacobiField_eq (ch.bottom hk') i hK h0 (ch.node k hk).1 hone.self_of_nhds,
    ch.mfderiv_jacobiField_eq (ch.top hk) i hK' h0 (ch.node k hk).2 hone'.self_of_nhds]
  rfl

private theorem mfderiv_covDerivAlong_jacobiField {k : ℕ} (hk : k < ch.n)
    (j : H.StageInterval (ch.lo k) (ch.hi k)) (i : Fin (Module.finrank ℝ ThreeSpace)) {r : ℝ}
    (hrK : r ∈ ch.K k) (hr0 : 0 < r)
    (hr : r ∈ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val)) (hone : ∀ᶠ s in 𝓝 r, ch.bump k s = 1) :
    (mfderiv ThreeModel ThreeModel ((ch.W k).f j) (ch.γ k r)
        (covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - r ^ 2)) (ch.γ k)
          (ch.jacobiField i k) r) : ThreeSpace) =
      covDerivAlong (I := ThreeModel) (H.stageMetric j.val (T - r ^ 2))
        (fun s => H.historyLCurveMap hle T w p Z₀ ⟨j.val,
          (hfst.trans (ch.first_le k)).trans j.property.1, j.property.2.trans (ch.le_last k)⟩ s
            Z₀.1)
        (fun s => H.historyLJacobiField hle T w p Z₀ ⟨j.val,
          (hfst.trans (ch.first_le k)).trans j.property.1, j.property.2.trans (ch.le_last k)⟩
            i s) r := by
  have hmet : ∀ x (a b : TangentSpace ThreeModel x),
      (H.stageMetric j.val (T - r ^ 2)).inner ((ch.W k).f j x)
        (mfderiv ThreeModel ThreeModel ((ch.W k).f j) x a)
        (mfderiv ThreeModel ThreeModel ((ch.W k).f j) x b) =
      ((ch.W k).S.base.metric (T - r ^ 2)).inner x a b := by
    intro x a b
    rw [(ch.W k).metric j r hr, localPullMetric_inner]
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (ch.γ k) r :=
    (ch.contMDiff k).mdifferentiableAt (by simp)
  have hV := differentiableAt_chartRepAt_of_contMDiff_two (I := ThreeModel)
    ((ch.contMDiff_jacobiField i hk).of_le (natCast_le_infty 2)) r
  rw [mfderiv_covDerivAlong_of_isLocalDiffeomorph _ _ ((ch.W k).localDiffeomorph j) hmet (ch.γ k)
    (ch.jacobiField i k) hγ hV]
  have hU : ∀ᶠ s in 𝓝 r, s ∈ ch.K k ∧ 0 < s ∧ s ∈ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val) :=
    ((ch.isOpen_K k).inter (isOpen_Ioi.inter isOpen_Ioo)).mem_nhds ⟨hrK, hr0, hr⟩
  refine DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve (I := ThreeModel) _
    _ _ ?_ ?_
  · filter_upwards [hU] with s hs
    rw [← ch.curve k s hs.1, historyLCurveMap_self]
    exact (ch.rep k Z₀.1 (ch.mem_V k) j s ⟨hs.1, hs.2.2⟩).symm
  · filter_upwards [hU, hone] with s hs hs1
    exact ch.mfderiv_jacobiField_eq j i hs.1 hs.2.1 hs.2.2 hs1

theorem isGlued_covDerivField_jacobiField (i : Fin (Module.finrank ℝ ThreeSpace)) :
    ch.toLWindowChain.IsGlued (ch.toLWindowChain.covDerivField (ch.jacobiField i)) := by
  intro k hk
  obtain ⟨hK, hK', h0, hone, hone'⟩ := ch.node_facts hk
  have hk' : k < ch.n := Nat.lt_of_succ_lt hk
  change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom hk')) (ch.γ k (ch.c (k + 1)))
      (covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - ch.c (k + 1) ^ 2)) (ch.γ k)
        (ch.jacobiField i k) (ch.c (k + 1))) : ThreeSpace) =
    mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1)))
      (covDerivAlong (I := ThreeModel) ((ch.W (k + 1)).S.base.metric (T - ch.c (k + 1) ^ 2))
        (ch.γ (k + 1)) (ch.jacobiField i (k + 1)) (ch.c (k + 1)))
  rw [ch.mfderiv_covDerivAlong_jacobiField hk' (ch.bottom hk') i hK h0 (ch.node k hk).1 hone,
    ch.mfderiv_covDerivAlong_jacobiField hk (ch.top hk) i hK' h0 (ch.node k hk).2 hone']
  rfl

private theorem exists_adapted_piece {k : ℕ} (hk : k < ch.n) {b : ℝ} (hb : ch.c (k + 1) = b)
    (V : TangentSpace ThreeModel (ch.γ k b)) :
    ∃ (P : ∀ s, TangentSpace ThreeModel (ch.γ k s)) (Ω : Set ℝ), IsOpen Ω ∧
      Icc (ch.c k) b ⊆ Ω ∧ ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
        (fun s => (TotalSpace.mk' ThreeSpace (ch.γ k s) (P s) :
          TangentBundle ThreeModel (ch.W k).X)) Ω ∧
      P b = V ∧ IsLAdapted (ch.W k).S T (ch.γ k) P Ω := by
  subst hb
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨a, b, ha, hb, hgeo⟩ := ch.geodesic k hk
  obtain ⟨P, Ω, hΩ, hsub, -, hP, hPb, hPad⟩ := exists_lAdaptedField_on_Icc (ch.W k).S
    (ch.W k).solution T (ch.γ k) (ch.contMDiff k) (ch.lt k hk).le isOpen_Ioo
    (fun r hr => ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩) (fun s hs => (hgeo s hs).1) V
  exact ⟨P, Ω, hΩ, hsub, hP, hPb, hPad⟩

private theorem exists_adaptedFrame_aux (hn : 0 < ch.n) : ∀ d, d < ch.n →
    ∃ P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field,
      (∀ l k, ch.n - 1 - d ≤ k → k < ch.n → ∃ Ω : Set ℝ, IsOpen Ω ∧
        Icc (ch.c k) (ch.c (k + 1)) ⊆ Ω ∧ ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
          (fun s => (TotalSpace.mk' ThreeSpace (ch.γ k s) (P l k s) :
            TangentBundle ThreeModel (ch.W k).X)) Ω ∧
        IsLAdapted (ch.W k).S T (ch.γ k) (P l k) Ω) ∧
      (∀ l k (hk : k + 1 < ch.n), ch.n - 1 - d ≤ k → ch.toLWindowChain.GluedAt (P l) hk) ∧
      ∀ l l', ((ch.W (ch.n - 1)).S.base.metric (T - ch.c ch.n ^ 2)).inner
        (ch.γ (ch.n - 1) (ch.c ch.n)) (P l (ch.n - 1) (ch.c ch.n))
          (P l' (ch.n - 1) (ch.c ch.n)) = if l = l' then 1 else 0 := by
  classical
  intro d
  induction d with
  | zero =>
    intro _
    have hk : ch.n - 1 < ch.n := Nat.sub_lt hn one_pos
    have hb : ch.c (ch.n - 1 + 1) = ch.c ch.n := by rw [Nat.sub_add_cancel hn]
    obtain ⟨basis, hbasis⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (I := ThreeModel) ((ch.W (ch.n - 1)).S.base.metric (T - ch.c ch.n ^ 2))
      (ch.γ (ch.n - 1) (ch.c ch.n))
    have hex := fun l : Fin (Module.finrank ℝ ThreeSpace) => ch.exists_adapted_piece hk hb
      (basis l)
    choose Q Ω hΩ hsub hQ hQb hQad using hex
    refine ⟨fun l => Function.update (fun _ _ => 0) (ch.n - 1) (Q l), fun l k hk1 hk2 => ?_,
      fun l k hk hk1 => absurd hk (by omega), fun l l' => ?_⟩
    · obtain rfl : k = ch.n - 1 := by omega
      refine ⟨Ω l, hΩ l, by rw [hb]; exact hsub l, ?_, ?_⟩ <;> simp only [Function.update_self]
      · exact hQ l
      · exact hQad l
    · simp only [Function.update_self, hQb]
      exact hbasis l l'
  | succ d ih =>
    intro hd
    obtain ⟨P, hP, hPg, hPon⟩ := ih (Nat.lt_of_succ_lt hd)
    set m := ch.n - 1 - (d + 1) with hmdef
    have hm1 : m + 1 < ch.n := by omega
    have hm : m < ch.n := Nat.lt_of_succ_lt hm1
    have hmeq : ch.n - 1 - d = m + 1 := by omega
    let e := ((ch.W m).localDiffeomorph (ch.bottom hm)).mfderivToContinuousLinearEquiv
      (by simp) (ch.γ m (ch.c (m + 1)))
    have hex := fun l : Fin (Module.finrank ℝ ThreeSpace) => ch.exists_adapted_piece hm rfl
      (e.symm (mfderiv ThreeModel ThreeModel ((ch.W (m + 1)).f (ch.top hm1))
        (ch.γ (m + 1) (ch.c (m + 1))) (P l (m + 1) (ch.c (m + 1)))))
    choose Q Ω hΩ hsub hQ hQb hQad using hex
    refine ⟨fun l => Function.update (P l) m (Q l), fun l k hk1 hk2 => ?_,
      fun l k hk hk1 => ?_, fun l l' => ?_⟩
    · rcases eq_or_ne k m with rfl | hkm
      · refine ⟨Ω l, hΩ l, hsub l, ?_, ?_⟩ <;> simp only [Function.update_self]
        · exact hQ l
        · exact hQad l
      · simp only [Function.update_of_ne hkm]
        exact hP l k (by omega) hk2
    · rcases eq_or_ne k m with rfl | hkm
      · have h1 : m + 1 ≠ m := by omega
        change (mfderiv ThreeModel ThreeModel ((ch.W m).f (ch.bottom (Nat.lt_of_succ_lt hk)))
            (ch.γ m (ch.c (m + 1))) (Function.update (P l) m (Q l) m (ch.c (m + 1))) :
            ThreeSpace) = mfderiv ThreeModel ThreeModel ((ch.W (m + 1)).f (ch.top hk))
            (ch.γ (m + 1) (ch.c (m + 1))) (Function.update (P l) m (Q l) (m + 1) (ch.c (m + 1)))
        rw [Function.update_self, Function.update_of_ne h1, hQb l]
        exact e.apply_symm_apply _
      · have h1 : k + 1 ≠ m := by omega
        have hg := hPg l k hk (by omega)
        change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)))
            (ch.γ k (ch.c (k + 1))) (Function.update (P l) m (Q l) k (ch.c (k + 1))) :
            ThreeSpace) = mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk))
            (ch.γ (k + 1) (ch.c (k + 1))) (Function.update (P l) m (Q l) (k + 1) (ch.c (k + 1)))
        rw [Function.update_of_ne hkm, Function.update_of_ne h1]
        exact hg
    · have h1 : ch.n - 1 ≠ m := by omega
      simp only [Function.update_of_ne h1]
      exact hPon l l'

theorem exists_adaptedFrame (hn : 0 < ch.n) :
    ∃ P : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field,
      (∀ l, ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
          (fun s => (TotalSpace.mk' ThreeSpace (ch.γ k s) (P l k s) :
            TangentBundle ThreeModel (ch.W k).X)) ∧
        ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧ IsLAdapted (ch.W k).S T (ch.γ k) (P l k) (Ioo a b)) ∧
      (∀ l, ch.toLWindowChain.IsGlued (P l)) ∧
      ∀ l l', ((ch.W (ch.n - 1)).S.base.metric (T - ch.c ch.n ^ 2)).inner
        (ch.γ (ch.n - 1) (ch.c ch.n)) (P l (ch.n - 1) (ch.c ch.n))
          (P l' (ch.n - 1) (ch.c ch.n)) = if l = l' then 1 else 0 := by
  classical
  obtain ⟨P, hP, hPg, hPon⟩ := ch.exists_adaptedFrame_aux hn (ch.n - 1) (Nat.sub_lt hn one_pos)
  have hex : ∀ l k, k < ch.n → ∃ ρ : ℝ → ℝ, ∃ δ > 0,
      (∀ s ∈ Ioo (ch.c k - δ) (ch.c (k + 1) + δ), ρ s = 1) ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t)
        (ρ t • P l k t) : TangentBundle ThreeModel (ch.W k).X)) ∧
      IsLAdapted (ch.W k).S T (ch.γ k) (P l k) (Ioo (ch.c k - δ) (ch.c (k + 1) + δ)) := by
    intro l k hk
    obtain ⟨Ω, hΩ, hsub, hsm, had⟩ := hP l k (by omega) hk
    obtain ⟨ρ, δ, hδ, hρ, hone, hzero, hIoo⟩ := exists_bump_eq_one hΩ (ch.lt k hk).le hsub
    refine ⟨ρ, δ, hδ, hone, fun t => ?_, fun s hs => had s (hIoo hs)⟩
    by_cases ht : t ∈ Ω
    · exact contMDiffAt_totalSpace_smul hρ.contMDiff.contMDiffAt
        ((hsm t ht).contMDiffAt (hΩ.mem_nhds ht))
    · refine (contMDiffAt_totalSpace_zero (ch.contMDiff k).contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hzero t ht] with r hr
      simp only [hr, zero_smul]
  choose ρ δ hδ hone hsm had using hex
  let P' : Fin (Module.finrank ℝ ThreeSpace) → ch.toLWindowChain.Field := fun l k s =>
    if hk : k < ch.n then ρ l k hk s • P l k s else 0
  have hP' : ∀ l k (hk : k < ch.n), ∀ s ∈ Ioo (ch.c k - δ l k hk) (ch.c (k + 1) + δ l k hk),
      P' l k s = P l k s := by
    intro l k hk s hs
    simp only [P', dif_pos hk, hone l k hk s hs, one_smul]
  have hnode : ∀ l k (hk : k < ch.n), P' l k (ch.c (k + 1)) = P l k (ch.c (k + 1)) :=
    fun l k hk => hP' l k hk _ ⟨by linarith [ch.lt k hk, hδ l k hk], by linarith [hδ l k hk]⟩
  have hnode' : ∀ l k (hk : k < ch.n), P' l k (ch.c k) = P l k (ch.c k) :=
    fun l k hk => hP' l k hk _ ⟨by linarith [hδ l k hk], by linarith [ch.lt k hk, hδ l k hk]⟩
  refine ⟨P', fun l k hk => ⟨?_, ch.c k - δ l k hk, ch.c (k + 1) + δ l k hk, by
    linarith [hδ l k hk], by linarith [hδ l k hk], fun s hs => ?_⟩, fun l k hk => ?_, ?_⟩
  · simp only [P', dif_pos hk]
    exact hsm l k hk
  · refine isLAdaptedAt_congr ?_ (had l k hk s hs)
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    rw [hP' l k hk r hr]
  · have hk' : k < ch.n := Nat.lt_of_succ_lt hk
    change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom hk')) (ch.γ k (ch.c (k + 1)))
        (P' l k (ch.c (k + 1))) : ThreeSpace) = mfderiv ThreeModel ThreeModel
        ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1)))
        (P' l (k + 1) (ch.c (k + 1)))
    rw [hnode l k hk', hnode' l (k + 1) hk]
    exact hPg l k hk (by omega)
  · have hk : ch.n - 1 < ch.n := Nat.sub_lt hn one_pos
    have hcn : ch.c ch.n = ch.c (ch.n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
    intro l l'
    have e1 : P' l (ch.n - 1) (ch.c ch.n) = P l (ch.n - 1) (ch.c ch.n) := by
      rw [hcn]; exact hnode l _ hk
    have e2 : P' l' (ch.n - 1) (ch.c ch.n) = P l' (ch.n - 1) (ch.c ch.n) := by
      rw [hcn]; exact hnode l' _ hk
    rw [e1, e2]
    exact hPon l l'

end LFamilyChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
