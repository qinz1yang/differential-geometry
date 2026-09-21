import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLocallyClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Real

set_option autoImplicit false

namespace DifferentialGeometry.Analysis
open Filter Set Topology
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]

theorem arzela_ascoli_isCompact_closure_of_pointwise_compact
    {Y : Type*} [UniformSpace Y] [T2Space Y]
    (f : Nat -> C(X, Y))
    (hequi : Equicontinuous (fun k => (f k : X -> Y)))
    (hpoint : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ k, f k x ∈ Q) :
    IsCompact (closure (Set.range f : Set C(X, Y))) := by
  classical
  have : CompactlyCoherentSpace X := inferInstance
  have hclosedEmbedding :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
          (fun g : C(X, Y) => (g : X -> Y))) := by
    refine ⟨⟨⟨?_⟩, DFunLike.coe_injective⟩, ?_⟩
    · change ContinuousMap.compactOpen =
        TopologicalSpace.induced ContinuousMap.toUniformOnFunIsCompact _
      unfold UniformOnFun.topologicalSpace
      rw [← (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
          (α := X) (β := Y)).isInducing.eq_induced]
      unfold ContinuousMap.compactConvergenceUniformSpace
      rfl
    · rw [show
          Set.range
              (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
                (fun g : C(X, Y) => (g : X -> Y))) =
            {g : UniformOnFun X Y {K : Set X | IsCompact K} |
              Continuous (UniformOnFun.toFun {K : Set X | IsCompact K} g)} by
          exact ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous
        (β := Y) (𝔖 := {K : Set X | IsCompact K})
        CompactlyCoherentSpace.isCoherentWith
  have hEq :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        EquicontinuousOn
          ((fun g : C(X, Y) => (g : X -> Y)) ∘
            ((↑) : {g : C(X, Y) // g ∈ Set.range f} -> C(X, Y))) K := by
    intro K _hK
    let idx : {g : C(X, Y) // g ∈ Set.range f} -> Nat :=
      fun g => Classical.choose g.2
    have hidx :
        forall g : {g : C(X, Y) // g ∈ Set.range f}, f (idx g) = g.1 :=
      fun g => Classical.choose_spec g.2
    have hglobal :
        Equicontinuous (fun g : {g : C(X, Y) // g ∈ Set.range f} =>
          (g.1 : X -> Y)) := by
      have hsub := hequi.comp idx
      have hfun :
          ((fun k : Nat => (f k : X -> Y)) ∘ idx) =
            (fun g : {g : C(X, Y) // g ∈ Set.range f} => (g.1 : X -> Y)) := by
        funext g x
        change f (idx g) x = g.1 x
        rw [hidx g]
      simpa [hfun] using hsub
    simpa [Function.comp_def] using hglobal.equicontinuousOn K
  have hPoint :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        forall x : X, x ∈ K ->
        exists Q : Set Y, IsCompact Q ∧
          forall i : C(X, Y), i ∈ (Set.range f : Set C(X, Y)) ->
            ((fun g : C(X, Y) => (g : X -> Y)) i) x ∈ Q := by
    intro _K _hK x _hx
    obtain ⟨Q, hQ, hx⟩ := hpoint x
    refine ⟨Q, hQ, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hx k
  have hcompact : IsCompact (closure (Set.range f : Set C(X, Y))) := by
    exact
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (X := X) (α := Y) (ι := C(X, Y))
        (𝔖 := {K : Set X | IsCompact K})
        (F := fun g : C(X, Y) => (g : X -> Y))
        (fun K hK => hK) hclosedEmbedding
        (s := Set.range f) hEq hPoint
  exact hcompact

theorem arzela_ascoli_subseq_tendsto_of_pointwise_compact
    [SigmaCompactSpace X]
    {Y : Type*} [UniformSpace Y] [T2Space Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (f : ℕ → C(X, Y))
    (hequi : Equicontinuous (fun k => (f k : X → Y)))
    (hpoint : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ᶠ k in atTop, f k x ∈ Q) :
    ∃ (phi : ℕ → ℕ) (g : C(X, Y)),
      StrictMono phi ∧ Tendsto (fun n => f (phi n)) atTop (𝓝 g) := by
  have hpointAll : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ k, f k x ∈ Q := by
    intro x
    obtain ⟨Q, hQ, htail⟩ := hpoint x
    obtain ⟨N, hN⟩ := eventually_atTop.mp htail
    refine ⟨Q ∪ (fun k => f k x) '' Iio N, hQ.union ((finite_Iio N).image _).isCompact, ?_⟩
    intro k
    by_cases hk : N ≤ k
    · exact Or.inl (hN k hk)
    · exact Or.inr ⟨k, lt_of_not_ge hk, rfl⟩
  have hmem : ∀ n, f n ∈ closure (Set.range f : Set C(X, Y)) :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨g, _, phi, hphi, hconv⟩ :=
    (arzela_ascoli_isCompact_closure_of_pointwise_compact f hequi hpointAll).tendsto_subseq hmem
  exact ⟨phi, g, hphi, hconv⟩

end DifferentialGeometry.Analysis

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set Topology
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [T2Space X]

omit [T2Space X] in
theorem arzelaAscoli_subseq_tendsto
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧ Tendsto (fun n => f (phi n)) atTop (𝓝 g) := by
  apply DifferentialGeometry.Analysis.arzela_ascoli_subseq_tendsto_of_pointwise_compact f hequi
  intro x
  obtain ⟨B, hB⟩ := hbdd x
  exact ⟨Icc (-B) B, isCompact_Icc, Eventually.of_forall fun k => abs_le.mp (hB ⟨k, rfl⟩)⟩

omit [T2Space X] in
theorem arzelaAscoli_subseq_tendstoUniformlyOnCompacts
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  rcases arzelaAscoli_subseq_tendsto (X := X) f hequi hbdd with
    ⟨phi, g, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp htendsto)⟩

section VectorTarget

variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V]

omit [SigmaCompactSpace X] [T2Space X] in
theorem arzelaAscoli_isCompact_closure
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    IsCompact (closure (Set.range f : Set C(X, V))) := by
  apply DifferentialGeometry.Analysis.arzela_ascoli_isCompact_closure_of_pointwise_compact f hequi
  intro x
  obtain ⟨B, hB⟩ := hbdd x
  exact ⟨Metric.closedBall 0 B, isCompact_closedBall 0 B,
    fun k => mem_closedBall_zero_iff.mpr (hB k)⟩

omit [T2Space X] in
theorem arzelaAscoli_subseq_vec
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    exists (phi : Nat -> Nat) (g : C(X, V)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  have hmem : forall n : Nat, f n ∈ closure (Set.range f : Set C(X, V)) :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases (arzelaAscoli_isCompact_closure f hequi hbdd).tendsto_subseq hmem with
    ⟨g, _hg, phi, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
        (by simpa [Function.comp_def] using htendsto)⟩

end VectorTarget

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.Analysis

open Filter Set Topology
open scoped Topology BoundedContinuousFunction

theorem arzela_subseq_compact
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] [T2Space Y]
    (K : Set Y) (hK : IsCompact K) (f : Nat -> C(X, Y))
    (hval : forall n x, f n x ∈ K)
    (hequi : Equicontinuous (fun n => (f n : X -> Y))) :
    exists (phi : Nat -> Nat) (g : C(X, Y)),
      StrictMono phi ∧ TendstoUniformly (fun n => f (phi n)) g atTop := by
  classical
  let fb : Nat → (X →ᵇ Y) := fun n => BoundedContinuousFunction.mkOfCompact (f n)
  let A : Set (X →ᵇ Y) := Set.range fb
  have hEq : Equicontinuous ((↑) : A -> X -> Y) := by
    let idx : A -> Nat := fun q => Classical.choose q.2
    have hidx : forall q : A, fb (idx q) = q.1 :=
      fun q => Classical.choose_spec q.2
    have hsub := hequi.comp idx
    have hfun :
        ((fun n : Nat => (f n : X -> Y)) ∘ idx) =
          (fun q : A => (q.1 : X -> Y)) := by
      funext q x
      calc
        f (idx q) x = fb (idx q) x := rfl
        _ = q.1 x := by rw [hidx q]
    simpa only [hfun] using hsub
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli K hK A
      (by
        intro q x hq
        rcases hq with ⟨n, rfl⟩
        exact hval n x)
      hEq
  have hmem : forall n : Nat, fb n ∈ closure A :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases hcompact.tendsto_subseq hmem with
    ⟨g, _hg, phi, hphi, htendsto⟩
  refine ⟨phi, g.toContinuousMap, hphi, ?_⟩
  have huniform : TendstoUniformly (fun n => fb (phi n)) g atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (by simpa only [Function.comp_def] using htendsto)
  change TendstoUniformly (fun n x => f (phi n) x) (fun x => g x) atTop
  change TendstoUniformly (fun n x => fb (phi n) x) (fun x => g x) atTop at huniform
  simpa only [fb, BoundedContinuousFunction.mkOfCompact_apply] using huniform

alias arzela_ascoli_isCompact_closure :=
  CheegerGromovCompactness.arzelaAscoli_isCompact_closure

alias arzela_ascoli_subseq_tendsto_locally_uniformly :=
  CheegerGromovCompactness.arzelaAscoli_subseq_vec

end DifferentialGeometry.Analysis

namespace ArzelaAscoli
open Filter Set
open scoped Topology NNReal ENNReal

variable {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]

theorem exists_lipschitz_subseq_limit_of_eventually_lipschitzOn_closedBall
    (f : ℕ → X → ℝ) (p : X) (K : ℝ≥0)
    (hLip : ∀ R : ℝ, 0 ≤ R → ∀ᶠ n in atTop,
      LipschitzOnWith K (f n) (Metric.closedBall p R))
    (hbdd : ∃ B : ℝ, ∀ᶠ n in atTop, |f n p| ≤ B) :
    ∃ (phi : ℕ → ℕ) (g : C(X, ℝ)), StrictMono phi ∧ LipschitzWith K g ∧
      ∀ A : Set X, IsCompact A → TendstoUniformlyOn (fun n => f (phi n)) g atTop A := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hB
  choose N hN using fun n : ℕ => eventually_atTop.mp (hLip n (Nat.cast_nonneg n))
  let u : ℕ → ℕ := fun n => max n (max (N n) Nb)
  obtain ⟨rho, hrho, hurho⟩ := strictMono_subseq_of_id_le (u := u) (fun n => le_max_left _ _)
  let psi := u ∘ rho
  have hpsi : StrictMono psi := hurho
  have hLipPsi (n : ℕ) : LipschitzOnWith K (f (psi n)) (Metric.closedBall p (n : ℝ)) := by
    have hindex : N (rho n) ≤ psi n := (le_max_left _ _).trans (le_max_right _ _)
    apply (hN (rho n) (psi n) hindex).mono
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hrho.id_le n)
  choose g hg heq using fun n => (hLipPsi n).extend_real
  let G : ℕ → C(X, ℝ) := fun n => ⟨g n, (hg n).continuous⟩
  have hbase (n : ℕ) : |g n p| ≤ B := by
    rw [← heq n (Metric.mem_closedBall_self (Nat.cast_nonneg n))]
    apply hNb
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hbound (x : X) : BddAbove (range fun n => |G n x|) := by
    refine ⟨(K : ℝ) * dist x p + B, ?_⟩
    rintro _ ⟨n, rfl⟩
    change |g n x| ≤ _
    calc
      _ ≤ |g n x - g n p| + |g n p| := by
        simpa only [sub_add_cancel] using abs_add_le (g n x - g n p) (g n p)
      _ ≤ (K : ℝ) * dist x p + B :=
        add_le_add (by simpa only [Real.dist_eq] using (hg n).dist_le_mul x p) (hbase n)
  have hequi : Equicontinuous (fun n => (G n : X → ℝ)) :=
    (LipschitzWith.uniformEquicontinuous _ K hg).equicontinuous
  obtain ⟨sigma, limit, hsigma, hconv⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.arzelaAscoli_subseq_tendstoUniformlyOnCompacts
      G hequi hbound
  have hpoint (x : X) : Tendsto (fun n => G (sigma n) x) atTop (𝓝 (limit x)) :=
    (hconv {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hlimit : LipschitzWith K limit := LipschitzWith.of_dist_le_mul fun x y =>
    le_of_tendsto ((hpoint x).dist (hpoint y))
      (Eventually.of_forall fun n => (hg (sigma n)).dist_le_mul x y)
  refine ⟨psi ∘ sigma, limit, hpsi.comp hsigma, hlimit, ?_⟩
  intro A hA
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall p
  have hlarge : ∀ᶠ n in atTop, R ≤ (sigma n : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp hsigma.tendsto_atTop) (eventually_ge_atTop R))
  apply (hconv A hA).congr
  filter_upwards [hlarge] with n hn
  intro x hx
  exact (heq (sigma n) (Metric.closedBall_subset_closedBall hn (hR hx))).symm


theorem exists_lipschitz_subseq_limit_on_Ico
    {Y : Type*} [EMetricSpace Y] (f : ℕ → ℝ → Y) {rho : ℝ} {K : ℝ≥0}
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 ≤ τ n) (hτρ : Tendsto τ atTop (𝓝 rho))
    (hLip : ∀ C : ℝ≥0, K < C → ∀ᶠ n in atTop,
      LipschitzOnWith C (f n) (Icc 0 (τ n)))
    (hpoint : ∀ t ∈ Ico 0 rho, ∃ Q : Set Y, IsCompact Q ∧ ∀ᶠ n in atTop, f n t ∈ Q) :
    ∃ (phi : ℕ → ℕ) (g : C(Ico 0 rho, Y)), StrictMono phi ∧ LipschitzWith K g ∧
      ∀ A : Set (Ico 0 rho), IsCompact A →
        TendstoUniformlyOn (fun n (t : Ico 0 rho) => f (phi n) t) g atTop A := by
  classical
  let : LocallyCompactSpace (Ico (0 : ℝ) rho) := isLocallyClosed_Ico.locallyCompactSpace
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hLip (K + 1) (lt_add_one K))
  let F : ℕ → ℝ → Y := fun n t =>
    if N ≤ n then f n (projIcc 0 (τ n) (hτ n) t) else f 0 0
  have hFLip (n : ℕ) : LipschitzWith (K + 1) (F n) := by
    by_cases hn : N ≤ n
    · simpa only [F, if_pos hn, mul_one, Function.comp_def, Set.domRestrict_apply] using
        (hN n hn).to_restrict.comp (LipschitzWith.projIcc (hτ n))
    · simpa only [F, if_neg hn] using ((LipschitzWith.const (f 0 0)).weaken (show 0 ≤ K + 1 from zero_le))
  let G : ℕ → C(Ico 0 rho, Y) :=
    fun n => ⟨fun t => F n t, (hFLip n).continuous.comp continuous_subtype_val⟩
  have heq (t : Ico (0 : ℝ) rho) : ∀ᶠ n in atTop, G n t = f n t := by
    filter_upwards [eventually_ge_atTop N, hτρ.eventually (eventually_gt_nhds t.2.2)] with n hn ht
    change (if N ≤ n then _ else _) = _
    rw [if_pos hn, projIcc_of_mem (hτ n) ⟨t.2.1, ht.le⟩]
  have hGpoint (t : Ico (0 : ℝ) rho) :
      ∃ Q : Set Y, IsCompact Q ∧ ∀ᶠ n in atTop, G n t ∈ Q := by
    obtain ⟨Q, hQ, ht⟩ := hpoint t t.2
    refine ⟨Q, hQ, ?_⟩
    filter_upwards [heq t, ht] with n hn hmem
    rwa [hn]
  have hequi : Equicontinuous (fun n => (G n : Ico 0 rho → Y)) :=
    (LipschitzWith.uniformEquicontinuous _ (K + 1)
      (fun n => (hFLip n).restrict _)).equicontinuous
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_ascoli_subseq_tendsto_of_pointwise_compact G hequi hGpoint
  have hpointConv (t : Ico (0 : ℝ) rho) :
      Tendsto (fun n => f (phi n) t) atTop (𝓝 (g t)) := by
    have hc := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv
      {t} isCompact_singleton).tendsto_at (mem_singleton t)
    exact hc.congr' (hphi.tendsto_atTop (heq t))
  have hlimit : LipschitzWith K g := by
    intro x y
    have hC (C : ℝ≥0) (hC : K < C) : edist (g x) (g y) ≤ C * edist x y := by
      apply le_of_tendsto ((hpointConv x).edist (hpointConv y))
      filter_upwards [hphi.tendsto_atTop (hLip C hC),
        hphi.tendsto_atTop (hτρ.eventually (eventually_gt_nhds x.2.2)),
        hphi.tendsto_atTop (hτρ.eventually (eventually_gt_nhds y.2.2))] with n hn hx hy
      exact hn ⟨x.2.1, hx.le⟩ ⟨y.2.1, hy.le⟩
    have hc : Tendsto (fun C : ℝ≥0 => (C : ℝ≥0∞) * edist x y)
        (𝓝[>] K) (𝓝 ((K : ℝ≥0∞) * edist x y)) :=
      ENNReal.Tendsto.mul_const
        (ENNReal.continuous_coe.continuousAt.tendsto.mono_left inf_le_left)
        (Or.inr (edist_ne_top x y))
    exact ge_of_tendsto hc (eventually_nhdsWithin_iff.mpr (Eventually.of_forall hC))
  refine ⟨phi, g, hphi, hlimit, ?_⟩
  intro A hA
  apply (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv A hA).congr
  by_cases hAne : A.Nonempty
  · obtain ⟨t, htA, htmax⟩ := hA.exists_isGreatest hAne
    filter_upwards [hphi.tendsto_atTop (eventually_ge_atTop N),
      hphi.tendsto_atTop (hτρ.eventually (eventually_gt_nhds t.2.2))] with n hn ht
    intro x hx
    change N ≤ phi n at hn
    change (t : ℝ) < τ (phi n) at ht
    change (if N ≤ phi n then _ else _) = _
    rw [if_pos hn, projIcc_of_mem (hτ (phi n)) ⟨x.2.1, (show (x : ℝ) ≤ t from htmax hx).trans ht.le⟩]
  · exact Eventually.of_forall fun _ x hx => (hAne ⟨x, hx⟩).elim

end ArzelaAscoli
