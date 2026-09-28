/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Chain

variable {n : ℕ} {M₁ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] {U : Set M₁}

theorem LocallyFinitePieceTower.eqOn_coreSpace_of_le {Y : Type*}
    (T : LocallyFinitePieceTower n M₁ U) {f : ℕ → M₁ → Y}
    (hf : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) {i j : ℕ} (hij : i ≤ j) :
    EqOn (f j) (f i) (T.coreSpace i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ k hik ih => exact fun x hx => (hf k (T.core_space_monotone hik hx)).trans (ih hx)

end Chain

section Defect

theorem Moise352Stages.exists_isPLHomeomorphInto_eqOn {n : ℕ} (H : Moise352Stages.{u} n)
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K)
    (hT : ∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (j : ℕ) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f (T.coreSpace j) ∧ EqOn f h (T.coreSpace j) := by
  obtain ⟨f, hstep, hstage, hclose⟩ :=
    H T hT hh (fun i : ℕ => 1 / ((i : ℝ) + 1)) fun _ => div_pos one_pos (by positivity)
  refine ⟨f j, hstage j, fun x hx => ?_⟩
  have hd : dist (f j x) (h x) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hcon
    obtain ⟨k, hjk, hmk⟩ : ∃ k : ℕ, j ≤ k ∧ m ≤ k :=
      ⟨max j m, le_max_left j m, le_max_right j m⟩
    have hxi : x ∈ T.coreSpace k := T.core_space_monotone hjk hx
    have heq : f k x = f j x := T.eqOn_coreSpace_of_le hstep hjk hx
    have hlt : dist (f j x) (h x) < 1 / ((k : ℝ) + 1) := by
      rw [← heq]
      exact hclose k x hxi
    have hcast : ((m : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
      have hc : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmk
      linarith
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hcast
    linarith
  exact dist_le_zero.mp hd

end Defect

private noncomputable def quarterRunningMin (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0 / 4
  | i + 1 => min (quarterRunningMin d i) (d (i + 1) / 4)

private theorem exists_antitone_pos_four_mul_le_of_forall_pos {d : ℕ → ℝ} (hd : ∀ i, 0 < d i) :
    ∃ ε : ℕ → ℝ, (∀ i, 0 < ε i) ∧ Antitone ε ∧ ∀ i, 4 * ε i ≤ d i := by
  refine ⟨quarterRunningMin d, ?_, antitone_nat_of_succ_le fun i => min_le_left _ _, ?_⟩
  · intro i
    induction i with
    | zero => exact div_pos (hd 0) (by norm_num)
    | succ k ih => exact lt_min ih (div_pos (hd (k + 1)) (by norm_num))
  · intro i
    cases i with
    | zero =>
      have h0 : quarterRunningMin d 0 = d 0 / 4 := rfl
      rw [h0]
      linarith
    | succ k =>
      have h1 : quarterRunningMin d (k + 1) ≤ d (k + 1) / 4 := min_le_right _ _
      linarith

section Obligation

def Moise352StageStep (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ {φ : M₁ → ℝ}, (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x) →
      (∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace 0) ∧ InjOn f (T.coreSpace 0) ∧
          ∀ x ∈ T.coreSpace 0, dist (f x) (h x) < φ x) ∧
        ∀ (i : ℕ) (g : M₁ → M₂), IsPLHomeomorphInto n g (T.coreSpace i) →
          (∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) →
          ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧
            InjOn f (T.coreSpace (i + 1)) ∧ EqOn f g (T.coreSpace i) ∧
            ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x

end Obligation

section Reduction

theorem moise352_of_stageStep {n : ℕ} (H : Moise352StageStep.{u} n) : Moise352.{u} n := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  obtain ⟨T, hT⟩ := hK
  choose ρ hρpos hρsep using fun i => T.exists_pos_le_dist_coreSpace hh i
  have hcex : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x := by
    intro i
    rcases (T.coreSpace i).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [he] at hx
      exact absurd hx (notMem_empty x)
    · obtain ⟨x₀, hx₀, hle⟩ := (T.isCompact_core_space i).exists_isMinOn hne
        (hφ.mono (T.core_space_subset_union i))
      exact ⟨φ x₀, hpos x₀ (T.core_space_subset_union i hx₀),
        fun x hx => isMinOn_iff.mp hle x hx⟩
  choose c hcpos hcle using hcex
  obtain ⟨ε, hεpos, hεanti, hεd⟩ := exists_antitone_pos_four_mul_le_of_forall_pos
    (d := fun i => min (ρ i) (c i)) fun i => lt_min (hρpos i) (hcpos i)
  obtain ⟨β, hβ⟩ : ∃ β : M₁ → ℝ, ∀ x ∈ K, ∃ i, x ∈ T.coreSpace i ∧ β x = ε i ∧
      ∀ j, x ∈ T.coreSpace j → i ≤ j := by
    refine ⟨fun x => if hx : ∃ i, x ∈ T.coreSpace i then ε (Nat.find hx) else 1, ?_⟩
    intro x hx
    have hex : ∃ i, x ∈ T.coreSpace i := T.exists_mem_core_space hx
    exact ⟨Nat.find hex, Nat.find_spec hex, dite_eq_left hex, fun j hj => Nat.find_min' hex hj⟩
  have hβstage : ∀ i, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ T.coreSpace i, b ≤ β x := by
    refine fun i => ⟨ε i, hεpos i, fun x hx => ?_⟩
    obtain ⟨j, -, hβx, hmin⟩ := hβ x (T.core_space_subset_union i hx)
    rw [hβx]
    exact hεanti (hmin i hx)
  obtain ⟨Hbase, Hstep⟩ := H T hT hh (φ := β) hβstage
  obtain ⟨u₀, hu₀pl, hu₀inj, hu₀d⟩ := Hbase
  have hu₀ : IsPLHomeomorphInto n u₀ (T.coreSpace 0) :=
    hu₀pl.isPLHomeomorphInto (T.isCompact_core_space 0) hu₀inj
  have hnext : ∀ (i : ℕ) (g : M₁ → M₂), ∃ v : M₁ → M₂,
      IsPLHomeomorphInto n g (T.coreSpace i) →
        (∀ x ∈ T.coreSpace i, dist (g x) (h x) < β x) →
        IsPLHomeomorphInto n v (T.coreSpace (i + 1)) ∧ EqOn v g (T.coreSpace i) ∧
          ∀ x ∈ T.coreSpace (i + 1), dist (v x) (h x) < β x := by
    intro i g
    by_cases hg : IsPLHomeomorphInto n g (T.coreSpace i) ∧
        ∀ x ∈ T.coreSpace i, dist (g x) (h x) < β x
    · obtain ⟨v, hvpl, hvinj, hveq, hvd⟩ := Hstep i g hg.1 hg.2
      exact ⟨v, fun _ _ => ⟨hvpl.isPLHomeomorphInto (T.isCompact_core_space (i + 1)) hvinj,
        hveq, hvd⟩⟩
    · exact ⟨h, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
  choose G hG using hnext
  obtain ⟨f, hf0, hfsucc⟩ : ∃ f : ℕ → M₁ → M₂, f 0 = u₀ ∧ ∀ i, f (i + 1) = G i (f i) :=
    ⟨fun i => Nat.rec (motive := fun _ => M₁ → M₂) u₀ (fun k v => G k v) i, rfl, fun _ => rfl⟩
  have hinv : ∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i) ∧
      ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < β x := by
    intro i
    induction i with
    | zero =>
      rw [hf0]
      exact ⟨hu₀, hu₀d⟩
    | succ k ih =>
      have hk := hG k (f k) ih.1 ih.2
      rw [hfsucc k]
      exact ⟨hk.1, hk.2.2⟩
  have hstepEq : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i) := by
    intro i
    rw [hfsucc i]
    exact (hG i (f i) (hinv i).1 (hinv i).2).2.1
  have hunif : ∀ x ∈ K, ∃ i, x ∈ T.coreSpace i ∧ ∃ r : ℝ, 3 * β x < r ∧
      ∀ z ∈ K \ T.coreSpace i, r ≤ dist (h z) (h x) ∧ 3 * β z < r := by
    intro x hx
    obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
    refine ⟨i + 2, T.core_space_monotone (by omega) hxi, ρ i, ?_, fun z hz => ⟨?_, ?_⟩⟩
    · have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : 0 < ε i := hεpos i
      rw [hβx]
      linarith
    · exact hρsep i x hxi z hz
    · obtain ⟨k, hzk, hβz, -⟩ := hβ z hz.1
      have hik : i ≤ k := by
        by_contra hcon
        exact hz.2 (T.core_space_monotone (by omega) hzk)
      have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : ε k ≤ ε i := hεanti hik
      have h4 : 0 < ε k := hεpos k
      rw [hβz]
      linarith
  obtain ⟨g, hg, hgd⟩ := T.exists_isPLHomeomorphInto_of_stages hstepEq (fun i => (hinv i).1)
    (fun i => (hinv i).2) hunif
  refine ⟨g, hg, fun x hx => (hgd x hx).trans ?_⟩
  obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
  have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
  have h2 : min (ρ i) (c i) ≤ c i := min_le_right _ _
  have h3 : c i ≤ φ x := hcle i x hxi
  have h4 : 0 < ε i := hεpos i
  rw [hβx]
  linarith

end Reduction

section NonVacuity

theorem LocallyFinitePieceTower.coreSpace_ofPiece {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X} (P : PLPiece n X Y) (i : ℕ) :
    (LocallyFinitePieceTower.ofPiece P).coreSpace i = Y :=
  P.piece.bijOn.image_eq

theorem LocallyFinitePieceTower.exists_isPLOn_injOn_eqOn_dist_lt_of_coreSpace_succ_subset
    {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] {K : Set M₁}
    (T : LocallyFinitePieceTower n M₁ K) {i : ℕ}
    (hsub : T.coreSpace (i + 1) ⊆ T.coreSpace i) {g h : M₁ → M₂} {φ : M₁ → ℝ}
    (hg : IsPLHomeomorphInto n g (T.coreSpace i))
    (hd : ∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧ InjOn f (T.coreSpace (i + 1)) ∧
      EqOn f g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x := by
  have heq : T.coreSpace (i + 1) = T.coreSpace i :=
    Subset.antisymm hsub (T.core_space_monotone (Nat.le_succ i))
  refine ⟨g, ?_, ?_, fun _ _ => rfl, fun x hx => hd x (hsub hx)⟩
  · rw [heq]
    exact hg.isPLOn
  · rw [heq]
    exact hg.injOn

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
