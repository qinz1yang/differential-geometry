import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Logic.Encodable.Basic

section

open Filter MeasureTheory
open scoped ENNReal Topology

private theorem exists_seq_tendsto_ae_nat
    {A : Type*} {X : ℕ → Type*} [MeasurableSpace A] [∀ i, PseudoEMetricSpace (X i)]
    {μ : Measure A} {f : ℕ → ∀ i, A → X i} {g : ∀ i, A → X i}
    (hfg : ∀ i, TendstoInMeasure μ (fun n => f n i) atTop (g i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂μ, ∀ i, Tendsto (fun n => f (φ n) i z) atTop (𝓝 (g i z)) := by
  classical
  let N : ℕ → ℕ → ℕ := fun i => ExistsSeqTendstoAe.seqTendstoAeSeq (hfg i)
  let T : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup (fun i => N i n)
  let φ : ℕ → ℕ := Nat.rec (T 0) (fun n k => max (T (n + 1)) (k + 1))
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (lt_add_one (φ n)).trans_le (le_max_right _ _)
  have hT : ∀ n, T n ≤ φ n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hN : ∀ i n, i ≤ n → N i n ≤ φ n := by
    intro i n hin
    exact (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))).trans (hT n)
  refine ⟨φ, hφ, ae_all_iff.mpr fun i => ?_⟩
  let S : ℕ → Set A := fun n =>
    {z | (2 : ℝ≥0∞)⁻¹ ^ (n + i) ≤ edist (f (φ (n + i)) i z) (g i z)}
  have hS : ∀ n, μ (S n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hb := ExistsSeqTendstoAe.seqTendstoAeSeq_spec (hfg i) (n + i)
      (φ (n + i)) (hN i (n + i) (Nat.le_add_left i n))
    refine hb.trans ?_
    rw [pow_add]
    exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (by norm_num))
  have hsum : (∑' n, μ (S n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hS)
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      ENNReal.ofNat_ne_top (n := 2)
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (n + i)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)).comp
      (tendsto_add_atTop_nat i)
  filter_upwards [ae_eventually_notMem hsum] with z hz
  apply (tendsto_add_atTop_iff_nat i).mp
  apply EMetric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hz, hpow.eventually (Iio_mem_nhds hε)] with n hn hεn
  exact (lt_of_not_ge hn).trans hεn

theorem MeasureTheory.exists_seq_tendsto_ae_of_countable_tendstoInMeasure
    {A I : Type*} {X : I → Type*} [MeasurableSpace A] [Countable I]
    [∀ i, PseudoEMetricSpace (X i)]
    {μ : Measure A} {f : ℕ → ∀ i, A → X i} {g : ∀ i, A → X i}
    (hfg : ∀ i, TendstoInMeasure μ (fun n => f n i) atTop (g i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂μ, ∀ i, Tendsto (fun n => f (φ n) i z) atTop (𝓝 (g i z)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    exact ⟨id, strictMono_id, Filter.Eventually.of_forall fun _ i => isEmptyElim i⟩
  | inr hI =>
    let : Encodable I := Encodable.ofCountable I
    let i₀ : I := Classical.choice hI
    let e : ℕ → I := fun n => (Encodable.decode n).getD i₀
    have he : Function.Surjective e := Encodable.surjective_decode_getD I i₀
    obtain ⟨φ, hφ, hlim⟩ := exists_seq_tendsto_ae_nat (fun n => hfg (e n))
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hlim] with z hz i
    obtain ⟨n, rfl⟩ := he i
    exact hz n

end
