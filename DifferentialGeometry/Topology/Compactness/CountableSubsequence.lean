import Mathlib.Topology.Sequences
import Mathlib.Logic.Encodable.Basic

section

open Filter
open scoped Topology

private theorem exists_subseq_tendsto_nat
    {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] (f : ℕ → ∀ i, X i)
    (hf : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧
        ∃ x : X i, Tendsto (fun n => f (σ (τ n)) i) atTop (𝓝 x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ x : X i, Tendsto (fun n => f (φ n) i) atTop (𝓝 x) := by
  classical
  let S := {σ : ℕ → ℕ // StrictMono σ}
  let step : ℕ → S → S := fun i σ =>
    ⟨σ.val ∘ (hf i σ.val σ.property).choose,
      σ.property.comp (hf i σ.val σ.property).choose_spec.1⟩
  let state : ℕ → S := Nat.rec ⟨id, strictMono_id⟩ step
  let φ : ℕ → ℕ := fun n => (state n).val n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    apply (state n).property
    exact (Nat.lt_succ_self n).trans_le
      ((hf n (state n).val (state n).property).choose_spec.1.id_le (n + 1))
  have htail : ∀ i n, i ≤ n → ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (state n).val = (state i).val ∘ τ := by
    intro i n hin
    induction n, hin using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ n hin ih =>
      obtain ⟨τ, hτ, heq⟩ := ih
      let ρ := (hf n (state n).val (state n).property).choose
      have hρ : StrictMono ρ := (hf n (state n).val (state n).property).choose_spec.1
      refine ⟨τ ∘ ρ, hτ.comp hρ, ?_⟩
      change (state n).val ∘ ρ = (state i).val ∘ (τ ∘ ρ)
      rw [heq]
      rfl
  refine ⟨φ, hφ, fun i => ?_⟩
  obtain ⟨x, hx⟩ := (hf i (state i).val (state i).property).choose_spec.2
  have hlim : Tendsto (fun n => f ((state (i + 1)).val n) i) atTop (𝓝 x) := hx
  refine ⟨x, tendsto_def.mpr fun U hU => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually hU)
  apply eventually_atTop.mpr
  refine ⟨max (i + 1) N, fun n hn => ?_⟩
  obtain ⟨τ, hτ, heq⟩ := htail (i + 1) n ((le_max_left _ _).trans hn)
  have hφeq : φ n = (state (i + 1)).val (τ n) := congrFun heq n
  change f (φ n) i ∈ U
  rw [hφeq]
  exact hN (τ n) (((le_max_right _ _).trans hn).trans (hτ.id_le n))

theorem exists_subseq_tendsto_of_countable_coordinatewise_subseq
    {I : Type*} {X : I → Type*} [Countable I] [∀ i, TopologicalSpace (X i)]
    (f : ℕ → ∀ i, X i)
    (hf : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧
        ∃ x : X i, Tendsto (fun n => f (σ (τ n)) i) atTop (𝓝 x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ x : X i, Tendsto (fun n => f (φ n) i) atTop (𝓝 x) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    exact ⟨id, strictMono_id, fun i => isEmptyElim i⟩
  | inr hI =>
    let : Encodable I := Encodable.ofCountable I
    let i₀ : I := Classical.choice hI
    let e : ℕ → I := fun n => (Encodable.decode n).getD i₀
    have he : Function.Surjective e := Encodable.surjective_decode_getD I i₀
    obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_nat
      (fun n i => f n (e i)) (fun i => hf (e i))
    refine ⟨φ, hφ, fun i => ?_⟩
    obtain ⟨n, rfl⟩ := he i
    exact hlim n

end
