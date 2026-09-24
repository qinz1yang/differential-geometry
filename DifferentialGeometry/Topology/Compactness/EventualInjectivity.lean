import Mathlib.Topology.Sequences

section

open Set Filter Topology

namespace IsCompact

variable {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
  {M : ℕ → Type*} {K : Set Q}

theorem eventually_injOn_of_local_injOn_of_collision_limits
    (hK : IsCompact K) (F : ∀ n, Q → M n)
    (hlocal : ∀ x ∈ K, ∃ U ∈ nhds x, ∀ᶠ n in atTop, InjOn (F n) U)
    (hcollision : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (x y : ℕ → Q), (∀ n, x n ∈ K) → (∀ n, y n ∈ K) →
      ∀ a ∈ K, ∀ b ∈ K,
        Tendsto x atTop (nhds a) → Tendsto y atTop (nhds b) →
        (∀ n, F (φ n) (x n) = F (φ n) (y n)) → a = b) :
    ∀ᶠ n in atTop, InjOn (F n) K := by
  classical
  by_contra h
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp h)
  have hex : ∀ n, ∃ x ∈ K, ∃ y ∈ K, F (φ n) x = F (φ n) y ∧ x ≠ y := by
    intro n
    have hn := hbad n
    simp only [InjOn, not_forall] at hn
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hn
    exact ⟨x, hx, y, hy, heq, hne⟩
  choose x hx y hy heq hne using hex
  obtain ⟨p, hp, ψ, hψ, hpconv⟩ :=
    (hK.prod hK).tendsto_subseq (fun n => show (x n, y n) ∈ K ×ˢ K from ⟨hx n, hy n⟩)
  have hxconv : Tendsto (x ∘ ψ) atTop (nhds p.1) := by
    exact (continuous_fst.tendsto p).comp hpconv
  have hyconv : Tendsto (y ∘ ψ) atTop (nhds p.2) := by
    exact (continuous_snd.tendsto p).comp hpconv
  have hpEq := hcollision (φ ∘ ψ) (hφ.comp hψ) (x ∘ ψ) (y ∘ ψ)
    (fun n => hx (ψ n)) (fun n => hy (ψ n)) p.1 hp.1 p.2 hp.2 hxconv hyconv
    (fun n => heq (ψ n))
  rw [← hpEq] at hyconv
  obtain ⟨U, hU, hinj⟩ := hlocal p.1 hp.1
  have htail := ((hφ.comp hψ).tendsto_atTop.eventually hinj).and
    ((hxconv.eventually hU).and (hyconv.eventually hU))
  obtain ⟨n, hn⟩ := htail.exists
  exact hne (ψ n) (hn.1 hn.2.1 hn.2.2 (heq (ψ n)))

end IsCompact

end
