import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# Diffeomorphisms determined by two smooth covers with the same fibres

Two onto local diffeomorphisms from the same manifold, with equal fibre equivalence relations,
induce a whole diffeomorphism of their actual targets. The resulting diffeomorphism commutes
pointwise with both original covering maps. No metric or classification assumption is involved.
-/

set_option autoImplicit false

noncomputable section

open Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F K : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  [instF : NormedAddCommGroup F] [instFR : NormedSpace ℝ F]
  [instK : NormedAddCommGroup K] [instKR : NormedSpace ℝ K]
  {HE HF HK : Type*} [instHE : TopologicalSpace HE] [instHF : TopologicalSpace HF]
  [instHK : TopologicalSpace HK] {I : ModelWithCorners ℝ E HE}
  {J : ModelWithCorners ℝ F HF} {L : ModelWithCorners ℝ K HK}
  {X M N : Type*} [instX : TopologicalSpace X] [instM : TopologicalSpace M]
  [instN : TopologicalSpace N] [instCX : ChartedSpace HE X]
  [instCM : ChartedSpace HF M] [instCN : ChartedSpace HK N]

theorem exists_diffeomorph_of_same_cover_fibres (p : X → M) (q : X → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (hq : IsLocalDiffeomorph I L ∞ q)
    (hps : Surjective p) (hqs : Surjective q)
    (hrel : ∀ x y, p x = p y ↔ q x = q y) :
    ∃ e : M ≃ₘ⟮J, L⟯ N, ∀ x, e (p x) = q x := by
  let f : M → N := q ∘ surjInv hps
  have hf : ∀ x, f (p x) = q x := fun x =>
    (hrel (surjInv hps (p x)) x).mp (surjInv_eq hps (p x))
  have hinj : Injective f := by
    intro a b hab
    have he := (hrel (surjInv hps a) (surjInv hps b)).mpr hab
    simpa only [surjInv_eq] using he
  have hsurj : Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hqs y
    exact ⟨p x, hf x⟩
  let e : M ≃ N := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ x, e (p x) = q x := hf
  have hinv : ∀ x, e.symm (q x) = p x := by
    intro x
    rw [← he x, e.symm_apply_apply]
  refine ⟨{ toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, he⟩
  · apply hp.contMDiff_of_comp_of_surjective hps
    have hc : (e : M → N) ∘ p = q := funext he
    rw [hc]
    exact hq.contMDiff
  · apply hq.contMDiff_of_comp_of_surjective hqs
    have hc : (e.symm : N → M) ∘ q = p := funext hinv
    rw [hc]
    exact hp.contMDiff

end DifferentialGeometry.Topology.Manifold
