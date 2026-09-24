import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Data.Set.Card

noncomputable section

namespace DifferentialGeometry.Topology.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

private noncomputable def fiberMapToFundamentalGroup (hp : IsCoveringMap p) [PathConnectedSpace E]
    {x : X} {e : E} (he : p e = x) (e' : E) (he' : p e' = x) : FundamentalGroup X x :=
  ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e e')).map
    ⟨p, hp.continuous⟩).cast he.symm he'.symm

private theorem monodromy_fiberMapToFundamentalGroup (hp : IsCoveringMap p)
    [PathConnectedSpace E] {x : X} {e : E} (he : p e = x) (e' : E) (he' : p e' = x) :
    hp.monodromy (fiberMapToFundamentalGroup hp he e' he') ⟨e, he⟩ = ⟨e', he'⟩ := by
  have hcast : (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e e')).map
      ⟨p, hp.continuous⟩ =
      (((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e e')).map
        ⟨p, hp.continuous⟩).cast he.symm he'.symm).cast he he' := by
    rw [Path.Homotopic.Quotient.cast_cast]
    exact (eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _)).symm
  refine hp.monodromy_eq_of_map_eq
    (Γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e e')) ?_
  simpa only [fiberMapToFundamentalGroup] using hcast

private theorem fiberMapToFundamentalGroup_eq_of_monodromy_eq (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] {x : X} {e : E} (he : p e = x) (γ : FundamentalGroup X x)
    (y : p ⁻¹' {x}) (h : hp.monodromy γ ⟨e, he⟩ = y) :
    fiberMapToFundamentalGroup hp he (y : E) y.2 = γ := by
  have hy : p (y : E) = x := y.2
  have hz : p (hp.monodromy γ ⟨e, he⟩ : E) = x := (hp.monodromy γ ⟨e, he⟩).2
  change fiberMapToFundamentalGroup hp he (y : E) hy = γ
  have hpt : (hp.monodromy γ ⟨e, he⟩ : E) = (y : E) := congrArg Subtype.val h
  have hΓ : Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e (y : E)) =
      (hp.liftPathQuotient γ ⟨e, he⟩).cast rfl hpt.symm := Subsingleton.elim _ _
  calc fiberMapToFundamentalGroup hp he (y : E) hy
      = (((hp.liftPathQuotient γ ⟨e, he⟩).cast rfl hpt.symm).map
          ⟨p, hp.continuous⟩).cast he.symm hy.symm := by
        rw [fiberMapToFundamentalGroup, hΓ]
    _ = ((Path.Homotopic.Quotient.cast γ he hz).cast rfl
          (congrArg (fun z => p z) hpt.symm)).cast he.symm hy.symm := by
        rw [Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient]
    _ = γ := by
        rw [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_cast]
        exact eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _)

private theorem ncard_fiber_eq_card_fundamentalGroup_aux (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] {x : X} {e : E} (he : p e = x) :
    (p ⁻¹' {x}).ncard = Nat.card (FundamentalGroup X x) := by
  have hbij : Function.Bijective fun γ : FundamentalGroup X x => hp.monodromy γ ⟨e, he⟩ := by
    refine ⟨fun γ γ' h => ?_, fun y => ?_⟩
    · have h1 := fiberMapToFundamentalGroup_eq_of_monodromy_eq hp he γ
        (hp.monodromy γ' ⟨e, he⟩) h
      have h2 := fiberMapToFundamentalGroup_eq_of_monodromy_eq hp he γ'
        (hp.monodromy γ' ⟨e, he⟩) rfl
      exact h1.symm.trans h2
    · have hy : p (y : E) = x := y.2
      refine ⟨fiberMapToFundamentalGroup hp he (y : E) hy, ?_⟩
      have h1 := monodromy_fiberMapToFundamentalGroup hp he (y : E) hy
      simpa [Subtype.ext_iff] using h1
  exact Nat.card_congr (Equiv.ofBijective _ hbij).symm

theorem ncard_fiber_eq_card_fundamentalGroup (hp : IsCoveringMap p) [SimplyConnectedSpace E]
    {x : X} (e : p ⁻¹' {x}) :
    (p ⁻¹' {x}).ncard = Nat.card (FundamentalGroup X x) := by
  have he : p (e : E) = x := e.2
  exact ncard_fiber_eq_card_fundamentalGroup_aux hp he

end DifferentialGeometry.Topology.Covering
