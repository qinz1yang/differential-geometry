import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPLBall.simplyConnectedSpace [FiniteDimensional ℝ E] {n : ℕ} {D : Set E}
    (hD : IsPLBall n D) : SimplyConnectedSpace D := by
  obtain ⟨f, hf⟩ := hD
  let _ : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  exact hf.homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

theorem IsPLBall.locallyPathConnectedSpace [FiniteDimensional ℝ E] {n : ℕ} {D : Set E}
    (hD : IsPLBall n D) : LocallyPathConnectedSpace D := by
  obtain ⟨f, hf⟩ := hD
  let _ : LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).locallyPathConnectedSpace
  exact hf.homeomorph.symm.isOpenEmbedding.locallyPathConnectedSpace

end DifferentialGeometry.Topology.PiecewiseLinear

namespace IsCoveringMap

open DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

variable {X' : Type u} {X : Type v} [TopologicalSpace X'] [TopologicalSpace X]
  {p : X' → X}

theorem exists_unique_lift_of_isPLBall (hp : IsCoveringMap p)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {D : Set E} (hD : IsPLBall n D) (f : C(D, X)) (x₀ : D) (e₀ : X')
    (h₀ : p e₀ = f x₀) : ∃! g : C(D, X'), p ∘ g = f ∧ g x₀ = e₀ := by
  let _ : SimplyConnectedSpace D := hD.simplyConnectedSpace
  let _ : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  obtain ⟨g, hg, huniq⟩ := hp.existsUnique_continuousMap_lifts f x₀ e₀ h₀
  exact ⟨g, ⟨hg.2, hg.1⟩, fun g' hg' ↦ huniq g' ⟨hg'.2, hg'.1⟩⟩

theorem injective_fundamentalGroup_map (hp : IsCoveringMap p) (e : X') :
    Function.Injective (FundamentalGroup.map ⟨p, hp.continuous⟩ e) := by
  exact hp.injective_path_homotopic_map e e

theorem fundamentalGroup_stabilizer_eq_range (hp : IsCoveringMap p) (e : X') :
    @MulAction.stabilizer (FundamentalGroup X (p e)) (p ⁻¹' {p e}) inferInstance
        (hp.fundamentalGroupMulAction (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) =
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range := by
  ext γ
  change hp.monodromy γ (⟨e, rfl⟩ : p ⁻¹' {p e}) = ⟨e, rfl⟩ ↔ _
  constructor
  · intro h
    refine ⟨(hp.liftPathQuotient γ (⟨e, rfl⟩ : p ⁻¹' {p e})).cast
      rfl congr($h.symm), ?_⟩
    change
      (((hp.liftPathQuotient γ (⟨e, rfl⟩ : p ⁻¹' {p e})).cast
        rfl congr($h.symm)).map ⟨p, hp.continuous⟩) = γ
    rw [Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient]
    exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq _ _).trans
      (Path.Homotopic.Quotient.cast_heq _ _))
  · rintro ⟨Γ, hΓ⟩
    apply hp.monodromy_eq_of_map_eq (FundamentalGroup.toPath Γ)
    have hmap : (FundamentalGroup.toPath Γ).map ⟨p, hp.continuous⟩ = γ := by
      rw [← FundamentalGroup.map_apply]
      exact hΓ
    simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using hmap

theorem monodromy_eq_iff_mem_range (hp : IsCoveringMap p) (e : X')
    (γ : FundamentalGroup X (p e)) :
    hp.monodromy γ (⟨e, rfl⟩ : p ⁻¹' {p e}) = ⟨e, rfl⟩ ↔
      γ ∈ (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range := by
  rw [← hp.fundamentalGroup_stabilizer_eq_range e]
  rfl

theorem liftPath_one_eq_iff_mem_range (hp : IsCoveringMap p) (e : X')
    (γ : Path (p e) (p e)) :
    hp.liftPath γ e γ.source 1 = e ↔
      FundamentalGroup.fromPath ⟦γ⟧ ∈
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range := by
  have h := hp.monodromy_eq_iff_mem_range e (FundamentalGroup.fromPath ⟦γ⟧)
  constructor
  · intro hend
    apply h.mp
    exact Subtype.ext hend
  · intro hrange
    exact congrArg Subtype.val (h.mpr hrange)

theorem fundamentalGroupMulAction_isPretransitive [PathConnectedSpace X']
    (hp : IsCoveringMap p) (x : X) :
    let _ := hp.fundamentalGroupMulAction x
    MulAction.IsPretransitive (FundamentalGroup X x) (p ⁻¹' {x}) := by
  let _ := hp.fundamentalGroupMulAction x
  constructor
  intro e₀ e₁
  let Γ : Path.Homotopic.Quotient (e₀ : X') e₁ :=
    .mk (PathConnectedSpace.somePath (e₀ : X') e₁)
  let γ : FundamentalGroup X x :=
    (Γ.map ⟨p, hp.continuous⟩).cast e₀.2.symm e₁.2.symm
  refine ⟨γ, ?_⟩
  change hp.monodromy γ e₀ = e₁
  apply hp.monodromy_eq_of_map_eq Γ
  change Γ.map ⟨p, hp.continuous⟩ =
    ((Γ.map ⟨p, hp.continuous⟩).cast e₀.2.symm e₁.2.symm).cast e₀.2 e₁.2
  exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq e₀.2 e₁.2).trans
    (Path.Homotopic.Quotient.cast_heq e₀.2.symm e₁.2.symm)).symm

theorem card_fiber_eq_index [PathConnectedSpace X'] (hp : IsCoveringMap p) (e : X') :
    Nat.card (p ⁻¹' {p e}) =
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index := by
  let _ := hp.fundamentalGroupMulAction (p e)
  let _ : MulAction.IsPretransitive (FundamentalGroup X (p e)) (p ⁻¹' {p e}) :=
    hp.fundamentalGroupMulAction_isPretransitive (p e)
  rw [← hp.fundamentalGroup_stabilizer_eq_range e]
  exact (MulAction.index_stabilizer_of_transitive (FundamentalGroup X (p e))
    (⟨e, rfl⟩ : p ⁻¹' {p e})).symm

end IsCoveringMap
