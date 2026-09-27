import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_real_circle_lift_of_nullhomotopic {X : Type*} [TopologicalSpace X]
    {g : C(X, loopCircle)} (hg : g.Nullhomotopic) :
    ∃ l : C(X, ℝ), ∀ x, (l x : loopCircle) = g x := by
  obtain ⟨y, ⟨H⟩⟩ := hg
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective y
  have hcov : IsCoveringMap (fun t : ℝ => (t : loopCircle)) :=
    AddCircle.isCoveringMap_coe (1 : ℝ)
  have hzero : ∀ x, H.symm (0, x) = ((ContinuousMap.const X a) x : loopCircle) := by
    intro x
    exact (H.symm.apply_zero x).trans ha.symm
  let L := hcov.liftHomotopy H.symm.toContinuousMap (ContinuousMap.const X a) hzero
  refine ⟨⟨fun x => L (1, x), L.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro x
  exact (congrFun (hcov.liftHomotopy_lifts H.symm.toContinuousMap
    (ContinuousMap.const X a) hzero) (1, x)).trans (H.symm.apply_one x)

theorem IsCylindricalDiagram.exists_meridian_height_lift_of_nullhomotopic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsCompact P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJS : J ⊆ S)
    (hnull : (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic) :
    ∃ e : S ≃ₜ (P × loopCircle),
      (∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t)) ∧
      ∃ l : C(J, ℝ), (∀ x, (l x : loopCircle) = (e ⟨x.1, hJS x.2⟩).2) ∧
        ∀ x : J, x.1 ∈ f '' (P ×ˢ {(0 : ℝ)}) ↔ ∃ m : ℤ, l x = m := by
  obtain ⟨e, he⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends hP hends
  let π : C(S, loopCircle) := ⟨fun y => (e y).2, continuous_snd.comp e.continuous⟩
  obtain ⟨l, hl⟩ := exists_real_circle_lift_of_nullhomotopic (hnull.comp_right π)
  change ∀ x : J, (l x : loopCircle) = (e ⟨x.1, hJS x.2⟩).2 at hl
  refine ⟨e, he, l, hl, ?_⟩
  intro x
  have hzero : x.1 ∈ f '' (P ×ˢ {(0 : ℝ)}) ↔ (e ⟨x.1, hJS x.2⟩).2 = 0 := by
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, hxy⟩
      have ht' : t = 0 := ht
      subst t
      have hx : e.symm (⟨y, hy⟩, (0 : loopCircle)) = (⟨x.1, hJS x.2⟩ : S) := by
        apply Subtype.ext
        exact (he ⟨y, hy⟩ 0).trans hxy
      rw [← hx, e.apply_symm_apply]
    · intro hz
      have hx := he (e ⟨x.1, hJS x.2⟩).1 0
      change (e.symm ((e ⟨x.1, hJS x.2⟩).1, (0 : loopCircle)) : F) =
        f ((e ⟨x.1, hJS x.2⟩).1, 0) at hx
      have hp : ((e ⟨x.1, hJS x.2⟩).1, (0 : loopCircle)) = e ⟨x.1, hJS x.2⟩ :=
        Prod.ext rfl hz.symm
      rw [hp, e.symm_apply_apply] at hx
      exact ⟨(_, 0), ⟨(e ⟨x.1, hJS x.2⟩).1.2, rfl⟩, hx.symm⟩
  rw [hzero, ← hl x]
  simpa only [zsmul_eq_mul, mul_one, eq_comm] using
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := l x))

end DifferentialGeometry.Topology.PiecewiseLinear
