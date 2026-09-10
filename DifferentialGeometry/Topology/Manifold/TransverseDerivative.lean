/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.SmoothTransverseSection
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

open Filter Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x y z

namespace DifferentialGeometry.Topology

namespace ContinuousLinearMap

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

def adjoin (L : E →L[ℝ] F) (w : F) : E × ℝ →L[ℝ] F :=
  L.coprod ((1 : ℝ →L[ℝ] ℝ).smulRight w)

@[simp]
theorem adjoin_apply (L : E →L[ℝ] F) (w : F) (p : E × ℝ) :
    adjoin L w p = L p.1 + p.2 • w := by
  rfl

theorem adjoin_injective
    (L : E →L[ℝ] F) (w : F)
    (hL : Function.Injective L) (hw : w ∉ Set.range L) :
    Function.Injective (adjoin L w) := by
  change Function.Injective (adjoin L w).toLinearMap
  rw [← LinearMap.ker_eq_bot]
  ext p
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hp
    have hsum : L p.1 + p.2 • w = 0 := by
      simpa [adjoin] using hp
    by_cases ht : p.2 = 0
    · have hx : p.1 = 0 := hL (by simpa [ht] using hsum)
      exact Prod.ext hx ht
    · exfalso
      apply hw
      refine ⟨(-p.2)⁻¹ • p.1, ?_⟩
      have hLx : L p.1 = (-p.2) • w := by
        calc
          L p.1 = (L p.1 + p.2 • w) - p.2 • w := by abel
          _ = (-p.2) • w := by rw [hsum]; simp
      rw [map_smul, hLx, smul_smul]
      simp [ht]
  · rintro rfl
    simp

noncomputable def transverseEquiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (w : F)
    (hL : Function.Injective L) (hw : w ∉ Set.range L)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) :
    (E × ℝ) ≃L[ℝ] F := by
  let A := adjoin L w
  have hA : Function.Injective A := adjoin_injective L w hL hw
  have hrank : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, hdim]
    simp
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hA
  exact ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA) (LinearMap.range_eq_top.mpr hsurj)

@[simp]
theorem transverseEquiv_apply
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (w : F)
    (hL : Function.Injective L) (hw : w ∉ Set.range L)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (p : E × ℝ) :
    transverseEquiv L w hL hw hdim p = L p.1 + p.2 • w := by
  rfl

end ContinuousLinearMap

namespace SmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {f : B → A}

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_injective
    (C : SmoothEmbeddingRealNormalAtlas I J n f)
    (hn : (1 : ℕ∞ω) ≤ n) (x : B) :
    Function.Injective (mfderiv I J f x) := by
  let R := SmoothEmbeddingRealNormalAtlas.toEmbeddingRealNormalAtlas C
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  let z : B → B × ℝ := fun y ↦ (y, 0)
  have hx : x ∈ R.baseSet x := R.mem_baseSet_self x
  have hlocal : (fun y ↦ (R.chart x).symm (f y)) =ᶠ[nhds x] z := by
    apply eventually_of_mem ((R.isOpen_baseSet x).mem_nhds hx)
    intro y hy
    change (R.chart x).symm (f y) = (y, 0)
    rw [← R.apply_zero x hy]
    exact (R.chart x).left_inv (R.zero_mem_source x hy)
  have hderivEq :
      mfderiv I IP (fun y ↦ (R.chart x).symm (f y)) x = mfderiv I IP z x :=
    hlocal.mfderiv_eq
  have hfDiff : MDifferentiableAt I J f x :=
    (C.contMDiff.contMDiffAt.mdifferentiableWithinAt
      (lt_of_lt_of_le zero_lt_one hn).ne').mdifferentiableAt univ_mem
  have hfx : f x ∈ (R.chart x).target := by
    rw [← R.apply_zero x hx]
    exact (R.chart x).map_source (R.zero_mem_source x hx)
  have hinvDiff : MDifferentiableAt J IP (R.chart x).symm (f x) :=
    ((C.contMDiffOn_chart_symm x) (f x) hfx)
      |>.mdifferentiableWithinAt (lt_of_lt_of_le zero_lt_one hn).ne'
      |>.mdifferentiableAt ((R.chart x).open_target.mem_nhds hfx)
  have hcomp (v : TangentSpace I x) :
      mfderiv I IP z x v =
        mfderiv J IP (R.chart x).symm (f x) (mfderiv I J f x v) := by
    calc
      _ = mfderiv I IP (fun y ↦ (R.chart x).symm (f y)) x v :=
        DFunLike.congr_fun hderivEq.symm v
      _ = _ := mfderiv_comp_apply x hinvDiff hfDiff v
  intro v₁ v₂ hv
  have hv' : mfderiv I IP z x v₁ = mfderiv I IP z x v₂ := by
    rw [hcomp v₁, hcomp v₂, hv]
  have hz : mfderiv I IP z x = ContinuousLinearMap.inl ℝ E ℝ := mfderiv_prod_left
  rw [hz] at hv'
  exact congrArg Prod.fst hv'

set_option backward.isDefEq.respectTransparency false in
noncomputable def transverseEquivAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : SmoothEmbeddingRealNormalAtlas I J n f)
    (hn : (1 : ℕ∞ω) ≤ n)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (x : B) (w₀ : TangentSpace J (f x))
    (hw : w₀ ∉ Set.range (mfderiv I J f x)) :
    (TangentSpace I x × ℝ) ≃L[ℝ] TangentSpace J (f x) := by
  change (E × ℝ) ≃L[ℝ] F
  exact DifferentialGeometry.Topology.ContinuousLinearMap.transverseEquiv
    (mfderiv I J f x) w₀ (C.mfderiv_injective hn x) hw hdim

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem transverseEquivAt_apply
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : SmoothEmbeddingRealNormalAtlas I J n f)
    (hn : (1 : ℕ∞ω) ≤ n)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (x : B) (w₀ : TangentSpace J (f x))
    (hw : w₀ ∉ Set.range (mfderiv I J f x))
    (p : TangentSpace I x × ℝ) :
    C.transverseEquivAt hn hdim x w₀ hw p =
      mfderiv I J f x p.1 + p.2 • w₀ := by
  exact DifferentialGeometry.Topology.ContinuousLinearMap.transverseEquiv_apply
    (E := E) (F := F) (mfderiv I J f x) w₀
      (C.mfderiv_injective hn x) hw hdim p

end SmoothEmbeddingRealNormalAtlas

namespace CoorientedSmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {f : B → A}
    (C : CoorientedSmoothEmbeddingRealNormalAtlas I J n f)

set_option backward.isDefEq.respectTransparency false in
noncomputable def positiveNormalEquivAt
    (hn : (1 : ℕ∞ω) ≤ n)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (x : B) (w₀ : TangentSpace J (f x))
    (hw : w₀ ∈ C.positiveNormalHalfSpace x) :
    (TangentSpace I x × ℝ) ≃L[ℝ] TangentSpace J (f x) :=
  C.toSmoothEmbeddingRealNormalAtlas.transverseEquivAt hn hdim x w₀
    (C.not_mem_range_mfderiv_of_mem_positiveNormalHalfSpace hn hw)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem positiveNormalEquivAt_apply
    (hn : (1 : ℕ∞ω) ≤ n)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (x : B) (w₀ : TangentSpace J (f x))
    (hw : w₀ ∈ C.positiveNormalHalfSpace x)
    (p : TangentSpace I x × ℝ) :
    C.positiveNormalEquivAt hn hdim x w₀ hw p =
      mfderiv I J f x p.1 + p.2 • w₀ := by
  exact C.toSmoothEmbeddingRealNormalAtlas.transverseEquivAt_apply hn hdim x w₀
    (C.not_mem_range_mfderiv_of_mem_positiveNormalHalfSpace hn hw) p

end CoorientedSmoothEmbeddingRealNormalAtlas

end DifferentialGeometry.Topology
