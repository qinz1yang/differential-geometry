import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBernstein
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductHigherDerivativeBernstein
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSecondDerivativeBernstein
import Mathlib.Data.Set.Finite.Lattice

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

private theorem exists_one_le_sq_bound {ι : Type*} [Finite ι] (A : ι → ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j, A j ≤ D ^ 2 := by
  obtain ⟨B, hB⟩ := (Set.finite_range A).bddAbove
  refine ⟨max 1 B, le_max_left _ _, fun j => ?_⟩
  exact (hB (Set.mem_range_self j)).trans ((le_max_right 1 B).trans
    (le_self_pow₀ (le_max_left 1 B) (by decide)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] {T : RealTimeInterval} {a b : ℝ}

theorem exists_uniform_iteratedDs_curvature_bounds
    (B : RicciBackground (I := I) (M := M) T a b) (L₀ Θ₀ : ℝ)
    (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r : ℝ, a ≤ s → s < u → u ≤ b → Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ (m : ℕ) (x : ℝ), c.normSq B.family.metric lambda
        (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x u ≤
        A m / (u - s) ^ (m + 1) := by
  obtain ⟨δ, r₀, A₁, hδ, hδ1, hr₀, hr₀1, hA₁, hbase⟩ :=
    exists_uniform_curvature_and_derivative_bounds B L₀ Θ₀ hL₀ hΘ₀
  let Good : ℕ → ℝ → Prop := fun m A =>
    ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r : ℝ, a ≤ s → s < u → u ≤ b → Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ x : ℝ, c.normSq B.family.metric lambda
        (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x u ≤
        A / (u - s) ^ (m + 1)
  have horders : ∀ m : ℕ, ∃ A : ℝ, 0 < A ∧ Good m A := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm0 : m = 0
      · subst m
        refine ⟨4, by norm_num, ?_⟩
        intro lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x
        simpa [ProductCurve.iteratedDs, ProductCurve.curvatureSq] using (hbase lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x).1
      by_cases hm1 : m = 1
      · subst m
        refine ⟨A₁, hA₁, ?_⟩
        intro lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x
        exact (hbase lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x).2
      have hm2 : 2 ≤ m := by omega
      have hprev : ∀ j : Fin m, ∃ Aj : ℝ, 0 < Aj ∧ Good j Aj := by
        intro j
        exact ih j j.isLt
      choose Aj hAj hGood using hprev
      obtain ⟨D, hD, hAjD⟩ := exists_one_le_sq_bound Aj
      have hstep : ∃ Aout : ℝ, 0 < Aout ∧
          ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
          ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
          ∀ s u : ℝ, s < u → Icc s u ⊆ Icc a b → Icc s u ⊆ J → u - s ≤ 1 →
          (∀ x t, t ∈ Ioc s u → ∀ j ≤ m - 1,
            c.normSq B.family.metric lambda
              (c.iteratedDs B.family.metric lambda j (c.curvatureVector B.family.metric lambda)) x t ≤
              D ^ 2 / (t - s) ^ (j + 1)) →
          ∀ x, c.normSq B.family.metric lambda
            (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x u ≤
            Aout / (u - s) ^ (m + 1) := by
        by_cases hm : m = 2
        · subst m
          exact exists_uniform_iteratedDs_two_curvature_bound_of_lower_derivative_bounds B hD
        · have hpred : 2 ≤ m - 1 := by omega
          have hsum : m - 1 + 1 = m := by omega
          have hsum' : m - 1 + 2 = m + 1 := by omega
          simpa only [hsum, hsum'] using
            exists_uniform_iteratedDs_curvature_bound_of_lower_derivative_bounds B hpred hD
      obtain ⟨Aout, hAout, hbound⟩ := hstep
      refine ⟨Aout, hAout, ?_⟩
      intro lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x
      have hjets : ∀ y t, t ∈ Ioc s u → ∀ j ≤ m - 1,
          c.normSq B.family.metric lambda
            (c.iteratedDs B.family.metric lambda j (c.curvatureVector B.family.metric lambda)) y t ≤
            D ^ 2 / (t - s) ^ (j + 1) := by
        intro y t ht j hj
        have hjm : j < m := by omega
        let jj : Fin m := ⟨j, hjm⟩
        have hgj := hGood jj lambda hlambda c J hJ hc hlen htot s t r has ht.1 (ht.2.trans hub)
          ((Icc_subset_Icc le_rfl ht.2).trans hI) hr hrr hlenr (ht.2.trans htime) hsmall y
        have hAjbound := hAjD jj
        exact hgj.trans (div_le_div_of_nonneg_right hAjbound (pow_nonneg (sub_nonneg.mpr ht.1.le) _))
      have htime1 : u - s ≤ 1 := by
        have hr1 := hrr.trans hr₀1
        have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
        have hh := (mul_le_mul_of_nonneg_left hr2 hδ.le).trans (by simpa only [mul_one] using hδ1.le)
        linarith only [htime, hh]
      exact hbound lambda hlambda c J hJ hc s u hsu (Icc_subset_Icc has hub)
        ((Icc_subset_Icc has le_rfl).trans hI) htime1 hjets x
  choose A hA hGood using horders
  refine ⟨δ, r₀, A, hδ, hδ1, hr₀, hr₀1, hA, ?_⟩
  intro lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall m x
  exact hGood m lambda hlambda c J hJ hc hlen htot s u r has hsu hub hI hr hrr hlenr htime hsmall x

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
