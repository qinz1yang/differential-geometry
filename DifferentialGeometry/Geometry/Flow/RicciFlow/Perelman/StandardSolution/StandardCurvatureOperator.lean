import DifferentialGeometry.Analysis.Elliptic.Barrier.CompleteLocalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RayleighSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardRayleigh
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem shifted_upperRicci_support_continuousWithinAt
    (S : PartialStandardSolution) (T : ℝ) (hsub : Icc 0 T ⊆ S.domain)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : E3)
    (V : E3 → E3) (hV : ContinuousAt V x) (hVx : V x ≠ 0)
    (ell : ℝ) :
    ContinuousWithinAt
      (fun p : ℝ × E3 => ell +
        (upperRicciTensorAt (S.metric p.1) p.2
            (vec2 (I := 𝓡 3) (V p.2) (V p.2)) -
          ell * (S.metric p.1).inner p.2 (V p.2) (V p.2)) /
            (S.metric p.1).inner p.2 (V p.2) (V p.2))
      (spacetimeSlab (M := E3) T) (t, x) := by
  have hslab : spacetimeSlab (M := E3) T ⊆ S.domain ×ˢ (univ : Set E3) :=
    prod_mono hsub subset_rfl
  have hpoint : (t, x) ∈ spacetimeSlab (M := E3) T := ⟨ht, mem_univ x⟩
  have hv : ContinuousWithinAt (fun p : ℝ × E3 => V p.2)
      (spacetimeSlab (M := E3) T) (t, x) :=
    hV.comp_continuousWithinAt continuous_snd.continuousAt.continuousWithinAt
  have hg : ContinuousWithinAt (cartesianMetricFamily S.metric)
      (spacetimeSlab (M := E3) T) (t, x) :=
    (S.smooth.continuousOn.mono hslab) (t, x) hpoint
  have hRic : ContinuousWithinAt (cartesianRicciFamily S.metric)
      (spacetimeSlab (M := E3) T) (t, x) :=
    (S.ricci_contDiffOn.continuousOn.mono hslab) (t, x) hpoint
  have hsc : ContinuousWithinAt
      (fun p : ℝ × E3 => metricScalarAt (S.metric p.1) p.2)
      (spacetimeSlab (M := E3) T) (t, x) :=
    (S.scalar_contDiffOn.continuousOn.mono hslab) (t, x) hpoint
  have hd : ContinuousWithinAt
      (fun p : ℝ × E3 => (S.metric p.1).inner p.2 (V p.2) (V p.2))
      (spacetimeSlab (M := E3) T) (t, x) :=
    (hg.clm_apply hv).clm_apply hv
  have hRq : ContinuousWithinAt
      (fun p : ℝ × E3 => ricciTensor (S.metric p.1) p.2 (V p.2) (V p.2))
      (spacetimeSlab (M := E3) T) (t, x) :=
    (hRic.clm_apply hv).clm_apply hv
  simp_rw [upperRicciTensorAt_apply]
  exact continuousWithinAt_const.add
    ((((hsc.div_const 2).mul hd).sub hRq).sub
      (continuousWithinAt_const.mul hd) |>.div hd
        (ne_of_gt ((S.metric t).pos x (V x) hVx)))

private theorem least_upperRicci_nonneg_closed (S : PartialStandardSolution)
    (T : ℝ) (hT : 0 < T) (hTl : ENNReal.ofReal T < S.lifetime) :
    ∀ t ∈ Icc 0 T, ∀ x : E3, 0 ≤ leastUpperRicciAt (S.metric t) x := by
  let Q := S.toSolutionOn
  let G := flowG Q
  have hQ : IsSolutionOn Q := S.isSolutionOn
  have hQs := smoothOfSolution Q hQ
  have hslab :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos T hT.le).mpr hTl
  have hreg : Ioc 0 T ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTl⟩
  obtain ⟨K, hK, hRm, hqbound, hframebound⟩ :=
    S.exists_upperRicciRayleigh_bounds_closed T hT.le hTl
  have hnorm : ∀ t ∈ Icc 0 T, ∀ x : E3,
      nablaKRm04NormSqIntrinsic Q 0 t x ≤ K ^ 2 := by
    intro t ht x
    exact (Real.sqrt_le_iff.mp (hRm t ht x)).2
  have hcut := nonempty_shi_barrier_cutoff_data_of_solution Q hQ hT hslab hreg
    (S.complete 0 (hslab ⟨le_rfl, hT.le⟩)) (sq_nonneg K) hnorm
  let q := fun t x => -leastUpperRicciAt (S.metric t) x
  have hcont : ContinuousOn (fun p : ℝ × E3 => q p.1 p.2)
      (Icc 0 T ×ˢ univ) :=
    S.neg_leastUpperRicciAt_continuousOn.mono (prod_mono hslab subset_rfl)
  have hinit : ∀ x : E3, q 0 x ≤ 0 := by
    intro x
    exact neg_nonpos.mpr (S.leastUpperRicciAt_zero_nonneg x)
  have hsupport : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : E3, 0 < q t x →
      ∃ v : ℝ → E3 → ℝ,
        v t x = q t x ∧
        (∀ᶠ p in 𝓝[spacetimeSlab (M := E3) T] (t, x),
          v p.1 p.2 ≤ q p.1 p.2) ∧
        ContinuousWithinAt (fun p : ℝ × E3 => v p.1 p.2)
          (spacetimeSlab (M := E3) T) (t, x) ∧
        DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (v t) y) ∧
        MDifferentiableAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3))
          (T% (gradientFun (I := 𝓡 3) (G.metric t) (v t))) x ∧
        parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤
          (6 * K) * v t x := by
    intro t ht hp x hpos
    obtain ⟨basis, r1, r2, r3, horth, h21, h32, hdiag,
      hmin, _hunit, _hvalue, hleft, hright⟩ :=
      exists_ordered_ricci_frame_leastUpperRicciAt (S.metric t) x
    let ell := (1 / 2 : ℝ) * Q.scalar t x - r1
    have hell : leastUpperRicciAt (S.metric t) x = ell := by
      rw [hmin]
      change metricScalarAt (S.metric t) x / 2 - r1 =
        (1 / 2 : ℝ) * metricScalarAt (S.metric t) x - r1
      ring
    have hleft' : ∀ z : TangentSpace (𝓡 3) x,
        ricciUpperBoundSec Q t x (vec2 (I := 𝓡 3) (basis 0) z) =
          ((1 / 2 : ℝ) * Q.scalar t x - r1) *
            (Q.base.metric t).inner x (basis 0) z := by
      intro z
      change ricciUpperBoundSec S.toSolutionOn t x
        (vec2 (I := 𝓡 3) (basis 0) z) =
          ell * (S.metric t).inner x (basis 0) z
      rw [← S.upperRicciTensorAt_eq_sec, ← hell]
      exact hleft z
    have hright' : ∀ z : TangentSpace (𝓡 3) x,
        ricciUpperBoundSec Q t x (vec2 (I := 𝓡 3) z (basis 0)) =
          ((1 / 2 : ℝ) * Q.scalar t x - r1) *
            (Q.base.metric t).inner x z (basis 0) := by
      intro z
      change ricciUpperBoundSec S.toSolutionOn t x
        (vec2 (I := 𝓡 3) z (basis 0)) =
          ell * (S.metric t).inner x z (basis 0)
      rw [← S.upperRicciTensorAt_eq_sec, ← hell]
      exact hright z
    have hdim (y : E3) : Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 :=
      finrank_euclideanSpace_fin
    obtain ⟨V, hV, _hcovV, hψvalue, hψtime, hψspace, hψgrad, _hPψ, hPneg⟩ :=
      exists_rayleigh_support_operator_in_ordered_frame Q hQs T hT hdim
        hslab hreg t ⟨hp, ht.2⟩ x basis r1 r2 r3
        horth h21 h32 hdiag hleft' hright'
    let ψ := fun s y => ell +
      (ricciUpperBoundSec Q s y (vec2 (I := 𝓡 3) (V y) (V y)) -
        ell * (S.metric s).inner y (V y) (V y)) /
          (S.metric s).inner y (V y) (V y)
    have hvalue : ψ t x = ell := hψvalue
    have hVcont : Continuous (fun y : E3 => (V y : E3)) :=
      (contMDiff_vectorSpace_iff_contDiff.mp V.contMDiff).continuous
    have hVne : (V x : E3) ≠ 0 := by
      rw [hV]
      exact basis.ne_zero 0
    have hψcont : ContinuousWithinAt (fun p : ℝ × E3 => ψ p.1 p.2)
        (spacetimeSlab (M := E3) T) (t, x) := by
      have hh := shifted_upperRicci_support_continuousWithinAt S T hslab
        t ht x (fun y => V y) hVcont.continuousAt hVne ell
      simpa only [S.upperRicciTensorAt_eq_sec] using hh
    have hcompare : ∀ᶠ p in 𝓝[spacetimeSlab (M := E3) T] (t, x),
        -ψ p.1 p.2 ≤ q p.1 p.2 := by
      have hh := S.eventually_shifted_upperRicci_lower_support t x
        (fun y => V y) hVcont.continuousAt hVne ell
        (spacetimeSlab (M := E3) T)
      simpa only [S.upperRicciTensorAt_eq_sec] using hh
    have hneggrad :
        MDifferentiableAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3))
          (T% (gradientFun (I := 𝓡 3) (G.metric t)
            (fun y => -ψ t y))) x := by
      have heq :
          (fun y : E3 => gradientFun (I := 𝓡 3) (G.metric t)
            (fun z => -ψ t z) y) =ᶠ[𝓝 x]
            (fun y : E3 => -gradientFun (I := 𝓡 3) (G.metric t) (ψ t) y) := by
        filter_upwards [hψspace] with y hy
        exact gradientFun_neg (I := 𝓡 3) (G.metric t) hy
      have htotal :
          (T% fun y : E3 => gradientFun (I := 𝓡 3) (G.metric t)
            (fun z => -ψ t z) y) =ᶠ[𝓝 x]
            (T% fun y : E3 => -gradientFun (I := 𝓡 3) (G.metric t) (ψ t) y) := by
        filter_upwards [heq] with y hy
        change TotalSpace.mk' E3 y
            (gradientFun (I := 𝓡 3) (G.metric t) (fun z => -ψ t z) y) =
          TotalSpace.mk' E3 y (-gradientFun (I := 𝓡 3) (G.metric t) (ψ t) y)
        rw [hy]
      exact (mdifferentiableAt_neg_section hψgrad).congr_of_eventuallyEq htotal
    have hellneg : ell < 0 := by
      change 0 < -leastUpperRicciAt (S.metric t) x at hpos
      rw [hell] at hpos
      linarith only [hpos]
    have hr1 : metricRicciAt (S.metric t) x
        (vec2 (I := 𝓡 3) (basis 0) (basis 0)) = r1 := by
      simpa only [ricciDiag3, ite_true] using hdiag 0 0
    have hr1K : r1 ≤ 3 * K := hframebound t ht x basis horth r1 hr1
    refine ⟨fun s y => -ψ s y, ?_, hcompare, hψcont.neg,
      hψtime.neg, hψspace.mono (fun y hy => hy.neg), hneggrad, ?_⟩
    · change -ψ t x = -leastUpperRicciAt (S.metric t) x
      rw [hvalue, hell]
    · change parabolicOperatorWithDrift (flowG Q) T (fun _ _ => 0)
        (fun s y => -ψ s y) t x ≤ 6 * K * (-ψ t x)
      rw [hvalue]
      exact hPneg K hellneg hr1K
  have hnonpos :=
    DifferentialGeometry.Analysis.nonpositive_of_linear_reaction_lower_supports_and_cutoffs
      G T hT q (6 * K) (8 * K) (mul_nonneg (by norm_num) hK)
      hcont hinit hqbound hsupport hcut
  intro t ht x
  exact neg_nonpos.mp (hnonpos t ht x)

theorem PartialStandardSolution.leastUpperRicciAt_nonneg
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain) (x : E3) :
    0 ≤ leastUpperRicciAt (S.metric t) x := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  by_cases hp : 0 < t
  · exact least_upperRicci_nonneg_closed S t hp htime.2 t ⟨hp.le, le_rfl⟩ x
  · have hz : t = 0 := le_antisymm (le_of_not_gt hp) htime.1
    rw [hz]
    exact S.leastUpperRicciAt_zero_nonneg x

theorem PartialStandardSolution.curvatureOperator_nonnegative
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain) (x : E3) :
    metricAlgebraicCurvatureTensorAt (S.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone :=
  S.curvatureOperator_nonneg_of_leastUpperRicciAt_nonneg t x
    (S.leastUpperRicciAt_nonneg t ht x)
end DifferentialGeometry.PDE.RicciFlow
