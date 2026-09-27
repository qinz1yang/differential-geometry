import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.shifted_leastUpperRicci_upper_support
    (S : PartialStandardSolution)
    (a t₀ : ℝ) (ha : 0 ≤ a) (hat : a < t₀)
    (hTl : ENNReal.ofReal t₀ < S.lifetime) :
    let Q := S.toSolutionOn.timeShift a
    let G := flowG Q
    let τ := t₀ - a
    let u : ℝ → E3 → ℝ :=
      fun s x => leastUpperRicciAt (S.metric (s + a)) x
    ∀ t ∈ Icc 0 τ, 0 < t → ∀ x : E3,
      Nonempty (ParabolicUpperSupportAt G τ (fun _ _ => 0) u t x) := by
  let Q := S.toSolutionOn.timeShift a
  let G := flowG Q
  let τ : ℝ := t₀ - a
  let u : ℝ → E3 → ℝ :=
    fun s x => leastUpperRicciAt (S.metric (s + a)) x
  have hτ : 0 < τ := sub_pos.mpr hat
  have hupper (s : ℝ) (hs : s ≤ τ) : s + a ≤ t₀ := by
    change s ≤ t₀ - a at hs
    linarith only [hs]
  have hcarrier : ∀ s ∈ Icc 0 τ, s + a ∈ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier
      S.lifetime S.lifetime_pos (s + a)).mpr
        ⟨add_nonneg hs.1 ha,
          (ENNReal.ofReal_le_ofReal (hupper s hs.2)).trans_lt hTl⟩
  have hsub :
      Icc 0 τ ⊆
        ((lifetimeInterval S.lifetime S.lifetime_pos).timeShift a).carrier := by
    intro s hs
    exact hcarrier s hs
  have hreg :
      Ioc 0 τ ⊆
        ((lifetimeInterval S.lifetime S.lifetime_pos).timeShift a).regular := by
    intro s hs
    change s + a ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular
    exact (mem_lifetimeInterval_regular
      S.lifetime S.lifetime_pos (s + a)).mpr
        ⟨add_pos_of_pos_of_nonneg hs.1 ha,
          (ENNReal.ofReal_le_ofReal (hupper s hs.2)).trans_lt hTl⟩
  have hQ : IsSolutionOn Q := isSolutionOn_timeShift S.isSolutionOn a
  have hQs := smoothOfSolution Q hQ
  have hdim (y : E3) :
      Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 :=
    finrank_euclideanSpace_fin
  have hsec (s : ℝ) (y : E3) :
      upperRicciTensorAt (Q.base.metric s) y =
        ricciUpperBoundSec Q s y := by
    rw [ricci_upper_bound_sec_at_point]
    change
      (metricScalarAt (Q.base.metric s) y / 2) •
          metricTensorField (Q.base.metric s) y -
        metricRicciAt (Q.base.metric s) y =
      ((1 / 2 : ℝ) * metricScalarAt (Q.base.metric s) y) •
          metricTensorField (Q.base.metric s) y -
        metricRicci (Q.base.metric s) y
    rw [metricRicci_apply]
    congr 1
    congr 1
    ring
  change ∀ t ∈ Icc 0 τ, 0 < t → ∀ x : E3,
    Nonempty (ParabolicUpperSupportAt G τ (fun _ _ => 0) u t x)
  intro t ht hp x
  have htOriginal : t + a ∈ S.domain := hcarrier t ht
  obtain ⟨basis, r1, r2, r3, horth, h21, h32, hdiag,
    hmin, _hunit, _hRayleigh, hleft, hright⟩ :=
      exists_ordered_ricci_frame_leastUpperRicciAt (Q.base.metric t) x
  let ell : ℝ := (1 / 2 : ℝ) * Q.scalar t x - r1
  have hell : u t x = ell := by
    change leastUpperRicciAt (Q.base.metric t) x = ell
    rw [hmin]
    change metricScalarAt (Q.base.metric t) x / 2 - r1 =
      (1 / 2 : ℝ) * metricScalarAt (Q.base.metric t) x - r1
    ring
  have hleft' : ∀ z : TangentSpace (𝓡 3) x,
      ricciUpperBoundSec Q t x (vec2 (I := 𝓡 3) (basis 0) z) =
        ((1 / 2 : ℝ) * Q.scalar t x - r1) *
          (Q.base.metric t).inner x (basis 0) z := by
    intro z
    change ricciUpperBoundSec Q t x
      (vec2 (I := 𝓡 3) (basis 0) z) =
        ell * (Q.base.metric t).inner x (basis 0) z
    rw [← hsec t x, ← hell]
    exact hleft z
  have hright' : ∀ z : TangentSpace (𝓡 3) x,
      ricciUpperBoundSec Q t x (vec2 (I := 𝓡 3) z (basis 0)) =
        ((1 / 2 : ℝ) * Q.scalar t x - r1) *
          (Q.base.metric t).inner x z (basis 0) := by
    intro z
    change ricciUpperBoundSec Q t x
      (vec2 (I := 𝓡 3) z (basis 0)) =
        ell * (Q.base.metric t).inner x z (basis 0)
    rw [← hsec t x, ← hell]
    exact hright z
  have hdiagQ : ∀ i j : Fin 3,
      Q.ricciAt t x (vec2 (I := 𝓡 3) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j := hdiag
  have htrace : Q.scalar t x = r1 + r2 + r3 := by
    have hh := metricTrace_comp_orthonormal basis horth (Q.ricciAt t x)
    have hcomponents :
        (fun i j : Fin 3 =>
          Q.ricciAt t x (vec2 (I := 𝓡 3) (basis i) (basis j))) =
            ricciDiag3 r1 r2 r3 := by
      funext i j
      exact hdiagQ i j
    rw [hcomponents] at hh
    rw [Q.scalar_eq_metricTrace]
    simpa [ricciScal3, ricciDiag3, Fin.sum_univ_three] using hh
  have hRlower : 1 ≤ Q.scalar t x :=
    S.one_le_scalar (t + a) htOriginal x
  have hr1lower : Q.scalar t x / 3 ≤ r1 := by
    rw [htrace]
    linarith only [h21, h32]
  have hr1pos : 0 < r1 := by
    have hRpos : 0 < Q.scalar t x := lt_of_lt_of_le zero_lt_one hRlower
    exact (div_pos hRpos (by norm_num : (0 : ℝ) < 3)).trans_le hr1lower
  have hellnonneg : 0 ≤ ell := by
    rw [← hell]
    exact S.leastUpperRicciAt_nonneg (t + a) htOriginal x
  obtain ⟨V, hV, _hcovV, hψvalue, hψtime, hψspace, hψgrad, hPψ, _hPneg⟩ :=
    exists_rayleigh_support_operator_in_ordered_frame Q hQs τ hτ hdim
      hsub hreg t ⟨hp, ht.2⟩ x basis r1 r2 r3
      horth h21 h32 hdiagQ hleft' hright'
  let ψ : ℝ → E3 → ℝ := fun s y => ell +
    (ricciUpperBoundSec Q s y (vec2 (I := 𝓡 3) (V y) (V y)) -
      ell * (Q.base.metric s).inner y (V y) (V y)) /
        (Q.base.metric s).inner y (V y) (V y)
  have hvalue : ψ t x = ell := hψvalue
  have hVcont : Continuous (fun y : E3 => (V y : E3)) :=
    (contMDiff_vectorSpace_iff_contDiff.mp V.contMDiff).continuous
  have hVne : (V x : E3) ≠ 0 := by
    rw [hV]
    exact basis.ne_zero 0
  have hcompare :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := E3) τ] (t, x),
        u p.1 p.2 ≤ ψ p.1 p.2 := by
    have hsnd : Tendsto (fun p : ℝ × E3 => p.2)
        (𝓝[spacetimeSlab (M := E3) τ] (t, x)) (𝓝 x) :=
      continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards
      [hsnd.eventually (hVcont.continuousAt.eventually_ne hVne)] with p hpV
    change leastUpperRicciAt (Q.base.metric p.1) p.2 ≤
      ell +
        (ricciUpperBoundSec Q p.1 p.2
            (vec2 (I := 𝓡 3) (V p.2) (V p.2)) -
          ell * (Q.base.metric p.1).inner p.2 (V p.2) (V p.2)) /
            (Q.base.metric p.1).inner p.2 (V p.2) (V p.2)
    rw [← hsec p.1 p.2,
      shifted_upperRicciRayleighAt_eq
        (Q.base.metric p.1) p.2 (V p.2) hpV ell]
    exact leastUpperRicciAt_le_rayleigh
      (Q.base.metric p.1) p.2 (V p.2) hpV
  have hPnonneg :
      0 ≤ parabolicOperatorWithDrift G τ (fun _ _ => 0) ψ t x := by
    have hprod : 0 ≤ 2 * r1 * ell :=
      mul_nonneg (mul_nonneg (by norm_num) hr1pos.le) hellnonneg
    exact hprod.trans hPψ
  refine ⟨{
    upperSupport := ψ
    eq_at := hvalue.trans hell.symm
    upper_nhds := hcompare
    time_diff := hψtime
    space_diff_nhds := hψspace
    grad_diff := hψgrad
    operator_nonneg := hPnonneg
  }⟩

end DifferentialGeometry.PDE.RicciFlow
