import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.DiniComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.MovingSlope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle (normSq0S)
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {D : RealTimeInterval}

section Topological

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem lInjDomain_subset_of_le
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) {tau rho : ℝ}
    (h : tau ≤ rho) :
    lInjDomain S T x rho ⊆ lInjDomain S T x tau := by
  rintro Z ⟨sigma, hsigma, hmin⟩
  exact ⟨sigma, lt_of_le_of_lt h hsigma, hmin⟩

theorem mem_lInjDomain_of_mem_lMinDomain_of_lt
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    {Z : E} {tau sigma : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : tau < sigma) : Z ∈ lInjDomain S T x tau :=
  ⟨sigma, htau, hmin⟩

end Topological

section PseudoMetric

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem lMinDomain_subset_lInjDomain_iff_lCutDomain_eq_empty
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    {Z : E | (Z, tau) ∈ lMinDomain S T x} ⊆ lInjDomain S T x tau ↔
      lCutDomain S T x tau = ∅ := by
  constructor
  · intro hsub
    rw [Set.eq_empty_iff_forall_notMem]
    intro Z hZ
    obtain ⟨hmin, hnot⟩ := (mem_lCutDomain S T x tau Z).1 hZ
    exact hnot (hsub hmin)
  · intro hempty Z hZ
    by_contra hZnot
    have hcut : Z ∈ lCutDomain S T x tau :=
      (mem_lCutDomain S T x tau Z).2 ⟨hZ, hZnot⟩
    rw [hempty] at hcut
    exact hcut

theorem not_lMinDomain_subset_lInjDomain_of_mem_lCutDomain
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) {Z : E}
    (hZ : Z ∈ lCutDomain S T x tau) :
    ¬ {Z : E | (Z, tau) ∈ lMinDomain S T x} ⊆ lInjDomain S T x tau := by
  intro hsub
  obtain ⟨hmin, hnot⟩ := (mem_lCutDomain S T x tau Z).1 hZ
  exact hnot (hsub hmin)

theorem mem_lMinDomain_of_mem_lInjDomain_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M) {Z : E} {tau sigma : ℝ} (htau : 0 < tau)
    (hsigma : tau ≤ sigma) (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    (Z, tau) ∈ lMinDomain S T x :=
  lMinDomain_down_of_rm S hS K T x Z hmin htau hsigma hRm

end PseudoMetric

section Compact

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem mem_lMinDomain_of_mem_lInjDomain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) {Z : TangentSpace I x} {tau : ℝ} (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain S T x tau) :
    (Z, tau) ∈ lMinDomain S T x := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  exact lMinDomain_down S hS T x Z hmin htau hsigma.le

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Filter
open scoped Topology

variable {f g : ℝ → ℝ} {x d e c : ℝ}

private theorem slope_const_mul (c : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    slope (fun z : ℝ => c * f z) x y = c * slope f x y := by
  rw [slope_def_field, slope_def_field]
  ring

theorem upperRightDiniLE_of_forall_lt
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝[>] x, slope f x y < d + ε) :
    UpperRightDiniLE f x d :=
  fun ε hε => (h ε hε).mono fun _ hy => hy.le

theorem upperRightDiniLE_const_mul (hc : 0 ≤ c)
    (h : UpperRightDiniLE f x d) :
    UpperRightDiniLE (fun y => c * f y) x (c * d) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]
    intro ε hε
    filter_upwards with y
    rw [slope_const_mul]
    simp only [zero_mul, zero_add]
    exact hε.le
  · intro ε hε
    have hεc : 0 < ε / c := div_pos hε hcpos
    filter_upwards [h (ε / c) hεc] with y hy
    rw [slope_const_mul]
    calc c * slope f x y ≤ c * (d + ε / c) :=
          mul_le_mul_of_nonneg_left hy hcpos.le
      _ = c * d + ε := by field_simp

theorem upperRightDiniLE_add
    (hf : UpperRightDiniLE f x d) (hg : UpperRightDiniLE g x e) :
    UpperRightDiniLE (fun y => f y + g y) x (d + e) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith)] with y hfy hgy
  rw [slope_def_field] at hfy hgy ⊢
  have hsplit : ((f y + g y) - (f x + g x)) / (y - x) =
      (f y - f x) / (y - x) + (g y - g x) / (y - x) := by
    ring
  rw [hsplit]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped ENNReal Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [PreconnectedSpace M]
variable {D : RealTimeInterval}

theorem upperRightDiniLE_normalized_riemannianEDistOf_of_lt_two_mul
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T tau K r : ℝ} (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric (T - tau)))
    (hK : 0 ≤ K) (hr : 0 < r) (x y : ℝ → M)
    (hx : ContMDiffAt 𝓘(ℝ, ℝ) I 1 x tau)
    (hy : ContMDiffAt 𝓘(ℝ, ℝ) I 1 y tau)
    (hshort : (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal < 2 * r)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau)) (x tau) z <
          ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau)) (y tau) z <
          ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank ℝ E : ℝ) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    UpperRightDiniLE (fun u : ℝ => (Real.sqrt tau)⁻¹ *
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau
      ((Real.sqrt tau)⁻¹ *
        (2 * ((Module.finrank ℝ E : ℝ) - 1) * K * r +
          Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
            (mfderiv 𝓘(ℝ, ℝ) I x tau (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I x tau (1 : ℝ))) +
          Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
            (mfderiv 𝓘(ℝ, ℝ) I y tau (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I y tau (1 : ℝ))))) :=
  Extinction.Families.upperRightDiniLE_const_mul
    (inv_nonneg.mpr (Real.sqrt_nonneg tau))
    (Extinction.Families.upperRightDiniLE_of_forall_lt fun ε hε =>
      eventually_slope_riemannianEDistOf_lt_of_lt_two_mul
        S hS ht hcomplete hK hr x y hx hy hshort hRic ε hε)

omit [NeZero (Module.finrank ℝ E)] in
theorem upperRightDiniLE_normalized_riemannianEDistOf_of_two_mul_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T tau K r : ℝ} (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric (T - tau)))
    (hr : 0 < r) (x y : ℝ → M)
    (hx : ContMDiffAt 𝓘(ℝ, ℝ) I 1 x tau)
    (hy : ContMDiffAt 𝓘(ℝ, ℝ) I 1 y tau)
    (hlong : 2 * r ≤ (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau)) (x tau) z <
          ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau)) (y tau) z <
          ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank ℝ E : ℝ) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    UpperRightDiniLE (fun u : ℝ => (Real.sqrt tau)⁻¹ *
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau
      ((Real.sqrt tau)⁻¹ *
        (2 * ((Module.finrank ℝ E : ℝ) - 1) * ((2 / 3 : ℝ) * K * r + 1 / r) +
          Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
            (mfderiv 𝓘(ℝ, ℝ) I x tau (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I x tau (1 : ℝ))) +
          Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
            (mfderiv 𝓘(ℝ, ℝ) I y tau (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I y tau (1 : ℝ))))) :=
  Extinction.Families.upperRightDiniLE_const_mul
    (inv_nonneg.mpr (Real.sqrt_nonneg tau))
    (Extinction.Families.upperRightDiniLE_of_forall_lt fun ε hε =>
      eventually_slope_riemannianEDistOf_lt_of_two_mul_le
        S hS ht hcomplete hr x y hx hy hlong hRic ε hε)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped Topology

theorem exists_reducedCost_upperRightDiniLE (n Lm LM : ℝ) (hn : 1 ≤ n)
    (hLm : 0 ≤ Lm) :
    ∃ U : ℝ → ℝ,
      U 0 = 0 ∧ U 1 = 1 ∧ ContinuousOn U (Icc (0 : ℝ) 1) ∧
        (∀ c ∈ Ioc (0 : ℝ) 1, AbsolutelyContinuousOnInterval U c 1) ∧
        ∀ t ∈ Ioo (0 : ℝ) 1, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
          slope U t s ≤
            ((4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) +
                4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
              Real.sqrt (Lm + 1) +
            Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1) + ε := by
  refine ⟨fun s : ℝ => s, rfl, rfl, continuousOn_id, ?_, ?_⟩
  · intro c _hc
    exact (LipschitzWith.id.lipschitzOnWith).absolutelyContinuousOnInterval
  · intro t ht ε hε
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hp34 : 1 ≤ t ^ (-(3 / 4) : ℝ) := by
      rw [Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le]
      exact Real.one_le_rpow (by rwa [one_le_inv₀ ht0]) (by norm_num)
    have hp14 : 0 ≤ t ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg ht0.le _
    have hp1 : 0 ≤ t ^ ((1 / 4) : ℝ) := Real.rpow_nonneg ht0.le _
    have hsq : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hcoef : 1 ≤ 4 + 2 * (n - 1) + Real.sqrt 3 := by linarith
    have hlm : 1 ≤ Real.sqrt (Lm + 1) := by
      rw [Real.one_le_sqrt]
      linarith
    have hLMnn : 0 ≤ Real.sqrt (LM + 1) := Real.sqrt_nonneg _
    have hmain : 1 ≤ (4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) *
        Real.sqrt (Lm + 1) := by
      have h1 : (1 : ℝ) ≤ (4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) :=
        by simpa using mul_le_mul hcoef hp34 zero_le_one (by linarith)
      have h2 : (1 : ℝ) ≤ ((4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ)) *
          Real.sqrt (Lm + 1) :=
        by simpa using mul_le_mul h1 hlm zero_le_one (by linarith)
      linarith
    have hrest : 0 ≤ 4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) * Real.sqrt (Lm + 1) :=
      mul_nonneg (mul_nonneg (by linarith) hp14) (le_trans zero_le_one hlm)
    have hrest' : 0 ≤ 3 * t ^ ((1 / 4) : ℝ) * Real.sqrt (Lm + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hp1) (le_trans zero_le_one hlm)
    have htail : 0 ≤ Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1) :=
      mul_nonneg (mul_nonneg hsq (le_trans zero_le_one hp34)) hLMnn
    have hexpand :
        ((4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) +
            4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
            Real.sqrt (Lm + 1) =
          (4 + 2 * (n - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) * Real.sqrt (Lm + 1) +
            4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) * Real.sqrt (Lm + 1) +
            3 * t ^ ((1 / 4) : ℝ) * Real.sqrt (Lm + 1) := by
      ring
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hslope : slope (fun r : ℝ => r) t s = 1 := by
      rw [slope_def_field]
      exact div_self (sub_ne_zero.mpr (ne_of_gt hs))
    rw [hslope]
    rw [hexpand]
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
