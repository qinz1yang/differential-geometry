import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem hasDerivAt_lRegularizedAction_tail_eq_endpoint_inner
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T c b : ℝ) (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc c b))
    (hfix : ∀ u, f u c = f 0 c) :
    HasDerivAt (fun u ↦ lRegularizedAction S T (f u) c b)
      ((S.base.metric (T - b ^ 2)).inner (f 0 b)
        (lVelocity (I := I) (fun u ↦ f u b) 0)
        (lVelocity (I := I) (f 0) b)) 0 := by
  have ht : ∀ s ∈ uIcc c b, T - s ^ 2 ∈ D.regular := fun s hs ↦ (hgeo s hs).1
  have hzero : lVelocity (I := I) (fun u ↦ f u c) 0 = 0 := by
    have heq : (fun u ↦ f u c) = fun _ ↦ f 0 c := funext hfix
    rw [heq, lVelocity, mfderiv_const]
    rfl
  have heuler : ∀ s ∈ uIcc c b,
      lRegularizedEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u ↦ f u s) 0) = 0 := by
    intro s hs
    simp only [lRegularizedEulerPair]
    rw [(hgeo s hs).2.2.2, sub_self, map_zero]
  have hint : (∫ s in c..b,
      lRegularizedEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u ↦ f u s) 0)) = 0 := by
    calc
      _ = ∫ _s in c..b, (0 : ℝ) :=
        intervalIntegral.integral_congr fun s hs ↦ heuler s hs
      _ = 0 := intervalIntegral.integral_zero
  have hfirst := lRegularizedAction_first_variation (I := I) S hS T f hf c b ht
  simpa only [hzero, map_zero, zero_apply, hint, sub_zero] using hfirst

theorem redLength_upper_support_of_fixed_germ_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : ℝ) {c : ℝ} (hc : 0 < c) (hcb : c < b)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hmin : lRegularizedAction S T alpha 0 b = lCost S T (alpha 0) (alpha b) (b ^ 2))
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (hcenter : EqOn (f 0) alpha (Icc c b))
    (hgeo : IsLRegularizedGeodesicOn S T (f 0) (Icc c b))
    (hfix : ∀ u, f u =ᶠ[𝓝 c] alpha)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (hRm : ∃ B : ℝ, ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (S.base.metric t) y 4 (S.base.rm04 t y) ≤ B) :
    let phi : ℝ → ℝ := fun u ↦
      (lRegularizedAction S T alpha 0 c + lRegularizedAction S T (f u) c b) / (2 * b)
    ContDiff ℝ 2 phi ∧
      phi 0 = redLength S T (alpha 0) (alpha b) (b ^ 2) ∧
      (∀ u, redLength S T (alpha 0) (f u b) (b ^ 2) ≤ phi u) ∧
      HasDerivAt phi
        ((S.base.metric (T - b ^ 2)).inner (f 0 b)
          (lVelocity (I := I) (fun u ↦ f u b) 0)
          (lVelocity (I := I) (f 0) b) / (2 * b)) 0 := by
  classical
  have hb : 0 < b := hc.trans hcb
  have hcentral : lRegularizedAction S T (f 0) c b =
      lRegularizedAction S T alpha c b := by
    apply lRegularizedAction_congr (I := I) S T (f 0) alpha c b
    intro s hs
    rw [uIoo_of_le hcb.le] at hs
    exact hcenter ⟨hs.1.le, hs.2.le⟩
  have hheadInt := lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
    T 0 c alpha halpha (by
      intro s hs
      rw [uIcc_of_le hc.le] at hs
      exact hback s ⟨hs.1, hs.2.trans hcb.le⟩)
  have htailInt := lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
    T c b alpha halpha (by
      intro s hs
      rw [uIcc_of_le hcb.le] at hs
      exact hback s ⟨hc.le.trans hs.1, hs.2⟩)
  have hadd := lRegularizedAction_add (I := I) S T alpha 0 c b hheadInt htailInt
  let phi : ℝ → ℝ := fun u ↦
    (lRegularizedAction S T alpha 0 c + lRegularizedAction S T (f u) c b) / (2 * b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ht : ∀ s ∈ uIcc c b, T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact (hgeo s (by simpa only [uIcc_of_le hcb.le] using hs)).1
    exact (contDiff_const.add
      (contDiff_lRegularizedAction (I := I) S hS T f hf c b ht)).div_const (2 * b)
  · simp only [hcentral, hadd, hmin, redLength, Real.sqrt_sq hb.le]
  · intro u
    have hfu : ContMDiff 𝓘(ℝ, ℝ) I 1 (f u) :=
      (hf.comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
    let eta : ℝ → M := (Iic c).piecewise alpha (f u)
    have heta : ContMDiff 𝓘(ℝ, ℝ) I 1 eta :=
      halpha.piecewise_Iic hfu (hfix u).symm
    have heta0 : eta 0 = alpha 0 := by
      simp only [eta, Set.piecewise_eq_of_mem (Iic c) alpha (f u)
        (hc.le : (0 : ℝ) ∈ Iic c)]
    have hetab : eta b = f u b := by
      simp only [eta, Set.piecewise_eq_of_notMem (Iic c) alpha (f u)
        (not_le.mpr hcb : b ∉ Iic c)]
    have hetaHead : lRegularizedAction S T eta 0 c = lRegularizedAction S T alpha 0 c := by
      apply lRegularizedAction_congr
      intro s hs
      rw [uIoo_of_le hc.le] at hs
      exact Set.piecewise_eq_of_mem (Iic c) alpha (f u) (hs.2.le : s ∈ Iic c)
    have hetaTail : lRegularizedAction S T eta c b = lRegularizedAction S T (f u) c b := by
      apply lRegularizedAction_congr
      intro s hs
      rw [uIoo_of_le hcb.le] at hs
      exact Set.piecewise_eq_of_notMem (Iic c) alpha (f u) (not_le.mpr hs.1 : s ∉ Iic c)
    have hetaHeadInt := lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 c eta heta (by
        intro s hs
        rw [uIcc_of_le hc.le] at hs
        exact hback s ⟨hs.1, hs.2.trans hcb.le⟩)
    have hetaTailInt := lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
      T c b eta heta (by
        intro s hs
        rw [uIcc_of_le hcb.le] at hs
        exact hback s ⟨hc.le.trans hs.1, hs.2⟩)
    obtain ⟨B, hB⟩ := hRm
    have hbdd := lCost_competitors_bddBelow_of_rm_on_carrier
      S hS B T b hb.le (alpha 0) (f u b) hback hB
    have hcost : lCost S T (alpha 0) (f u b) (b ^ 2) ≤ lRegularizedAction S T eta 0 b := by
      apply csInf_le hbdd
      refine ⟨eta, heta, heta0, ?_, ?_⟩
      · simpa only [Real.sqrt_sq hb.le] using hetab
      · rw [lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T eta
          (b ^ 2) (sq_nonneg b), Real.sqrt_sq hb.le]
    have hetaAdd := lRegularizedAction_add S T eta 0 c b hetaHeadInt hetaTailInt
    rw [hetaHead, hetaTail] at hetaAdd
    have hbound := hcost.trans_eq hetaAdd.symm
    simpa only [redLength, Real.sqrt_sq hb.le, phi] using
      div_le_div_of_nonneg_right hbound (by positivity : 0 ≤ 2 * b)
  · have hd := hasDerivAt_lRegularizedAction_tail_eq_endpoint_inner S hS T c b f hf
      (by simpa only [uIcc_of_le hcb.le] using hgeo)
      (fun u ↦ (hfix u).self_of_nhds.trans (hfix 0).self_of_nhds.symm)
    convert (hd.const_add (lRegularizedAction S T alpha 0 c)).div_const (2 * b) using 1


theorem exists_redLength_upper_support_of_fixed_germ_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : ℝ) {c : ℝ} (hc : 0 < c) (hcb : c < b)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hmin : lRegularizedAction S T alpha 0 b = lCost S T (alpha 0) (alpha b) (b ^ 2))
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (hcenter : EqOn (f 0) alpha (Icc c b))
    (hgeo : IsLRegularizedGeodesicOn S T (f 0) (Icc c b))
    (hfix : ∀ u, f u =ᶠ[𝓝 c] alpha)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (hRm : ∃ B : ℝ, ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ B) :
    ∃ phi : ℝ → ℝ,
      phi 0 = redLength S T (alpha 0) (alpha b) (b ^ 2) ∧
      (∀ u, redLength S T (alpha 0) (f u b) (b ^ 2) ≤ phi u) ∧
      HasDerivAt phi
        ((S.base.metric (T - b ^ 2)).inner (f 0 b)
          (lVelocity (I := I) (fun u ↦ f u b) 0)
          (lVelocity (I := I) (f 0) b) / (2 * b)) 0 := by
  refine ⟨fun u ↦
    (lRegularizedAction S T alpha 0 c + lRegularizedAction S T (f u) c b) / (2 * b), ?_⟩
  exact (redLength_upper_support_of_fixed_germ_variation (I := I) S hS T b hc hcb
    alpha halpha hmin f hf hcenter hgeo hfix hback hRm).2


end DifferentialGeometry.PDE.RicciFlow.Perelman
