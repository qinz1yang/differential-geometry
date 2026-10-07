import DifferentialGeometry.Geometry.Hyperbolic.TruncationBall
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.MetricSpace.Bounded
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Topology.Manifold.HalfLine

set_option autoImplicit false

noncomputable section

open Set Manifold GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

universe u

private theorem riemannianEDistOf_cuspMap_radial_le_of_le
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (x : Torus) (a b : EuclideanHalfSpace 1)
    (hab : a.val 0 ≤ b.val 0) :
    riemannianEDistOf H.metric (Tr.cuspMap i (x, a)) (Tr.cuspMap i (x, b)) ≤
      ENNReal.ofReal (b.val 0 - a.val 0) := by
  let γ : ℝ → H.Carrier := Tr.cuspMap i ∘
    (fun t => (x, Topology.Manifold.halfSpaceOneLift t))
  have hlift : ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ Topology.Manifold.halfSpaceOneLift
      (Icc (a.val 0) (b.val 0)) :=
    Topology.Manifold.contMDiffOn_halfSpaceOneLift.mono
      (fun _ ht => a.property.trans ht.1)
  have hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ (Icc (a.val 0) (b.val 0)) :=
    ((Tr.cuspEmbedding i).contMDiff.comp_contMDiffOn
      (contMDiffOn_const.prodMk hlift)).of_le (by norm_num)
  have hspeed : ∀ t ∈ Ioo (a.val 0) (b.val 0),
      Real.sqrt (H.metric.inner (γ t) (mfderiv 𝓘(ℝ) (𝓡 3) γ t 1)
        (mfderiv 𝓘(ℝ) (𝓡 3) γ t 1)) ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := a.property.trans_lt ht.1
    let L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
    have hmaps : MapsTo L (Ici 0) (range (𝓡∂ 1)) := by
      intro r hr
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hr
    have hdwithin := ((𝓡∂ 1).hasMFDerivWithinAt_symm (hmaps ht0.le)).comp t
      L.toContinuousLinearMap.hasMFDerivWithinAt hmaps
    have hd : HasMFDerivAt 𝓘(ℝ) (𝓡∂ 1) Topology.Manifold.halfSpaceOneLift t
        L.toContinuousLinearMap := by
      have h := hdwithin.hasMFDerivAt (Ici_mem_nhds ht0)
      change HasMFDerivAt 𝓘(ℝ) (𝓡∂ 1) Topology.Manifold.halfSpaceOneLift t
        ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))).comp
          L.toContinuousLinearMap) at h
      exact h.congr_mfderiv (by ext r; rfl)
    have hp : MDifferentiableAt 𝓘(ℝ) halfCollarModel
        (fun r => (x, Topology.Manifold.halfSpaceOneLift r)) t :=
      mdifferentiableAt_const.prodMk hd.mdifferentiableAt
    let v : TangentSpace halfCollarModel (x, Topology.Manifold.halfSpaceOneLift t) :=
      (0, L 1)
    have hpair : mfderiv 𝓘(ℝ) halfCollarModel
        (fun r => (x, Topology.Manifold.halfSpaceOneLift r)) t 1 = v := by
      rw [mfderiv_prodMk mdifferentiableAt_const hd.mdifferentiableAt,
        mfderiv_const, hd.mfderiv]
      rfl
    have hsq : H.metric.inner (γ t) (mfderiv 𝓘(ℝ) (𝓡 3) γ t 1)
        (mfderiv 𝓘(ℝ) (𝓡 3) γ t 1) = 1 := by
      calc
        _ = (Tr.cusp i).metric.inner (x, Topology.Manifold.halfSpaceOneLift t) v v := by
          dsimp only [γ]
          rw [mfderiv_comp_apply t
            ((Tr.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp)) hp, hpair]
          exact Tr.cuspIsometry i (x, Topology.Manifold.halfSpaceOneLift t) v v
        _ = 1 := by
          rw [(Tr.cusp i).metric_formula]
          simp only [Fin.isValue, PiLp.equivOfUnique_symm_apply, uniqueElim_const,
            mul_one, add_eq_left, mul_eq_zero, Real.exp_ne_zero, false_or, L, v]
          exact map_zero ((Tr.cusp i).torusMetric.inner x 0)
    rw [hsq, Real.sqrt_one]
  have hdist := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound
    H.metric hab hγ hspeed
  have hrepr (v : EuclideanHalfSpace 1) :
      Topology.Manifold.halfSpaceOneLift (v.val 0) = v := by
    rw [Topology.Manifold.halfSpaceOneLift_eq]
    have heq : (⟨max 0 (v.val 0), le_max_left 0 (v.val 0)⟩ : Ici (0 : ℝ)) =
        Topology.Manifold.halfSpaceOneHomeomorph v := Subtype.ext (max_eq_right v.property)
    rw [heq]
    exact Topology.Manifold.halfSpaceOneHomeomorph.symm_apply_apply v
  simpa only [γ, Function.comp_apply, hrepr, ENNReal.ofReal_one, one_mul] using hdist

private theorem riemannianEDistOf_cuspMap_radial_le
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (x : Torus) (a b : EuclideanHalfSpace 1) :
    riemannianEDistOf H.metric (Tr.cuspMap i (x, a)) (Tr.cuspMap i (x, b)) ≤
      ENNReal.ofReal |a.val 0 - b.val 0| := by
  rcases le_total (a.val 0) (b.val 0) with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using
      riemannianEDistOf_cuspMap_radial_le_of_le Tr i x a b hab
  · rw [riemannianEDistOf_comm]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hba)] using
      riemannianEDistOf_cuspMap_radial_le_of_le Tr i x b a hba

theorem ofReal_abs_depth_sub_le_riemannianEDistOf_cuspMap
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (p q : CuspHalfSpace) :
    ENNReal.ofReal |p.2.val 0 - q.2.val 0| ≤
      riemannianEDistOf H.metric (Tr.cuspMap i p) (Tr.cuspMap i q) := by
  by_cases heq : p.2.val 0 = q.2.val 0
  · rw [heq, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hle (x y : CuspHalfSpace) :
      ENNReal.ofReal (x.2.val 0 - y.2.val 0) ≤
        riemannianEDistOf H.metric (Tr.cuspMap i x) (Tr.cuspMap i y) := by
    by_contra h
    have hd := lt_of_not_ge h
    obtain ⟨r, hdr, hrgap⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hd)
    have hr : 0 < r := ENNReal.toReal_nonneg.trans_lt hdr
    have hrs : r < x.2.val 0 := by
      have hy := y.2.property
      linarith
    have hyball : Tr.cuspMap i y ∈ riemannianBallOf H.metric (Tr.cuspMap i x) r :=
      (ENNReal.lt_ofReal_iff_toReal_lt hd.ne_top).mpr hdr
    obtain ⟨z, hz, hzy⟩ := Tr.riemannianBallOf_cuspMap_subset_tail i x hr hrs hyball
    have hzy' : z = y := (Tr.cuspEmbedding i).isEmbedding.injective hzy
    rw [hzy'] at hz
    change x.2.val 0 - r < y.2.val 0 at hz
    linarith
  rcases le_total (q.2.val 0) (p.2.val 0) with hpq | hqp
  · rw [abs_of_nonneg (sub_nonneg.mpr hpq)]
    exact hle p q
  · rw [abs_of_nonpos (sub_nonpos.mpr hqp), neg_sub,
      riemannianEDistOf_comm H.metric (Tr.cuspMap i p) (Tr.cuspMap i q)]
    exact hle q p

theorem riemannianEDistOf_cuspMap_radial
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (x : Torus) (a b : EuclideanHalfSpace 1) :
    riemannianEDistOf H.metric (Tr.cuspMap i (x, a)) (Tr.cuspMap i (x, b)) =
      ENNReal.ofReal |a.val 0 - b.val 0| :=
  le_antisymm (riemannianEDistOf_cuspMap_radial_le Tr i x a b)
    (Tr.ofReal_abs_depth_sub_le_riemannianEDistOf_cuspMap i (x, a) (x, b))

private theorem exists_pos_core_distance_bound {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (o : H.Carrier) :
    ∃ C > 0, ∀ q, riemannianEDistOf H.metric o (Tr.inclusion q) ≤ ENNReal.ofReal C := by
  let _ : LocallyCompactSpace H.Carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  have hc : IsCompact (range Tr.inclusion) := isCompact_range Tr.inclusion.continuous
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 o
  refine ⟨C, hC, fun q => ?_⟩
  have hd : dist (Tr.inclusion q) o ≤ C := hbound (mem_range_self q)
  rw [dist_comm] at hd
  change edist o (Tr.inclusion q) ≤ ENNReal.ofReal C
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hd

theorem exists_core_and_cusp_distance_bound {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (o : H.Carrier) :
    ∃ C > 0,
      (∀ q, riemannianEDistOf H.metric o (Tr.inclusion q) ≤ ENNReal.ofReal C) ∧
      ∀ (i : Fin Tr.count) (p : CuspHalfSpace),
        riemannianEDistOf H.metric o (Tr.cuspMap i p) ≤
          ENNReal.ofReal (C + p.2.val 0) := by
  obtain ⟨C, hC, hcore⟩ := exists_pos_core_distance_bound Tr o
  refine ⟨C, hC, hcore, ?_⟩
  intro i p
  have hr := (Tr.riemannianEDistOf_cuspMap_radial i p.1 halfZero p.2).le
  have hrad : riemannianEDistOf H.metric (Tr.cuspMap i (p.1, halfZero))
      (Tr.cuspMap i p) ≤ ENNReal.ofReal (p.2.val 0) := by
    change riemannianEDistOf H.metric (Tr.cuspMap i (p.1, halfZero))
      (Tr.cuspMap i p) ≤ ENNReal.ofReal |0 - p.2.val 0| at hr
    simpa only [zero_sub, abs_neg, abs_of_nonneg p.2.property] using hr
  calc
    _ ≤ riemannianEDistOf H.metric o (Tr.cuspMap i (p.1, halfZero)) +
        riemannianEDistOf H.metric (Tr.cuspMap i (p.1, halfZero)) (Tr.cuspMap i p) :=
      riemannianEDistOf_triangle H.metric o _ _
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal (p.2.val 0) := by
      apply add_le_add _ hrad
      rw [Tr.cusp_zero]
      exact hcore _
    _ = ENNReal.ofReal (C + p.2.val 0) :=
      (ENNReal.ofReal_add hC.le p.2.property).symm

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
