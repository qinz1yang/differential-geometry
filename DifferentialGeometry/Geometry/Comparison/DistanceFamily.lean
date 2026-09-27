import DifferentialGeometry.Geometry.Comparison.Variation.ArcLengthContinuity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Continuity
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FixedBasePartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Family.LocalEquivalence
import DifferentialGeometry.Geometry.Comparison.LocalDistanceComparison
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.CompactFamily
import DifferentialGeometry.Topology.Order.Interval
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Exponential Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem continuousAt_arcLength_intrinsicGeodesic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g₀ : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g₀)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {α β t : ℝ} (ht : t ∈ Ioo α β) (hJ : Icc α β ⊆ J)
    (x : M) (v₀ : TangentSpace I x) :
    ContinuousAt (fun p : ℝ × TangentSpace I x =>
      arcLength (I := I) (g p.1) (intrinsicGeodesic (I := I) g₀ hEnorm x p.2) 0 1)
      (t, v₀) := by
  obtain ⟨ρ, hρ, hc⟩ := intrinsicGeodesic_tangentLift_jointContinuity
    (I := I) g₀ hEnorm x v₀
  let K : Set (ℝ × TangentSpace I x) := Icc α β ×ˢ Metric.closedBall v₀ (ρ / 2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall v₀ (ρ / 2))
  have hτ : ContinuousOn (fun p : ℝ × TangentSpace I x => p.1) K :=
    continuous_fst.continuousOn
  have hτJ : MapsTo (fun p : ℝ × TangentSpace I x => p.1) K J := fun _ hp => hJ hp.1
  have hγ : ContinuousOn (fun p : (ℝ × TangentSpace I x) × ℝ =>
      (⟨intrinsicGeodesic (I := I) g₀ hEnorm x p.1.2 p.2,
        mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g₀ hEnorm x p.1.2) p.2 (1 : ℝ)⟩ :
        TangentBundle I M)) (K ×ˢ Icc (0 : ℝ) 1) := by
    apply hc.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
    intro p hp
    exact ⟨(Metric.closedBall_subset_ball (by linarith : ρ / 2 < ρ)) hp.1.2, hp.2⟩
  have hlen := continuousOn_arcLength_of_continuous_tangentLift hK zero_le_one g hg
    (fun p : ℝ × TangentSpace I x => p.1) hτ hτJ
    (fun p => intrinsicGeodesic (I := I) g₀ hEnorm x p.2) hγ
  have hKn : K ∈ nhds (t, v₀) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (Metric.closedBall_mem_nhds _ (by linarith))
  exact hlen.continuousAt hKn

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem arcLength_intrinsicGeodesic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) :
    arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) 0 1 =
      Real.sqrt (g.inner x v v) := by
  have heq : arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) 0 1 =
      ∫ _q in (0 : ℝ)..1, Real.sqrt (g.inner x v v) := by
    apply intervalIntegral.integral_congr
    intro q _hq
    exact congrArg Real.sqrt (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x v q)
  rw [heq, intervalIntegral.integral_const]
  simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_continuous_distance_upper_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {α β t : ℝ} (ht : t ∈ Ioo α β) (hJ : Icc α β ⊆ J)
    (hEnorm : IsMetricNorm (I := I) (M := M) (g t))
    (O x : M) (hfin : Manifold.riemannianEDist I O x ≠ ⊤) :
    ∃ F : ℝ × M → ℝ, ContinuousAt F (t, x) ∧
      F (t, x) = (Manifold.riemannianEDist I O x).toReal ∧
      ∀ᶠ p in nhds (t, x), riemannianEDistOf (I := I) (g p.1) O p.2 ≤ ENNReal.ofReal (F p) := by
  obtain ⟨v, hvexp, hvnorm⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
    (I := I) (g t) hEnorm O x hfin
  let B := standardDiagonalInverseBranch (I := I) (g t) hEnorm x
  let w : M → TangentSpace I x := fun y =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      (B.fixedBasePartialDiffeomorph.symm y)
  have hwx : w x = 0 := by
    simp only [w, B.fixedBasePartialDiffeomorph_symm_center, map_zero]
  have hw : ContinuousAt w x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.continuous.continuousAt.comp
      (B.fixedBasePartialDiffeomorph.symm.contMDiffOn_toFun.continuousOn.continuousAt
        (B.fixedBasePartialDiffeomorph.open_target.mem_nhds
          B.fixedBasePartialDiffeomorph_center_mem_target))
  let γ := intrinsicGeodesic (I := I) (g t) hEnorm O v
  let δ := fun y => intrinsicGeodesic (I := I) (g t) hEnorm x (w y)
  let F : ℝ × M → ℝ := fun p => arcLength (I := I) (g p.1) γ 0 1 +
    arcLength (I := I) (g p.1) (δ p.2) 0 1
  have hleft := continuousAt_arcLength_intrinsicGeodesic (I := I) (g t) hEnorm g hg ht hJ O v
  have hright := continuousAt_arcLength_intrinsicGeodesic (I := I) (g t) hEnorm g hg ht hJ x (0 : TangentSpace I x)
  have hcl : ContinuousAt (fun p : ℝ × M => arcLength (I := I) (g p.1) γ 0 1) (t, x) :=
    hleft.comp_of_eq (f := fun p : ℝ × M => (p.1, v))
      (continuousAt_fst.prodMk
        (continuousAt_const : ContinuousAt (fun _ : ℝ × M => v) (t, x))) rfl
  have hcr : ContinuousAt (fun p : ℝ × M => arcLength (I := I) (g p.1) (δ p.2) 0 1) (t, x) := by
    have hmap : ContinuousAt (fun p : ℝ × M => (p.1, w p.2)) (t, x) :=
      continuousAt_fst.prodMk (hw.comp_of_eq (f := Prod.snd) continuousAt_snd rfl)
    have hright' : ContinuousAt
      (fun p : ℝ × TangentSpace I x => arcLength (I := I) (g p.1)
        (intrinsicGeodesic (I := I) (g t) hEnorm x p.2) 0 1) (t, w x) := by
      rw [hwx]
      exact hright
    exact hright'.comp_of_eq (f := fun p : ℝ × M => (p.1, w p.2)) hmap rfl
  refine ⟨F, hcl.add hcr, ?_, ?_⟩
  · change arcLength (I := I) (g t) γ 0 1 + arcLength (I := I) (g t) (δ x) 0 1 = _
    simp only [γ, δ, arcLength_intrinsicGeodesic, hwx, map_zero,
      Real.sqrt_zero, add_zero]
    exact hvnorm
  · have hnear : ∀ᶠ p : ℝ × M in nhds (t, x),
        p.2 ∈ B.fixedBasePartialDiffeomorph.target :=
      continuousAt_snd.preimage_mem_nhds
        (B.fixedBasePartialDiffeomorph.open_target.mem_nhds
          B.fixedBasePartialDiffeomorph_center_mem_target)
    filter_upwards [hnear] with p hp
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
      (intrinsicGeodesic_contMDiff (I := I) (g t) hEnorm O v).contMDiffOn.of_le (by simp)
    have hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (δ p.2) (Icc 0 1) :=
      (intrinsicGeodesic_contMDiff (I := I) (g t) hEnorm x (w p.2)).contMDiffOn.of_le (by simp)
    have hjoin : γ 1 = δ p.2 0 := by
      change expMapIntrinsic (I := I) (g t) hEnorm O v =
        intrinsicGeodesic (I := I) (g t) hEnorm x (w p.2) 0
      rw [hvexp, intrinsicGeodesic_zero]
    have hbound := DifferentialGeometry.edistOf_le_two_arcs (I := I) (g p.1)
      zero_le_one zero_le_one hγ hδ hjoin
    have hγ0 : γ 0 = O := intrinsicGeodesic_zero (I := I) (g t) hEnorm O v
    have hδ1 : δ p.2 1 = p.2 := by
      exact B.fixedBasePartialDiffeomorph.right_inv hp
    rw [hγ0, hδ1] at hbound
    have hnn (η : ℝ → M) : 0 ≤ arcLength (I := I) (g p.1) η 0 1 :=
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => Real.sqrt_nonneg _)
    rw [← ENNReal.ofReal_add (hnn γ) (hnn (δ p.2))] at hbound
    exact hbound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_riemannianEDistOf_upper_support_continuousAt_of_nonzero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t : ℝ} (ht : J ∈ nhds t)
    (hcomplete : RiemannianMetricComplete (I := I) (g t))
    (O x : M) (hfin : riemannianEDistOf (I := I) (g t) O x ≠ ⊤) :
    ∃ F : ℝ × M → ℝ, ContinuousAt F (t, x) ∧
      F (t, x) = (riemannianEDistOf (I := I) (g t) O x).toReal ∧
      ∀ᶠ p in nhds (t, x), riemannianEDistOf (I := I) (g p.1) O p.2 ≤ ENNReal.ofReal (F p) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨(g t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨(g t).inner, (g t).contMDiff.continuous, by intro y v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (g t) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  obtain ⟨ε, hε, hεJ⟩ := Metric.mem_nhds_iff.mp ht
  have hwin : Icc (t - ε / 2) (t + ε / 2) ⊆ J := by
    intro s hs
    apply hεJ
    rw [Metric.mem_ball, Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hs.1, hs.2]
  exact exists_continuous_distance_upper_support (I := I) g hg
    (show t ∈ Ioo (t - ε / 2) (t + ε / 2) from ⟨by linarith, by linarith⟩)
    hwin hEnorm O x hfin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_riemannianEDistOf_upper_support_continuousAt
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t : ℝ} (ht : J ∈ nhds t)
    (hcomplete : RiemannianMetricComplete (I := I) (g t))
    (O x : M) (hfin : riemannianEDistOf (I := I) (g t) O x ≠ ⊤) :
    ∃ F : ℝ × M → ℝ, ContinuousAt F (t, x) ∧
      F (t, x) = (riemannianEDistOf (I := I) (g t) O x).toReal ∧
      ∀ᶠ p in nhds (t, x), riemannianEDistOf (I := I) (g p.1) O p.2 ≤ ENNReal.ofReal (F p) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨(g t).toRiemannianMetric⟩
    have hfin' : Manifold.riemannianEDist I O x < ⊤ := lt_top_iff_ne_top.mpr hfin
    obtain ⟨γ, hγ0, hγ1, hγ, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfin' zero_lt_one
    have hOx : O = x := by
      rw [← hγ0, ← hγ1]
      exact TotallyDisconnectedSpace.eq_of_continuous γ hγ.continuous 0 1
    have hdist : Manifold.riemannianEDist I O x = 0 := by
      rw [hOx, Manifold.riemannianEDist_self]
    refine ⟨fun _ => 0, continuousAt_const, ?_, ?_⟩
    · simp [riemannianEDistOf, hdist]
    · have hnear : ∀ᶠ p : ℝ × M in nhds (t, x), p.2 = x :=
        (continuousAt_snd : ContinuousAt (fun p : ℝ × M => p.2) (t, x)).preimage_mem_nhds
          ((isOpen_discrete ({x} : Set M)).mem_nhds (mem_singleton x))
      filter_upwards [hnear] with p hp
      simp only [hp, hOx, riemannianEDistOf_self, ENNReal.ofReal_zero, le_refl]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact exists_riemannianEDistOf_upper_support_continuousAt_of_nonzero
      g hg ht hcomplete O x hfin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_compact_eventually_riemannianEDistOf_le_of_nonzero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hcomplete : RiemannianMetricComplete (I := I) (g t₀))
    (O : M) (r : ℝ) :
    ∃ L : Set M, IsCompact L ∧ ∀ᶠ t in nhdsWithin t₀ J,
      ∀ x : M, riemannianEDistOf (I := I) (g t) O x ≤ ENNReal.ofReal r → x ∈ L := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let R : ℝ := 2 * (max r 0 + 1)
  have hrR : max r 0 < (1 / 2 : ℝ) * R := by dsimp [R]; linarith
  let K : Set M := {x : M |
      riemannianEDistOf (I := I) (g t₀) O x ≤ ENNReal.ofReal R}
  have hK : IsCompact K := RiemannianMetricComplete.closedEBall_isCompact
    (I := I) (M := M) hcomplete O R
  have hc : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hc1 : (1 / 2 : ℝ) ^ 2 < (1 : ℝ) := by norm_num
  have hcomp := eventually_metric_comparison_on_compact
    (I := I) (M := M) g hg ht₀ hK hc1 (show (1 : ℝ) < 2 by norm_num)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcomp] with t ht
  intro x hx
  have hlt : riemannianEDistOf (I := I) (g t) O x <
      ENNReal.ofReal ((1 / 2 : ℝ) * R) := by
    apply hx.trans_lt
    exact (ENNReal.ofReal_le_ofReal (le_max_left r 0)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right r 0)).2 hrR)
  have hdist := riemannianEDistOf_le_of_metric_lower_on_ball
    (I := I) (M := M) (g t₀) (g t) O x hc
    (fun y hy v => (ht y hy v).1) hlt
  have hreal : (riemannianEDistOf (I := I) (g t) O x).toReal < (1 / 2 : ℝ) * R :=
    ENNReal.toReal_lt_of_lt_ofReal hlt
  apply hdist.trans
  apply ENNReal.ofReal_le_ofReal
  exact ((div_lt_iff₀ hc).2 (by simpa only [mul_comm] using hreal)).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_eventually_riemannianEDistOf_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hcomplete : RiemannianMetricComplete (I := I) (g t₀))
    (O : M) (r : ℝ) :
    ∃ L : Set M, IsCompact L ∧ ∀ᶠ t in nhdsWithin t₀ J,
      ∀ x : M, riemannianEDistOf (I := I) (g t) O x ≤ ENNReal.ofReal r → x ∈ L := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    refine ⟨{O}, isCompact_singleton, Filter.Eventually.of_forall ?_⟩
    intro t x hx
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨(g t).toRiemannianMetric⟩
    have hfin : Manifold.riemannianEDist I O x < ⊤ := hx.trans_lt ENNReal.ofReal_lt_top
    obtain ⟨γ, hγ0, hγ1, hγ, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfin zero_lt_one
    have hOx : O = x := by
      rw [← hγ0, ← hγ1]
      exact TotallyDisconnectedSpace.eq_of_continuous γ hγ.continuous 0 1
    exact hOx.symm
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact exists_compact_eventually_riemannianEDistOf_le_of_nonzero
      g hg ht₀ hcomplete O r


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_riemannianEDistOf_le_of_isCompact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J)
    (hcomplete : ∀ t ∈ K, RiemannianMetricComplete (I := I) (g t)) (O : M) (r : ℝ) :
    ∃ L : Set M, IsCompact L ∧ ∀ t ∈ K, ∀ x : M,
      riemannianEDistOf (I := I) (g t) O x ≤ ENNReal.ofReal r → x ∈ L := by
  apply hK.exists_compact_superset_of_eventually
    (fun t => {x : M | riemannianEDistOf (I := I) (g t) O x ≤ ENNReal.ofReal r})
  intro t ht
  obtain ⟨L, hL, hnear⟩ := exists_compact_eventually_riemannianEDistOf_le
    (I := I) (M := M) g hg (hKJ ht) (hcomplete t ht) O r
  exact ⟨L, hL, hnear.filter_mono (nhdsWithin_mono t hKJ)⟩


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lowerSemicontinuousWithinAt_riemannianEDistOf
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hcomplete : RiemannianMetricComplete (I := I) (g t₀)) (O x : M) :
    LowerSemicontinuousWithinAt (fun p : ℝ × M =>
      riemannianEDistOf (I := I) (g p.1) O p.2) (J ×ˢ univ) (t₀, x) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  have hgcont : Continuous (fun y => riemannianEDistOf (I := I) (g t₀) O y) := by
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨(g t₀).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨(g t₀).inner, (g t₀).contMDiff.continuous, by intro y v w; rfl⟩⟩
    have hc : Continuous (fun y : M => Manifold.riemannianEDist I O y) := by
      simpa only [Manifold.riemannianEDist_comm] using
        (Exponential.continuous_riemannianEDist_to (I := I) (M := M) O)
    exact hc
  intro a ha
  obtain ⟨r, hrnn, har, hrd⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
  obtain ⟨s, hsnn, hrs, hsd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hrd
  have hr : 0 < r := ENNReal.ofReal_pos.mp (bot_le.trans_lt har)
  have hrsreal : r < s := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrnn).mp hrs
  have hs : 0 < s := hr.trans hrsreal
  let c : ℝ := r / s
  have hc : 0 < c := div_pos hr hs
  have hc1 : c < 1 := (div_lt_one hs).2 hrsreal
  have hcSq : c ^ 2 < 1 := by nlinarith
  let R : ℝ := 2 * s
  have hcR : c * R = 2 * r := by dsimp [c, R]; field_simp
  have hrR : r < c * R := by rw [hcR]; linarith
  obtain ⟨K, hK, hnearK⟩ := exists_compact_eventually_riemannianEDistOf_le
    (I := I) (M := M) g hg ht₀ hcomplete O R
  have hcover := hnearK.self_of_nhdsWithin ht₀
  have hcomp := eventually_metric_comparison_on_compact
    (I := I) (M := M) g hg ht₀ hK hcSq (show (1 : ℝ) < 2 by norm_num)
  have hfst : Tendsto (fun p : ℝ × M => p.1) (nhdsWithin (t₀, x) (J ×ˢ univ))
      (nhdsWithin t₀ J) :=
    continuousAt_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hp => hp.1)
  have hnear : ∀ᶠ p : ℝ × M in nhdsWithin (t₀, x) (J ×ˢ univ),
      ENNReal.ofReal s < riemannianEDistOf (I := I) (g t₀) O p.2 :=
    ((hgcont.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds hsd)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hfst hcomp, hnear] with p hp hps
  apply har.trans_le
  by_contra hn
  have hdr : riemannianEDistOf (I := I) (g p.1) O p.2 < ENNReal.ofReal r :=
    lt_of_not_ge hn
  have hdR := hdr.trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrnn).2 hrR)
  have hdist := riemannianEDistOf_le_of_metric_lower_on_ball
    (I := I) (M := M) (g t₀) (g p.1) O p.2 hc
    (fun y hy v => (hp y (hcover y hy) v).1) hdR
  have hdrreal : (riemannianEDistOf (I := I) (g p.1) O p.2).toReal < r :=
    ENNReal.toReal_lt_of_lt_ofReal hdr
  have hrsdiv : r / c = s := by dsimp [c]; field_simp
  have hddiv : (riemannianEDistOf (I := I) (g p.1) O p.2).toReal / c ≤ s := by
    rw [← hrsdiv]
    exact (div_le_div_of_nonneg_right hdrreal.le hc.le)
  have hle := hdist.trans (ENNReal.ofReal_le_ofReal hddiv)
  exact (not_lt_of_ge hle) hps


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousAt_riemannianEDistOf
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t₀ : ℝ} (ht₀ : J ∈ nhds t₀)
    (hcomplete : RiemannianMetricComplete (I := I) (g t₀)) (O x : M) :
    ContinuousAt (fun p : ℝ × M => riemannianEDistOf (I := I) (g p.1) O p.2) (t₀, x) := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.2
  constructor
  · have hlower := lowerSemicontinuousWithinAt_riemannianEDistOf
      (I := I) (M := M) g hg (mem_of_mem_nhds ht₀) hcomplete O x
    have hJn : J ×ˢ (univ : Set M) ∈ nhds (t₀, x) := prod_mem_nhds ht₀ univ_mem
    simpa only [lowerSemicontinuousWithinAt_iff, lowerSemicontinuousAt_iff,
      (nhdsWithin_eq_nhds.mpr hJn)] using hlower
  · by_cases hfin : riemannianEDistOf (I := I) (g t₀) O x = ⊤
    · intro b hb
      simp only [hfin, not_top_lt] at hb
    obtain ⟨F, hF, hFeq, hupper⟩ := exists_riemannianEDistOf_upper_support_continuousAt
      (I := I) (M := M) g hg ht₀ hcomplete O x hfin
    have hEF : ContinuousAt (fun p => ENNReal.ofReal (F p)) (t₀, x) :=
      ENNReal.continuous_ofReal.continuousAt.comp hF
    have hEFeq : ENNReal.ofReal (F (t₀, x)) = riemannianEDistOf (I := I) (g t₀) O x := by
      rw [hFeq, ENNReal.ofReal_toReal hfin]
    intro b hb
    have hnear : ∀ᶠ p in nhds (t₀, x), ENNReal.ofReal (F p) < b :=
      hEF.eventually (Iio_mem_nhds (by
        change ENNReal.ofReal (F (t₀, x)) < b
        rwa [hEFeq]))
    filter_upwards [hupper, hnear] with p hp hpF
    exact hp.trans_lt hpF


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem continuousOn_riemannianEDistOf_icc
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Icc a b)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (hcomplete : ∀ t ∈ Icc a b, RiemannianMetricComplete (I := I) (g t)) (O : M) :
    ContinuousOn (fun p : ℝ × M => riemannianEDistOf (I := I) (g p.1) O p.2)
      (Icc a b ×ˢ univ) := by
  by_cases hab : a ≤ b
  · let φ : ℝ → ℝ := fun t => (Set.projIcc a b hab t : ℝ)
    have hφ : Continuous φ := continuous_subtype_val.comp continuous_projIcc
    have hφmem : ∀ t : ℝ, φ t ∈ Icc a b := fun t => (Set.projIcc a b hab t).property
    have hφeq : ∀ t ∈ Icc a b, φ t = t := by
      intro t ht
      simp only [φ, Set.projIcc_of_mem hab ht]
    have hgφ : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 univ
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (g (φ t)) x) :=
      tensor0SFamilyContinuousOnSet.comp_time hg hφ (fun t _ => hφmem t)
    have hext : Continuous (fun p : ℝ × M => riemannianEDistOf (I := I) (g (φ p.1)) O p.2) := by
      rw [continuous_iff_continuousAt]
      intro p
      exact continuousAt_riemannianEDistOf (I := I) (M := M) (fun t => g (φ t)) hgφ
        univ_mem (hcomplete (φ p.1) (hφmem p.1)) O p.2
    apply hext.continuousOn.congr
    intro p hp
    dsimp only
    rw [hφeq p.1 hp.1]
  · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab), empty_prod]
    exact continuousOn_empty _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousOn_riemannianEDistOf
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (hcomplete : ∀ t ∈ J, RiemannianMetricComplete (I := I) (g t)) (O : M) :
    ContinuousOn (fun p : ℝ × M => riemannianEDistOf (I := I) (g p.1) O p.2)
      (J ×ˢ univ) := by
  intro p hp
  obtain ⟨a, b, hpa, _, habJ, hnear⟩ := hJ.exists_Icc_subset_mem_nhdsWithin hp.1 hp.1
  have hc := continuousOn_riemannianEDistOf_icc (I := I) (M := M) g
    (hg.mono habJ) (fun t ht => hcomplete t (habJ ht)) O p ⟨hpa, mem_univ _⟩
  apply hc.mono_of_mem_nhdsWithin
  have hfst : Tendsto (fun q : ℝ × M => q.1) (nhdsWithin p (J ×ˢ univ))
      (nhdsWithin p.1 J) :=
    continuousAt_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hq => hq.1)
  filter_upwards [hfst hnear] with q hq
  exact ⟨hq, mem_univ _⟩

end DifferentialGeometry.Geometry.Riemannian
