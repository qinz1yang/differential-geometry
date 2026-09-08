import DifferentialGeometry.Geometry.Comparison.Variation.ArcLengthContinuity
import DifferentialGeometry.Geometry.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Exponential.DiagInvFixed

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
  let B := stdBranch (I := I) (g t) hEnorm x
  let w : M → TangentSpace I x := fun y =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (B.fixedPD.symm y)
  have hwx : w x = 0 := by simp only [w, B.fixedPD_symm_center, map_zero]
  have hw : ContinuousAt w x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.continuous.continuousAt.comp
      (B.fixedPD.symm.contMDiffOn_toFun.continuousOn.continuousAt
        (B.fixedPD.open_target.mem_nhds B.fixedPD_center_mem))
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
  · have hnear : ∀ᶠ p : ℝ × M in nhds (t, x), p.2 ∈ B.fixedPD.target :=
      continuousAt_snd.preimage_mem_nhds (B.fixedPD.open_target.mem_nhds B.fixedPD_center_mem)
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
      exact B.fixedPD.right_inv hp
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

end DifferentialGeometry.Geometry.Riemannian
