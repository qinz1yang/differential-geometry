import DifferentialGeometry.Geometry.Metric.Ray
import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Geodesic.EquationGerm
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold NNReal Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_unitSpeed_minimizing_riemannian_geodesic
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hpq : p ≠ q) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let : PseudoEMetricSpace M := (inferInstance : MetricSpace M).toPseudoMetricSpace.toPseudoEMetricSpace
    ∃ γ : ℝ → M, Isometry (fun t : Icc (0 : ℝ) (dist p q) ↦ γ t) ∧
      γ 0 = p ∧ γ (dist p q) = q ∧
      (∀ t, IsGeodesicAt (I := I) g γ t) ∧
      ∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1 := by
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hLpos : 0 < dist p q := dist_pos.mpr hpq
  obtain ⟨v, hv, hvnorm⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing
    (I := I) g hEnorm p q
  have hvnorm' : Real.sqrt (g.inner p v v) = dist p q := by
    rw [riemMetric_dist_eq (I := I)]
    exact hvnorm
  let L := dist p q
  let w : TangentSpace I p := L⁻¹ • v
  have hw : g.inner p w w = 1 := by
    have hvv : g.inner p v v = L ^ 2 := by
      rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hvnorm']
    dsimp only [w]
    rw [gInner_smul_self (I := I), hvv, ← mul_pow, inv_mul_cancel₀ hLpos.ne', one_pow]
  let γ := intrinsicGeodesic (I := I) g hEnorm p w
  have hzero : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p w
  have hend : γ L = q := by
    have hLw : L • w = v := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul]
    change intrinsicGeodesic (I := I) g hEnorm p w L = q
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p w L,
      ← expMapIntrinsic_def, hLw, hv]
  have hdist_le {s t : ℝ} (hst : s ≤ t) : dist (γ s) (γ t) ≤ t - s := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p w hst
    rw [hw, Real.sqrt_one, one_mul] at h
    rw [riemMetric_dist_eq (I := I)]
    exact (ENNReal.toReal_le_toReal (riemannianEDist_ne_top (I := I) _ _)
      ENNReal.ofReal_ne_top).mpr h |>.trans_eq (ENNReal.toReal_ofReal (sub_nonneg.mpr hst))
  have hgeogerms (t : ℝ) : IsGeodesicAt (I := I) g γ t :=
    isGeodesicAt_of_isGeodesicOn g (U := univ) (Filter.univ_mem)
      ((intrinsicGeodesic_isGeodesic g hEnorm p w).isGeodesicOn univ)
      (intrinsicGeodesic_contMDiff g hEnorm p w).continuous.continuousOn
  have hunit (t : ℝ) : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1 :=
    (intrinsicGeodesic_speedSq_eq g hEnorm p w t).trans hw
  let : PseudoEMetricSpace M := (inferInstance : MetricSpace M).toPseudoMetricSpace.toPseudoEMetricSpace
  have hlip : LipschitzWith 1 γ := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total s t with hst | hts
    · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      linarith [hdist_le hst]
    · rw [abs_of_nonneg (sub_nonneg.mpr hts), dist_comm]
      exact hdist_le hts
  have hisom := isometry_Icc_of_lipschitzOnWith_of_dist_eq (hlip.lipschitzOnWith (s := Icc 0 L))
    (show dist (γ 0) (γ L) = L - 0 by rw [hzero, hend, sub_zero])
  exact ⟨γ, hisom, hzero, hend, hgeogerms, hunit⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isometric_riemannian_segment
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let : PseudoEMetricSpace M := (inferInstance : MetricSpace M).toPseudoMetricSpace.toPseudoEMetricSpace
    ∃ δ : Icc (0 : ℝ≥0) (nndist p q) → M,
      Isometry δ ∧ δ ⟨0, by simp⟩ = p ∧ δ ⟨nndist p q, by simp⟩ = q := by
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  by_cases hpq : p = q
  · subst q
    let : PseudoEMetricSpace M := (inferInstance : MetricSpace M).toPseudoMetricSpace.toPseudoEMetricSpace
    refine ⟨fun _ ↦ p, Isometry.of_dist_eq fun s t ↦ ?_, rfl, rfl⟩
    have hs0 : s.1 = 0 := le_antisymm (by simpa using s.2.2) s.2.1
    have ht0 : t.1 = 0 := le_antisymm (by simpa using t.2.2) t.2.1
    have hs : s = t := Subtype.ext (hs0.trans ht0.symm)
    simp [hs]
  obtain ⟨γ, hisom, hzero, hend, _hgeo, _hunit⟩ :=
    exists_unitSpeed_minimizing_riemannian_geodesic g hEnorm p q hpq
  let L := dist p q
  let : PseudoEMetricSpace M := (inferInstance : MetricSpace M).toPseudoMetricSpace.toPseudoEMetricSpace
  let e : Icc (0 : ℝ≥0) (nndist p q) → Icc (0 : ℝ) L :=
    fun t ↦ ⟨(t.1 : ℝ), t.1.2, t.2.2⟩
  have he : Isometry e := Isometry.of_dist_eq fun _ _ ↦ rfl
  refine ⟨(fun t : Icc (0 : ℝ) L ↦ γ t) ∘ e, hisom.comp he, ?_, ?_⟩
  · exact hzero
  · exact hend

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_unitSpeed_minimizing_geodesic_of_complete
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : M) (hpq : p ≠ q) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ ((riemannianEDistOf g p q).toReal) = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      (∀ t, IsGeodesicAt (I := I) g γ t) ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      ∀ s ∈ Icc 0 ((riemannianEDistOf g p q).toReal),
        ∀ t ∈ Icc 0 ((riemannianEDistOf g p q).toReal),
          (riemannianEDistOf g (γ s) (γ t)).toReal = |s - t| := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : ℕ∞ω))
    (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hd (x y : M) : (riemannianEDistOf g x y).toReal = dist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm,
      riemMetric_dist_eq (I := I)]
  rw [hd]
  obtain ⟨γ, hisom, hzero, hend, hgeo, hunit⟩ :=
    exists_unitSpeed_minimizing_riemannian_geodesic g hEnorm p q hpq
  refine ⟨γ, hzero, hend, fun t => contMDiffAt_of_isGeodesicAt (hgeo t), hgeo, hunit, ?_⟩
  intro s hs t ht
  rw [hd]
  exact hisom.dist_eq ⟨s, hs⟩ ⟨t, ht⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_riemannian_ray [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) :
    ∃ γ : ℝ≥0 → M, γ 0 = p ∧
      ∀ s t, (riemannianEDistOf (I := I) g (γ s) (γ t)).toReal = dist s t := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : ℕ∞ω))
    (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let : ProperSpace M := properSpace_riemMetric_of_complete_metric (I := I) g hcomplete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨γ, hzero, hisom⟩ := exists_isometry_ray p (exists_isometric_riemannian_segment g hEnorm p)
  refine ⟨γ, hzero, fun s t ↦ ?_⟩
  rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm,
    ← riemMetric_dist_eq (I := I)]
  exact hisom.dist_eq s t


omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_distance_parametrized_minimizer_of_complete [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : M) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ ((riemannianEDistOf g p q).toReal) = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      ∀ s ∈ Icc 0 ((riemannianEDistOf g p q).toReal),
        ∀ t ∈ Icc 0 ((riemannianEDistOf g p q).toReal),
          riemannianEDistOf g (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  by_cases hpq : p = q
  · subst q
    refine ⟨fun _ => p, rfl, rfl, contMDiff_const, ?_⟩
    intro s hs t ht
    rw [riemannianEDistOf_self, ENNReal.toReal_zero] at hs ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [hs0, ht0, sub_self, abs_zero, ENNReal.ofReal_zero, riemannianEDistOf_self]
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    let _ : Subsingleton M :=
      DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero I hzero
    exact hpq (Subsingleton.elim p q)
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space (TangentBundle I M) := inferInstance
  obtain ⟨γ, hzero, hend, hsmooth, _, _, hdist⟩ :=
    exists_unitSpeed_minimizing_geodesic_of_complete g hcomplete p q hpq
  refine ⟨γ, hzero, hend, hsmooth, ?_⟩
  intro s hs t ht
  rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g (γ s) (γ t)), hdist s hs t ht]

end DifferentialGeometry.Geometry
