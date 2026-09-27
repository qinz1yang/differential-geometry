import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Metric

private theorem first_exit_open
    {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) {gamma : ℝ → X} (hgamma : Continuous gamma)
    (hstart : gamma 0 ∈ U) (hend : gamma 1 ∉ U) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      (∀ s ∈ Ico (0 : ℝ) t, gamma s ∈ U) ∧ gamma t ∉ U := by
  let J := Icc (0 : ℝ) 1
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let gammaJ : J → X := fun t ↦ gamma t
  let A : Set J := gammaJ ⁻¹' Uᶜ
  have hgammaJ : Continuous gammaJ :=
    hgamma.comp continuous_subtype_val
  have hA : IsClosed A := hU.isClosed_compl.preimage hgammaJ
  have hAne : A.Nonempty := by
    refine ⟨⟨1, zero_le_one, le_rfl⟩, ?_⟩
    exact hend
  obtain ⟨t, htA, htmin⟩ :=
    hA.isCompact.exists_isMinOn hAne continuous_subtype_val.continuousOn
  have htNot : gamma (t : ℝ) ∉ U := htA
  have htne : (t : ℝ) ≠ 0 := by
    intro ht
    apply htNot
    simpa only [ht] using hstart
  have htpos : (0 : ℝ) < t :=
    lt_of_le_of_ne t.property.1 (Ne.symm htne)
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, htNot⟩
  intro s hs
  by_contra hsNot
  let sJ : J := ⟨s, hs.1, hs.2.le.trans t.property.2⟩
  have hsA : sJ ∈ A := hsNot
  exact (not_le_of_gt hs.2) (htmin hsA)

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def metricPathLength
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo a b, ENNReal.ofReal (Real.sqrt
    (g.inner (gamma s)
      (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s 1)
      (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s 1)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metricPathLength_eq_pathELength
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (a b : ℝ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    metricPathLength g gamma a b = pathELength I gamma a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  unfold metricPathLength
  apply lintegral_congr
  intro s
  exact (tensor0SBundle_enorm_eq_riemannianBundle_enorm
    g (gamma s) (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s 1)).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_metricPathLength_lt
    (g : SmoothRiemannianMetric I M) (x y : M) (R : ℝ≥0∞)
    (hxy : riemannianEDistOf g x y < R) :
    ∃ gamma : ℝ → M, gamma 0 = x ∧ gamma 1 = y ∧
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
      metricPathLength g gamma 0 1 < R := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I x y < R at hxy
  obtain ⟨gamma, h0, h1, hgamma, hlen, _hflat0, _hflat1⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt
      hxy (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
  refine ⟨gamma, h0, h1, hgamma, ?_⟩
  rwa [metricPathLength_eq_pathELength]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_le_metricPathLength
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma)
    {a b : ℝ} (hab : a ≤ b) :
    riemannianEDistOf g (gamma a) (gamma b) ≤
      metricPathLength g gamma a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [metricPathLength_eq_pathELength]
  exact riemannianEDist_le_pathELength hgamma.contMDiffOn rfl rfl hab

private theorem metricPathLength_le_of_quad
    (g h : SmoothRiemannianMetric I M) {Q : ℝ} (hQ : 0 < Q)
    (gamma : ℝ → M) (a b : ℝ)
    (hquad : ∀ s ∈ Ioo a b, ∀ v : TangentSpace I (gamma s),
      g.inner (gamma s) v v ≤ Q * h.inner (gamma s) v v) :
    metricPathLength g gamma a b ≤
      ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma a b := by
  unfold metricPathLength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro s hs
  have hroot := Real.sqrt_le_sqrt
    (hquad s hs (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s 1))
  rw [Real.sqrt_mul hQ.le] at hroot
  simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] using
    ENNReal.ofReal_le_ofReal hroot

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem continuous_edistOf [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun q : M ↦ riemannianEDistOf g p q) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  change Continuous (fun q : M ↦ edist p q)
  exact continuous_const.edist continuous_id

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_ball_subset_of_local_quad [RegularSpace M]
    (g h : SmoothRiemannianMetric I M) (p y : M)
    {r Q : ℝ} (hr : 0 < r) (hQ : 0 < Q)
    (hy : riemannianEDistOf g p y < ENNReal.ofReal (r / 2))
    (hlocal : ∀ q : M,
      riemannianEDistOf g p q < ENNReal.ofReal r →
        ∀ v : TangentSpace I q, g.inner q v v ≤ Q * h.inner q v v) :
    {z : M | riemannianEDistOf h y z <
        ENNReal.ofReal (r / (2 * Real.sqrt Q))} ⊆
      {z : M | riemannianEDistOf g p z < ENNReal.ofReal r} := by
  intro z hz
  obtain ⟨gamma, hgamma0, hgamma1, hgamma, hlen⟩ :=
    exists_metricPathLength_lt h y z
      (ENNReal.ofReal (r / (2 * Real.sqrt Q))) hz
  let U : Set M := {q : M | riemannianEDistOf g p q < ENNReal.ofReal r}
  have hU : IsOpen U := isOpen_lt (continuous_edistOf g p) continuous_const
  have hstart : gamma 0 ∈ U := by
    change riemannianEDistOf g p (gamma 0) < ENNReal.ofReal r
    rw [hgamma0]
    exact hy.trans ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (half_lt_self hr))
  by_contra hzNot
  have hend : gamma 1 ∉ U := by
    simpa only [hgamma1] using hzNot
  obtain ⟨t, ht, hstay, hexit⟩ :=
    first_exit_open hU hgamma.continuous hstart hend
  have hprefix : riemannianEDistOf g y (gamma t) ≤
      metricPathLength g gamma 0 t := by
    simpa only [hgamma0] using
      edistOf_le_metricPathLength g gamma hgamma ht.1.le
  have hcompare : metricPathLength g gamma 0 t ≤
      ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma 0 t :=
    metricPathLength_le_of_quad g h hQ gamma 0 t
      (fun s hs ↦ hlocal (gamma s) (hstay s ⟨hs.1.le, hs.2⟩))
  have hmono : metricPathLength h gamma 0 t ≤ metricPathLength h gamma 0 1 := by
    unfold metricPathLength
    exact lintegral_mono_set (Ioo_subset_Ioo le_rfl ht.2)
  have hdistance : riemannianEDistOf g y (gamma t) ≤
      ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma 0 1 :=
    hprefix.trans (hcompare.trans (mul_le_mul le_rfl hmono (by positivity) (by positivity)))
  have hQsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hscaled : ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma 0 1 <
      ENNReal.ofReal (r / 2) := by
    calc
      ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma 0 1 <
          ENNReal.ofReal (Real.sqrt Q) *
            ENNReal.ofReal (r / (2 * Real.sqrt Q)) :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hQsqrt).ne'
          ENNReal.ofReal_ne_top hlen
      _ = ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
        congr 1
        field_simp [hQsqrt.ne']
  have htriangle : riemannianEDistOf g p (gamma t) ≤
      riemannianEDistOf g p y + riemannianEDistOf g y (gamma t) := by
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact riemannianEDist_triangle
  apply hexit
  change riemannianEDistOf g p (gamma t) < ENNReal.ofReal r
  calc
    riemannianEDistOf g p (gamma t) ≤
        riemannianEDistOf g p y + riemannianEDistOf g y (gamma t) := htriangle
    _ ≤ riemannianEDistOf g p y +
        ENNReal.ofReal (Real.sqrt Q) * metricPathLength h gamma 0 1 :=
      add_le_add le_rfl hdistance
    _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
      ENNReal.add_lt_add hy hscaled
    _ = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le]
      congr 1
      ring

end DifferentialGeometry.Geometry.Metric

end
