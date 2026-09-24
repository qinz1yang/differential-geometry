import DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.InverseFunction

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S] [IsManifold J ∞ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

theorem isLocalDiffeomorphAt_of_eqOn_halfClosedInterval
    {r w : ℝ} (hr : 0 < r) (hrw : r < w)
    (c : S × Ico (0 : ℝ) w → M) (Φ : S × ℝ → M)
    {U : Set (S × ℝ)} (hU : IsOpen U) (hzero : ∀ s, (s, (0 : ℝ)) ∈ U)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ Φ U)
    (heq : ∀ (s : S) (t : ℝ) (ht : t ∈ Icc 0 r),
      Φ (s, t) = c (s, ⟨t, ht.1, ht.2.trans_lt hrw⟩))
    (hc : letI := halfClosedIntervalChartedSpace (hr.trans hrw)
      ∀ s, Function.Bijective (mfderiv (J.prod (𝓡∂ 1)) I c
        (s, ⟨0, le_rfl, hr.trans hrw⟩))) :
    ∀ s, IsLocalDiffeomorphAt (J.prod 𝓘(ℝ)) I ∞ Φ (s, 0) := by
  let := halfClosedIntervalChartedSpace (hr.trans hrw)
  let e : S × Ico (0 : ℝ) w → S × ℝ := Prod.map id Subtype.val
  have hs : Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) ∞
      (Subtype.val : Ico (0 : ℝ) w → ℝ) :=
    isSmoothEmbedding_halfClosedInterval_inclusion (hr.trans hrw)
  have he : ContMDiff (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ)) ∞ e :=
    contMDiff_id.prodMap hs.contMDiff
  intro s
  let x : S × Ico (0 : ℝ) w := (s, ⟨0, le_rfl, hr.trans hrw⟩)
  have hBe : Function.Bijective (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ)) e x) := by
    have hBs : Function.Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ)
        (Subtype.val : Ico (0 : ℝ) w → ℝ) x.2) :=
      bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ) Subtype.val x.2
        (hs.isImmersion.isImmersionAt x.2) (by simp)
    rw [mfderiv_prodMap mdifferentiableAt_id (hs.contMDiff.mdifferentiable (by simp) _),
      mfderiv_id]
    exact Function.bijective_id.prodMap hBs
  have hnear : Φ ∘ e =ᶠ[𝓝 x] c := by
    have hstrip : {q : S × Ico (0 : ℝ) w | q.2.val < r} ∈ 𝓝 x :=
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const).mem_nhds hr
    filter_upwards [hstrip] with q hq
    exact heq q.1 q.2.val ⟨q.2.property.1, hq.le⟩
  have hΦx : MDifferentiableAt (J.prod 𝓘(ℝ)) I Φ (e x) :=
    (hΦ.contMDiffAt (hU.mem_nhds (hzero s))).mdifferentiableAt (by simp)
  have hD := hnear.mfderiv_eq (I := J.prod (𝓡∂ 1)) (I' := I)
  rw [mfderiv_comp x hΦx (he.mdifferentiable (by simp) x)] at hD
  have hBcomp : Function.Bijective
      ((mfderiv (J.prod 𝓘(ℝ)) I Φ (e x)) ∘
        (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ)) e x)) := by
    change Function.Bijective ((mfderiv (J.prod 𝓘(ℝ)) I Φ (e x)).comp
      (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ)) e x))
    rw [hD]
    exact hc s
  have hB : Function.Bijective (mfderiv (J.prod 𝓘(ℝ)) I Φ (s, 0)) :=
    (Function.Bijective.of_comp_iff _ hBe).mp hBcomp
  let L : (F × ℝ) →L[ℝ] E := mfderiv (J.prod 𝓘(ℝ)) I Φ (s, 0)
  let A : (F × ℝ) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective L.toLinearMap hB).toContinuousLinearEquiv
  exact DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hU (hzero s) hΦ ⟨A, rfl⟩

end DifferentialGeometry.Topology.Manifold
