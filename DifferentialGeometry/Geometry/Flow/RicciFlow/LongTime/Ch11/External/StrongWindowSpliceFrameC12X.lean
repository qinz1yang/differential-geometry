import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceShiftC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingNeckBandCylNK
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.LocalDiffeomorphPortHGI

/-!
# Splice frame tools (C12X, S16 `hwin` far branch; O-C12X-S16H G4e1)

* `IncomingBackwardNeckDeep_C12X.derivNorm_le_C12X`: the deep backward neck metric is `η`-close
  (`η < δ`) in `C^m`, `m ≤ k`, to the shrinking cylinder `cylFam v` (its own reference) on the
  closed test region, for every `v ∈ [-θ, 0]` (the `b = 0` part of `deep_closeness`).
* `ricciSharp_cylFam_norm_le_C12X`: on any open piece of the cylinder, the Ricci endomorphism of
  `cylFam v` (`v < 1`) has norm `≤ (2 (1 - v))⁻¹`.
* `abs_scalar_sub_le_of_cylFam_close_C12X`: `C²`-closeness to `cylFam v` (own reference) controls
  `|R - (1 - v)⁻¹|` (`abs_scalar_curvature_sub_le_of_small_metric_derivatives`).
* `metricDerivNorm_frame_C12X`: frame change — pulling back by a local diffeomorphism after a
  constant rescaling multiplies the self-referenced `C^q` distance by `√(κ⁻¹ ^ q)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

private local instance s16h_sphereDim4 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

universe u

section Deep

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r θ : ℝ}

/-- The deep backward neck metric is `η`-close (`η < δ`) in `C^m` (`m ≤ k`) to the shrinking
cylinder on the closed test region, for every `v ∈ [-θ, 0]`. -/
theorem IncomingBackwardNeckDeep_C12X.derivNorm_le_C12X
    (D : IncomingBackwardNeckDeep_C12X H i neck r θ) :
    ∃ η : ℝ, η < δ ∧ ∀ v : ℝ, v ∈ Icc (-θ) 0 → ∀ x ∈ neckClosedTest δ, ∀ m : ℕ, m ≤ k →
      metricDerivNorm m (D.metric v)
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
          (neckBuffer δ))
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
          (neckBuffer δ)) x ≤ η := by
  obtain ⟨η, hη, hbound⟩ := D.deep_closeness
  refine ⟨η, hη, fun v hv x hx m hm => ?_⟩
  have h := hbound m 0 (by omega) ⟨v, hv⟩ x hx
  have hv1 : v < 1 := hv.2.trans_lt zero_lt_one
  have hgc : shrinkingCylinderMetric ⟨v, hv1⟩ =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v :=
    shrinkingCylinderMetric_eq_flow ⟨v, hv1⟩
  have hJ : D.deepJet 0 ⟨v, hv⟩ = metricTensorField (D.metric v) -
      metricTensorField ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
        (neckBuffer δ)) := by
    ext y w
    rw [D.deepJet_eq]
    simp only [iteratedDerivWithin_zero, min_eq_left hv.2, hgc]
    rfl
  simp only at h
  rw [cylinderTensorCovDeriv_eq_tensor02CovDeriv, hJ] at h
  rw [hgc] at h
  have h2 := tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm (D.metric v)
    ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer δ))
    ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer δ))
    m x
  rw [← h2]
  exact h

end Deep

private theorem s16h_real_aux (a b W U p c : ℝ) (hc : 0 < c) (hb : 0 ≤ b) (hW : c * a ≤ W)
    (hU : c * b ≤ U) (hcs : p ^ 2 ≤ a * b) (hp : U = p) (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) :
    U ≤ W / c ^ 2 := by
  subst hp
  have h1 : (c * a) * (c * b) ≤ W * U := mul_le_mul hW hU (by positivity) hW0
  have h4 : c ^ 2 * U ^ 2 ≤ W * U := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  rcases hU0.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · nlinarith

/-- The Ricci endomorphism of the shrinking cylinder `cylFam v` (`v < 1`), restricted to any open
piece, has norm `≤ (2 (1 - v))⁻¹`. -/
theorem ricciSharp_cylFam_norm_le_C12X {v : ℝ} (hv : v < 1)
    (W : TopologicalSpace.Opens NeckCylinder) (x : W) (w : TangentSpace NeckCylinderModel x) :
    let gRef := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen W
    Real.sqrt (gRef.inner x (ricciSharp gRef x w) (ricciSharp gRef x w)) ≤
      (2 * (1 - v))⁻¹ * Real.sqrt (gRef.inner x w w) := by
  intro gRef
  have hc : 0 < 2 * (1 - v) := by linarith
  set u := ricciSharp gRef x w with hu
  have hUdef : gRef.inner x u u =
      (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 w.1 u.1 := by
    rw [hu, inner_ricciSharp]
    have h1 := Curvature.ricciTensor_restrictOpen
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) W x w (ricciSharp gRef x w)
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at h1
    exact h1.trans (PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric v x.1 w _)
  have hinner : ∀ y : TangentSpace NeckCylinderModel x, gRef.inner x y y =
      2 * (1 - v) * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 y.1 y.1 +
        y.2 * y.2 := fun y => PDE.RicciFlow.shrinkingCylinderMetric_inner hv x.1 y y
  have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq
    (Geometry.roundMetric (E := ThreeSpace) (n := 2)) x.1.1 w.1 u.1
  have ha := metric_inner_self_nonneg (Geometry.roundMetric (E := ThreeSpace) (n := 2))
    x.1.1 w.1
  have hb := metric_inner_self_nonneg (Geometry.roundMetric (E := ThreeSpace) (n := 2))
    x.1.1 u.1
  have hW0 : 0 ≤ gRef.inner x w w := metric_inner_self_nonneg gRef x w
  have hU0 : 0 ≤ gRef.inner x u u := metric_inner_self_nonneg gRef x u
  have hW : 2 * (1 - v) * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 w.1 w.1
      ≤ gRef.inner x w w := by
    rw [hinner]; nlinarith [mul_self_nonneg w.2]
  have hU : 2 * (1 - v) * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 u.1 u.1
      ≤ gRef.inner x u u := by
    rw [hinner]; nlinarith [mul_self_nonneg u.2]
  have hle := s16h_real_aux _ _ _ _ _ _ hc hb hW hU hcs hUdef hU0 hW0
  rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hW0, inv_pow]
  rw [div_eq_inv_mul] at hle
  exact hle

/-- `C²`-closeness to the shrinking cylinder `cylFam v` (own reference, `v < 1`) controls the
scalar curvature: `|R - (1 - v)⁻¹| ≤ 3 ((720 η + η (2(1-v))⁻¹) / (1 - η))`. -/
theorem abs_scalar_sub_le_of_cylFam_close_C12X {v : ℝ} (hv : v < 1)
    (W : TopologicalSpace.Opens NeckCylinder) (g : SmoothRiemannianMetric NeckCylinderModel W)
    (x : W) {η : ℝ} (hη : η ≤ 1 / 2)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen W)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen W) x ≤ η) :
    |metricScalarAt g x - (1 - v)⁻¹| ≤
      3 * ((240 * 3 * η + η * (2 * (1 - v))⁻¹) / (1 - η)) := by
  have h := abs_scalar_curvature_sub_le_of_small_metric_derivatives g
    ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen W) x η hη hsmall
    (2 * (1 - v))⁻¹ (fun w => ricciSharp_cylFam_norm_le_C12X hv W x w)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at h
  have hR : metricScalarAt ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
      W) x = (1 - v)⁻¹ := by
    rw [metricScalarAt_restrictOpen]
    exact PDE.RicciFlow.shrinkingCylinderMetric_scalar hv x.1
  rw [hR] at h
  push_cast at h
  exact h

/-- **Frame change.**  Pulling back by a local diffeomorphism after rescaling by `κ` multiplies the
self-referenced `C^q` distance by `√(κ⁻¹ ^ q)`. -/
theorem metricDerivNorm_frame_C12X {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Hm : Type*} [TopologicalSpace Hm] {I : ModelWithCorners ℝ E Hm}
    {Hn : Type*} [TopologicalSpace Hn] {J : ModelWithCorners ℝ F Hn}
    {M : Type*} [TopologicalSpace M] [ChartedSpace Hm M] [IsManifold I ∞ M] [T2Space M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace Hn N] [IsManifold J ∞ N] [T2Space N]
    (A : M → N) (hA : IsLocalDiffeomorph I J ∞ A) (G C : SmoothRiemannianMetric J N)
    {κ : ℝ} (hκ : 0 < κ) (q : ℕ) (x : M) :
    metricDerivNorm q (localPullMetric (scaleMetric κ hκ G) A hA)
        (localPullMetric (scaleMetric κ hκ C) A hA) (localPullMetric (scaleMetric κ hκ C) A hA) x =
      Real.sqrt (κ⁻¹ ^ q) * metricDerivNorm q G C C (A x) := by
  rw [metricDerivNorm_localPullMetric, metricDerivNorm_scale_all]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
