import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH


section Spatial

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance scalarScaleComparisonC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem mfderiv_real_comp {φ : ℝ → ℝ} {c : ℝ} {f : M → ℝ} {x : M}
    (hφ : HasDerivAt φ c (f x)) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (v : TangentSpace I x) :
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => φ (f y)) x v)
      = c * (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x v) := by
  have hmf : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y : M => φ (f y)) x
      (c • (mfderiv I 𝓘(ℝ, ℝ) f x : TangentSpace I x →L[ℝ] ℝ)) := by
    refine ((hφ.hasFDerivAt.hasMFDerivAt).comp x hf.hasMFDerivAt).congr_mfderiv ?_
    ext w
    change (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x w) * c =
      c * (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x w)
    exact mul_comm _ _
  exact DFunLike.congr_fun hmf.mfderiv v

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem metricInner_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]; simp
  · exact (g.pos x v hv).le

variable (g : SmoothRiemannianMetric I M)


private def invRootScalar (η : ℝ) : M → ℝ :=
  fun y => 2 / η * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹

omit [SigmaCompactSpace M] in
private theorem contMDiff_invRootScalar {η : ℝ}
    (hpos : ∀ y : M, 0 < metricScalarAt (I := I) g y) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (invRootScalar (I := I) g η) := by
  intro z
  have hz : metricScalarAt (I := I) g z ≠ 0 := (hpos z).ne'
  have hsz : Real.sqrt (metricScalarAt (I := I) g z) ≠ 0 :=
    (Real.sqrt_pos.mpr (hpos z)).ne'
  have h1 : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun r : ℝ => 2 / η * (Real.sqrt r)⁻¹)
      (metricScalarAt (I := I) g z) :=
    contDiffAt_const.mul ((Real.contDiffAt_sqrt hz).inv hsz)
  exact h1.comp_contMDiffAt (x := z) ((metricScalar_smooth (I := I) g) z)

omit [SigmaCompactSpace M] in
private theorem mfderiv_invRootScalar_sq_le {η : ℝ} (hη : 0 < η)
    (hpos : ∀ y : M, 0 < metricScalarAt (I := I) g y)
    (hgrad : ∀ (y : M) (w : TangentSpace I y),
      |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun z : M => metricScalarAt (I := I) g z) y w)| ≤
        η * metricScalarAt (I := I) g y * Real.sqrt (metricScalarAt (I := I) g y) *
          Real.sqrt (g.inner y w w))
    (x : M) (v : TangentSpace I x) :
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (invRootScalar (I := I) g η) x v) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (invRootScalar (I := I) g η) x v) ≤
      g.inner x v v := by
  have hRx : 0 < metricScalarAt (I := I) g x := hpos x
  have hsx : 0 < Real.sqrt (metricScalarAt (I := I) g x) := Real.sqrt_pos.mpr hRx
  have hRne : metricScalarAt (I := I) g x ≠ 0 := hRx.ne'
  have hsne : Real.sqrt (metricScalarAt (I := I) g x) ≠ 0 := hsx.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hsq : Real.sqrt (metricScalarAt (I := I) g x) ^ 2 = metricScalarAt (I := I) g x :=
    Real.sq_sqrt hRx.le
  have hconst : 2 / η * (-(1 / (2 * Real.sqrt (metricScalarAt (I := I) g x))) /
      Real.sqrt (metricScalarAt (I := I) g x) ^ 2) =
      -(1 / (η * (metricScalarAt (I := I) g x *
        Real.sqrt (metricScalarAt (I := I) g x)))) := by
    rw [hsq]
    field_simp
  have hderiv : HasDerivAt (fun r : ℝ => 2 / η * (Real.sqrt r)⁻¹)
      (-(1 / (η * (metricScalarAt (I := I) g x *
        Real.sqrt (metricScalarAt (I := I) g x)))))
      (metricScalarAt (I := I) g x) :=
    (((Real.hasDerivAt_sqrt hRne).inv hsne).const_mul (2 / η)).congr_deriv hconst
  have hRdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : M => metricScalarAt (I := I) g z) x :=
    ((metricScalar_smooth (I := I) g) x).mdifferentiableAt (by decide)
  have hval : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (invRootScalar (I := I) g η) x v) =
      -(1 / (η * (metricScalarAt (I := I) g x *
          Real.sqrt (metricScalarAt (I := I) g x)))) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun z : M => metricScalarAt (I := I) g z) x v) :=
    mfderiv_real_comp (I := I) hderiv hRdiff v
  have hpositive : 0 < η * (metricScalarAt (I := I) g x *
      Real.sqrt (metricScalarAt (I := I) g x)) := by positivity
  have habs : |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (invRootScalar (I := I) g η) x v)| ≤
      Real.sqrt (g.inner x v v) := by
    rw [hval, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 /
      (η * (metricScalarAt (I := I) g x * Real.sqrt (metricScalarAt (I := I) g x)))),
      div_mul_eq_mul_div, one_mul, div_le_iff₀ hpositive]
    calc |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun z : M => metricScalarAt (I := I) g z) x v)|
        ≤ η * metricScalarAt (I := I) g x *
            Real.sqrt (metricScalarAt (I := I) g x) * Real.sqrt (g.inner x v v) :=
          hgrad x v
      _ = Real.sqrt (g.inner x v v) * (η * (metricScalarAt (I := I) g x *
            Real.sqrt (metricScalarAt (I := I) g x))) := by ring
  have hgnn : 0 ≤ g.inner x v v := metricInner_self_nonneg (I := I) g x v
  have hstep := mul_self_le_mul_self (abs_nonneg
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (invRootScalar (I := I) g η) x v)) habs
  rwa [abs_mul_abs_self, Real.mul_self_sqrt hgnn] at hstep

omit [SigmaCompactSpace M] in
theorem scalar_spatial_scale_comparison {η : ℝ} (hη : 0 < η)
    (hpos : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (hgrad : ∀ (x : M) (v : TangentSpace I x),
      |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => metricScalarAt (I := I) g y) x v)| ≤
        η * metricScalarAt (I := I) g x * Real.sqrt (metricScalarAt (I := I) g x) *
          Real.sqrt (g.inner x v v)) :
    ∀ x y : M, riemannianEDistOf (I := I) g x y ≤
        ENNReal.ofReal (η⁻¹ / Real.sqrt (metricScalarAt (I := I) g x)) →
      4 / 9 * metricScalarAt (I := I) g x ≤ metricScalarAt (I := I) g y ∧
        metricScalarAt (I := I) g y ≤ 4 * metricScalarAt (I := I) g x := by
  intro x y hxy
  have hax : 0 < Real.sqrt (metricScalarAt (I := I) g x) :=
    Real.sqrt_pos.mpr (hpos x)
  have hby : 0 < Real.sqrt (metricScalarAt (I := I) g y) :=
    Real.sqrt_pos.mpr (hpos y)
  have hηne : η ≠ 0 := hη.ne'
  have hane : Real.sqrt (metricScalarAt (I := I) g x) ≠ 0 := hax.ne'
  have hbne : Real.sqrt (metricScalarAt (I := I) g y) ≠ 0 := hby.ne'
  have hlip := DifferentialGeometry.ofReal_abs_sub_le_riemannianEDistOf (I := I) g
    (invRootScalar (I := I) g η) (contMDiff_invRootScalar (I := I) g hpos)
    (fun z w => mfderiv_invRootScalar_sq_le (I := I) g hη hpos hgrad z w) x y
  have hnn : 0 ≤ η⁻¹ / Real.sqrt (metricScalarAt (I := I) g x) :=
    div_nonneg (inv_nonneg.mpr hη.le) (Real.sqrt_nonneg _)
  have hbound : |invRootScalar (I := I) g η x - invRootScalar (I := I) g η y| ≤
      η⁻¹ / Real.sqrt (metricScalarAt (I := I) g x) :=
    (ENNReal.ofReal_le_ofReal_iff hnn).mp (hlip.trans hxy)
  have hlow := (abs_le.mp hbound).1
  have hhigh := (abs_le.mp hbound).2
  simp only [invRootScalar] at hlow hhigh
  have hcancel1 : η * (2 / η * (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ -
      2 / η * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹) =
      2 * (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ -
        2 * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹ := by
    field_simp
  have hcancel2 : η * (η⁻¹ / Real.sqrt (metricScalarAt (I := I) g x)) =
      (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ := by
    field_simp
  have h1 : (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ ≤
      2 * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hhigh hη.le
    rw [hcancel1, hcancel2] at hm
    linarith
  have h2 : 2 * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹ ≤
      3 * (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hlow hη.le
    rw [hcancel1, mul_neg, hcancel2] at hm
    linarith
  have hprod : 0 < Real.sqrt (metricScalarAt (I := I) g x) *
      Real.sqrt (metricScalarAt (I := I) g y) := mul_pos hax hby
  have hyle : Real.sqrt (metricScalarAt (I := I) g y) ≤
      2 * Real.sqrt (metricScalarAt (I := I) g x) := by
    have hm := mul_le_mul_of_nonneg_right h1 hprod.le
    calc Real.sqrt (metricScalarAt (I := I) g y)
        = (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ *
            (Real.sqrt (metricScalarAt (I := I) g x) *
              Real.sqrt (metricScalarAt (I := I) g y)) := by field_simp
      _ ≤ 2 * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹ *
            (Real.sqrt (metricScalarAt (I := I) g x) *
              Real.sqrt (metricScalarAt (I := I) g y)) := hm
      _ = 2 * Real.sqrt (metricScalarAt (I := I) g x) := by field_simp
  have hyge : 2 * Real.sqrt (metricScalarAt (I := I) g x) ≤
      3 * Real.sqrt (metricScalarAt (I := I) g y) := by
    have hm := mul_le_mul_of_nonneg_right h2 hprod.le
    calc 2 * Real.sqrt (metricScalarAt (I := I) g x)
        = 2 * (Real.sqrt (metricScalarAt (I := I) g y))⁻¹ *
            (Real.sqrt (metricScalarAt (I := I) g x) *
              Real.sqrt (metricScalarAt (I := I) g y)) := by field_simp
      _ ≤ 3 * (Real.sqrt (metricScalarAt (I := I) g x))⁻¹ *
            (Real.sqrt (metricScalarAt (I := I) g x) *
              Real.sqrt (metricScalarAt (I := I) g y)) := hm
      _ = 3 * Real.sqrt (metricScalarAt (I := I) g y) := by field_simp
  have hxsq : Real.sqrt (metricScalarAt (I := I) g x) *
      Real.sqrt (metricScalarAt (I := I) g x) = metricScalarAt (I := I) g x :=
    Real.mul_self_sqrt (hpos x).le
  have hysq : Real.sqrt (metricScalarAt (I := I) g y) *
      Real.sqrt (metricScalarAt (I := I) g y) = metricScalarAt (I := I) g y :=
    Real.mul_self_sqrt (hpos y).le
  constructor
  · nlinarith [hyge, hax, hby, hxsq, hysq]
  · nlinarith [hyle, hax, hby, hxsq, hysq]

omit [T2Space M] [SigmaCompactSpace M] in
theorem scalarDifferential_eq_mfderiv_metricScalarAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    (v : TangentSpace I x) :
    scalarDifferential (I := I) S t x v =
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => metricScalarAt (I := I) (S.base.metric t) y) x v) :=
  rfl

end Spatial


section Temporal


theorem scalar_temporal_scale_comparison_of_le {R R' : ℝ → ℝ} {η c t : ℝ}
    (hη : 0 < η) (hct : c ≤ t) (hRt : 0 < R t) (hlen : t - c ≤ (2 * η * R t)⁻¹)
    (hpos : ∀ s ∈ Icc c t, 0 < R s)
    (hderiv : ∀ s ∈ Icc c t, HasDerivWithinAt R (R' s) (Icc c t) s)
    (hmono : ∀ s ∈ Icc c t, 0 ≤ R' s)
    (hupper : ∀ s ∈ Icc c t, R' s ≤ η * R s ^ 2) :
    ∀ s ∈ Icc c t, 2 / 3 * R t ≤ R s ∧ R s ≤ R t := by
  have hηne : η ≠ 0 := hη.ne'
  have hRtne : R t ≠ 0 := hRt.ne'
  have hconv : Convex ℝ (Icc c t) := convex_Icc c t
  have htmem : t ∈ Icc c t := ⟨hct, le_rfl⟩
  have hcont : ContinuousOn R (Icc c t) := fun s hs => (hderiv s hs).continuousWithinAt
  have hmonoR : MonotoneOn R (Icc c t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg hconv hcont
      (fun s hs => (hderiv s (interior_subset hs)).mono interior_subset)
      (fun s hs => hmono s (interior_subset hs))
  have hwderiv : ∀ s ∈ Icc c t,
      HasDerivWithinAt (fun r : ℝ => (R r)⁻¹ + η * r)
        (-(R' s) / R s ^ 2 + η) (Icc c t) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun r : ℝ => (R r)⁻¹) (-(R' s) / R s ^ 2) (Icc c t) s :=
      (hderiv s hs).inv (hpos s hs).ne'
    have h2 : HasDerivWithinAt (fun r : ℝ => η * r) η (Icc c t) s := by
      simpa using (hasDerivWithinAt_id s (Icc c t)).const_mul η
    exact h1.add h2
  have hwmono : MonotoneOn (fun r : ℝ => (R r)⁻¹ + η * r) (Icc c t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg hconv
      (fun s hs => (hwderiv s hs).continuousWithinAt)
      (fun s hs => (hwderiv s (interior_subset hs)).mono interior_subset) ?_
    intro s hs
    have hs' : s ∈ Icc c t := interior_subset hs
    have hR2 : 0 < R s ^ 2 := pow_pos (hpos s hs') 2
    have hdiv : R' s / R s ^ 2 ≤ η := (div_le_iff₀ hR2).mpr (hupper s hs')
    rw [neg_div]
    linarith
  intro s hs
  have hRs : 0 < R s := hpos s hs
  have hRsne : R s ≠ 0 := hRs.ne'
  refine ⟨?_, hmonoR hs htmem hs.2⟩
  have hwle := hwmono hs htmem hs.2
  have hts : t - s ≤ (2 * η * R t)⁻¹ := le_trans (by linarith [hs.1]) hlen
  have hcalc : η * (2 * η * R t)⁻¹ = 1 / 2 * (R t)⁻¹ := by field_simp
  have hshort : η * (t - s) ≤ 1 / 2 * (R t)⁻¹ := by
    rw [← hcalc]
    exact mul_le_mul_of_nonneg_left hts hη.le
  have hexpand : η * (t - s) = η * t - η * s := by ring
  have hBA : (R s)⁻¹ ≤ 3 / 2 * (R t)⁻¹ := by
    simp only at hwle
    linarith
  have hsi : (R s)⁻¹ * R s = 1 := inv_mul_cancel₀ hRsne
  have hti : (R t)⁻¹ * R t = 1 := inv_mul_cancel₀ hRtne
  have hstep : (1 : ℝ) ≤ 3 / 2 * (R t)⁻¹ * R s := by
    have h := mul_le_mul_of_nonneg_right hBA hRs.le
    rwa [hsi] at h
  have hstep2 : R t ≤ 3 / 2 * R s := by
    have h := mul_le_mul_of_nonneg_right hstep hRt.le
    rw [one_mul] at h
    calc R t ≤ 3 / 2 * (R t)⁻¹ * R s * R t := h
      _ = 3 / 2 * ((R t)⁻¹ * R t) * R s := by ring
      _ = 3 / 2 * R s := by rw [hti]; ring
  linarith


theorem scalar_temporal_scale_comparison {R R' : ℝ → ℝ} {η t : ℝ}
    (hη : 0 < η) (hRt : 0 < R t)
    (hpos : ∀ s ∈ Icc (t - (2 * η * R t)⁻¹) t, 0 < R s)
    (hderiv : ∀ s ∈ Icc (t - (2 * η * R t)⁻¹) t,
      HasDerivWithinAt R (R' s) (Icc (t - (2 * η * R t)⁻¹) t) s)
    (hmono : ∀ s ∈ Icc (t - (2 * η * R t)⁻¹) t, 0 ≤ R' s)
    (hupper : ∀ s ∈ Icc (t - (2 * η * R t)⁻¹) t, R' s ≤ η * R s ^ 2) :
    ∀ s ∈ Icc (t - (2 * η * R t)⁻¹) t, 2 / 3 * R t ≤ R s ∧ R s ≤ R t :=
  scalar_temporal_scale_comparison_of_le hη
    (sub_le_self t (by positivity)) hRt (le_of_eq (sub_sub_cancel t _))
    hpos hderiv hmono hupper

end Temporal


section Flow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance scaleComparisonTopology : TopologicalSpace F.M := F.topology
local instance scaleComparisonCharted : ChartedSpace H F.M := F.charted
local instance scaleComparisonSmooth : IsManifold I ∞ F.M := F.smooth
local instance scaleComparisonC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
local instance scaleComparisonSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance scaleComparisonT2 : T2Space F.M := F.t2
local instance scaleComparisonTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

omit [I.Boundaryless] in
def ScalarDifferentialBounds (η : ℝ) : Prop :=
  ∀ t ∈ D.carrier, ∀ x : F.M,
    (∀ v : TangentSpace I x,
      |scalarDifferential (I := I) F.S t x v| ≤
        η * F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
          Real.sqrt ((F.S.base.metric t).inner x v v)) ∧
    0 ≤ derivWithin (fun s : ℝ => F.S.scalar s x) D.carrier t ∧
    derivWithin (fun s : ℝ => F.S.scalar s x) D.carrier t ≤ η * F.S.scalar t x ^ 2

omit [I.Boundaryless] in
theorem ancientKappa_spatial_scale_comparison
    (hF : IsAncientKappaSolution kappa F) {η : ℝ} (hη : 0 < η)
    (hpos : ∀ t ≤ (0 : ℝ), ∀ x : F.M, 0 < F.S.scalar t x)
    (hb : ScalarDifferentialBounds F η) {t : ℝ} (ht : t ≤ 0) (x y : F.M)
    (hxy : riemannianEDistOf (I := I) (F.S.base.metric t) x y ≤
      ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x))) :
    4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
      F.S.scalar t y ≤ 4 * F.S.scalar t x := by
  have htc : t ∈ D.carrier := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using ht
  exact scalar_spatial_scale_comparison (I := I) (F.S.base.metric t) hη
    (fun z => hpos t ht z) (fun z w => (hb t htc z).1 w) x y hxy

omit [I.Boundaryless] in
theorem ancientKappa_temporal_scale_comparison
    (hF : IsAncientKappaSolution kappa F) {η : ℝ} (hη : 0 < η)
    (hpos : ∀ t ≤ (0 : ℝ), ∀ x : F.M, 0 < F.S.scalar t x)
    (hb : ScalarDifferentialBounds F η) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∀ s ∈ Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
      2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧ F.S.scalar s x ≤ F.S.scalar t x := by
  have hsub : Icc (t - (2 * η * F.S.scalar t x)⁻¹) t ⊆ D.carrier := by
    rw [hF.carrier_eq]
    exact fun s hs => le_trans hs.2 ht
  refine scalar_temporal_scale_comparison (R := fun s : ℝ => F.S.scalar s x)
    (R' := fun s : ℝ => derivWithin (fun r : ℝ => F.S.scalar r x) D.carrier s)
    hη (hpos t ht x) (fun s hs => hpos s (le_trans hs.2 ht) x) (fun s hs => ?_)
    (fun s hs => (hb s (hsub hs) x).2.1) (fun s hs => (hb s (hsub hs) x).2.2)
  exact ((F.isSolution.scalarTime (hsub hs) (subset_refl D.carrier) x).hasDerivWithinAt).mono
    hsub

omit [I.Boundaryless] in
theorem ancientKappa_scalar_scale_comparison
    (hF : IsAncientKappaSolution kappa F) {η : ℝ} (hη : 1 ≤ η)
    (hpos : ∀ t ≤ (0 : ℝ), ∀ x : F.M, 0 < F.S.scalar t x)
    (hb : ScalarDifferentialBounds F η) :
    ∀ t ≤ (0 : ℝ),
      (∀ x y : F.M, riemannianEDistOf (I := I) (F.S.base.metric t) x y ≤
          ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x)) →
        4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
          F.S.scalar t y ≤ 4 * F.S.scalar t x) ∧
      (∀ x : F.M, ∀ s ∈ Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
        2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧
          F.S.scalar s x ≤ F.S.scalar t x) := by
  have hη0 : 0 < η := lt_of_lt_of_le zero_lt_one hη
  exact fun t ht =>
    ⟨fun x y hxy =>
        ancientKappa_spatial_scale_comparison F hF hη0 hpos hb ht x y hxy,
      fun x => ancientKappa_temporal_scale_comparison F hF hη0 hpos hb ht x⟩

end Flow

section AncientThree

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance scaleComparisonThreeTopology : TopologicalSpace F.M := F.topology
local instance scaleComparisonThreeCharted : ChartedSpace H F.M := F.charted
local instance scaleComparisonThreeSmooth : IsManifold I ∞ F.M := F.smooth
local instance scaleComparisonThreeC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
local instance scaleComparisonThreeSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance scaleComparisonThreeT2 : T2Space F.M := F.t2
local instance scaleComparisonThreeTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

variable {kappa : ℝ}


theorem ancientKappa_scalar_scale_comparison_three
    (hdim : Module.finrank ℝ E = 3) (hF : IsAncientKappaSolution kappa F)
    {η : ℝ} (hη : 1 ≤ η) (hb : ScalarDifferentialBounds F η) :
    ∀ t ≤ (0 : ℝ),
      (∀ x y : F.M, riemannianEDistOf (I := I) (F.S.base.metric t) x y ≤
          ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x)) →
        4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
          F.S.scalar t y ≤ 4 * F.S.scalar t x) ∧
      (∀ x : F.M, ∀ s ∈ Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
        2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧
          F.S.scalar s x ≤ F.S.scalar t x) := by
  refine ancientKappa_scalar_scale_comparison F hF hη ?_ hb
  intro t ht x
  exact ancientKappa_scalar_pos F hdim hF ht x

end AncientThree

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
