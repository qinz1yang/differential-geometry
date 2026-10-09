import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowFarRegionC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceFrameC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.GrowingInitialCylinderCharts
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.LocalDiffeomorphPortHGI
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.CylinderRotation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# Splice post part, geometric core (C12X, S16 `hwin` far branch; O-C12X-S16J G2)

Tools for the post-surgery comparison of the far-early branch of `hwin` (G4e-post):

* `isLocalDiffeomorph_codRestrict_C12X`: a local diffeomorphism with values in an open set is a
  local diffeomorphism into that open set.
* `cylIso_C12X e a σ`: the cylinder isometry `(ω, z) ↦ (e ω, a + σ z)` (`σ² = 1`), which preserves
  every slice of the shrinking cylinder (`localPullMetric_cylFam_cylIso_C12X`).
* `exists_far_window_cylinder_close_C12X`: on the band `S² × (-(L+1), L+1)`, the radial chart
  `(ω, z) ↦ (‖x‖ + z) • rot_x ω` into a standard cap window pulls back every window metric which is
  `C^p`-close to a standard solution at time `T ∈ [0, Θ]` (reference: the initial metric) to a
  metric close to the cylinder `cylFam T` with itself as reference; uniformly in the standard
  solution, `T`, and `‖x‖ ≥ D₁` (G4d + `exists_uniform_standard_metric_deriv_norm_reference_bound`
  + `metric_deriv_norm_reference_change_le` twice).
-/

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance s16j_sphereDimA :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance s16j_cylOpensSigma (V : Opens SpatialNeckCylinder) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel V.isOpen)

private local instance s16j_winSigma (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

section CodRestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A local diffeomorphism with values in an open set is a local diffeomorphism into it. -/
theorem isLocalDiffeomorph_codRestrict_C12X (O : Opens N) {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hO : ∀ x, f x ∈ O) :
    IsLocalDiffeomorph I J ∞ (fun x => (⟨f x, hO x⟩ : O)) := by
  intro x
  obtain ⟨Φ, hxΦ, hΦ⟩ := hf x
  obtain ⟨Θ, hΘx, hΘ⟩ := isLocalDiffeomorph_subtype_val (I := J) O ⟨f x, hO x⟩
  have htgt : ∀ y ∈ Φ.source, Φ y ∈ Θ.target → (Θ.symm (Φ y) : N) = f y := by
    intro y hy hyt
    have hs : Θ.symm (Φ y) ∈ Θ.source := Θ.toPartialEquiv.map_target hyt
    rw [hΘ hs]
    exact (Θ.toPartialEquiv.right_inv hyt).trans (hΦ hy).symm
  refine ⟨Φ.trans Θ.symm, ⟨hxΦ, ?_⟩, ?_⟩
  · change Φ x ∈ Θ.target
    rw [← hΦ hxΦ]
    have h := Θ.toPartialEquiv.map_source hΘx
    rwa [← hΘ hΘx] at h
  · rintro y ⟨hy, hyt⟩
    exact Subtype.ext (htgt y hy hyt).symm

end CodRestrict

section CylinderIsometry

/-- The cylinder isometry `(ω, z) ↦ (e ω, a + σ z)`, `σ² = 1`. -/
def cylIso_C12X (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (a σ : ℝ)
    (hσ : σ ^ 2 = 1) : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
      SpatialNeckCylinder :=
  (cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ).trans (roundCylinderDiffeomorph (n := 2) e 0)

theorem cylIso_apply_C12X (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (x : SpatialNeckCylinder) :
    cylIso_C12X e a σ hσ x = (sphereDiffeo (n := 2) e x.1, a + σ * x.2) := by
  change roundCylinderDiffeomorph (n := 2) e 0 (cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ x) = _
  rw [roundCylinderDiffeomorph_apply, cylinderAxialDiffeomorph_apply, zero_add]

theorem cylIso_mfderiv_C12X (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (x : SpatialNeckCylinder)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel (cylIso_C12X e a σ hσ) x v =
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x.1 v.1, σ * v.2) := by
  let A := cylinderAxialDiffeomorph (I := 𝓡 2) (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    a σ hσ
  let R := roundCylinderDiffeomorph (n := 2) e 0
  change mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel (R ∘ A) x v = _
  rw [mfderiv_comp_apply x (R.contMDiff.mdifferentiableAt (by decide))
    (A.contMDiff.mdifferentiableAt (by decide)), cylinderAxialDiffeomorph_mfderiv]
  exact roundCylinderDiffeomorph_mfderiv (n := 2) e 0 (A x) _

private theorem s16j_round_inv (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (a b : TangentSpace (𝓡 2) p) :
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (sphereDiffeo (n := 2) e p)
        (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) p a)
        (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) p b) =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p a b := by
  rw [roundMetric_inner, roundMetric_inner, mfderiv_incl_sphereDiffeo,
    mfderiv_incl_sphereDiffeo, e.inner_map_map]

/-- The cylinder isometries preserve every slice of the shrinking cylinder. -/
theorem localPullMetric_cylFam_cylIso_C12X {τ : ℝ} (hτ : τ < 1)
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (a σ : ℝ)
    (hσ : σ ^ 2 = 1) :
    localPullMetric (cylFam_C12X τ) (cylIso_C12X e a σ hσ)
      (cylIso_C12X e a σ hσ).isLocalDiffeomorph = cylFam_C12X τ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, cylFam_inner_C12X hτ, cylFam_inner_C12X hτ, cylIso_mfderiv_C12X,
    cylIso_mfderiv_C12X]
  have h1 : (cylIso_C12X e a σ hσ x).1 = sphereDiffeo (n := 2) e x.1 := by
    rw [cylIso_apply_C12X]
  rw [h1]
  erw [s16j_round_inv e x.1 v.1 w.1]
  linear_combination (v.2 * w.2) * hσ

end CylinderIsometry

section FarWindow

open DifferentialGeometry.PDE.RicciFlow.StandardCap in
/-- The band `S² × (-(L + 1), L + 1)` of the cylinder. -/
def cylBand_C12X (L : ℝ) : Opens SpatialNeckCylinder :=
  ⟨univ ×ˢ Ioo (-(L + 1)) (L + 1), isOpen_univ.prod isOpen_Ioo⟩

open DifferentialGeometry.PDE.RicciFlow.StandardCap in
private theorem s16j_far_window_core {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1) (p : ℕ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) (L : ℝ) :
    ∃ εc : ℝ, 0 < εc ∧ ∃ D₁ : ℝ, 0 < D₁ ∧
    ∀ (Q : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ → ∀ x : EuclideanSpace ℝ (Fin 3), D₁ ≤ ‖x‖ →
    ∀ Dwin : ℝ, ‖x‖ + L + 1 ≤ Dwin + 1 →
    ∃ (f : cylBand_C12X L → standardCapWindow Dwin)
      (hf : IsLocalDiffeomorph SpatialNeckCylinderModel ThreeModel ∞ f),
      (∀ z, (f z).val = (‖x‖ + z.val.2) • pointedInitialRotation x z.val.1.val) ∧
      ∀ g : SmoothRiemannianMetric ThreeModel (standardCapWindow Dwin),
        (∀ i ≤ p, ∀ v, metricDerivNorm i g
          ((Q.val.metric T).restrictOpen (standardCapWindow Dwin))
          (StandardCap.metric.restrictOpen (standardCapWindow Dwin)) v < εc) →
        ∀ q ≤ p, ∀ z, metricDerivNorm q (localPullMetric g f hf)
          ((cylFam_C12X T).restrictOpen (cylBand_C12X L))
          ((cylFam_C12X T).restrictOpen (cylBand_C12X L)) z ≤ ε₁ := by
  obtain ⟨Dref, hDref, hbound⟩ := exists_uniform_standard_metric_deriv_norm_reference_bound
    Θ hΘ0 hΘ p
  obtain ⟨δA, hδA, hδA1, hδAdim, hδAbud⟩ :=
    exists_metric_reference_change_delta (E := EuclideanSpace ℝ (Fin 2) × ℝ) p hε₁
  obtain ⟨δB, hδB, hδB1, hδBdim, hδBbud⟩ :=
    exists_metric_reference_change_delta (E := EuclideanSpace ℝ (Fin 2) × ℝ) p hδA
  obtain ⟨Dg, hDg, hfar⟩ := StandardSolution.exists_far_radial_cylinder_close_C12X hΘ p hδB (L + 1)
  have hεc : 0 < δA / ((Dref + 1) * ((p : ℝ) + 1)) := by positivity
  refine ⟨_, hεc, max Dg (|L| + 2), lt_of_lt_of_le hDg (le_max_left _ _), ?_⟩
  intro Q T hT x hx Dwin hfit
  have hxL : |L| + 2 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hLabs := le_abs_self L
  obtain ⟨F, G, U, hF, -, hKU, hUs, hGU, hclose⟩ := hfar Q T hT x ((le_max_left _ _).trans hx)
  set Φ := initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖ with hΦdef
  have hFΦ : (F : SpatialNeckCylinder → EuclideanSpace ℝ (Fin 3)) = Φ := funext fun z => by
    rw [hF, hΦdef, initialPolarDiffeomorph_apply]
  have hpos : ∀ z : cylBand_C12X L, 0 < ‖x‖ + z.val.2 := fun z => by
    have h := z.2.2.1
    linarith
  have hsrc : ∀ z : cylBand_C12X L, z.val ∈ Φ.source := fun z => by
    rw [hΦdef, initialPolarDiffeomorph_source]
    exact hpos z
  have hf0 : IsLocalDiffeomorph SpatialNeckCylinderModel ThreeModel ∞
      (fun z : cylBand_C12X L => Φ z.val) :=
    isLocalDiffeomorph_restrict_open (cylBand_C12X L) fun z =>
      PartialDiffeomorph.isLocalDiffeomorphAt SpatialNeckCylinderModel ThreeModel ∞ Φ (hsrc z)
  have hmem : ∀ z : cylBand_C12X L, Φ z.val ∈ standardCapWindow Dwin := fun z => by
    change ‖Φ z.val‖ < Dwin + 1
    rw [hΦdef, initialPolarDiffeomorph_norm _ _ (hpos z)]
    linarith [z.2.2.2]
  let f : cylBand_C12X L → standardCapWindow Dwin := fun z => ⟨Φ z.val, hmem z⟩
  have hf : IsLocalDiffeomorph SpatialNeckCylinderModel ThreeModel ∞ f :=
    isLocalDiffeomorph_codRestrict_C12X (standardCapWindow Dwin) hf0 hmem
  refine ⟨f, hf, fun z => initialPolarDiffeomorph_apply _ _ _, ?_⟩
  intro g hg q hq z
  set Qw := (Q.val.metric T).restrictOpen (standardCapWindow Dwin) with hQw
  have hVK : ∀ y : cylBand_C12X L,
      y.val ∈ (univ : Set SpatialNeckSphere) ×ˢ Icc (-(L + 1)) (L + 1) :=
    fun y => ⟨mem_univ _, y.2.2.1.le, y.2.2.2.le⟩
  have hQV : localPullMetric Qw f hf = G.restrictOpen (cylBand_C12X L) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hd (a : TangentSpace SpatialNeckCylinderModel y) :
        mfderiv SpatialNeckCylinderModel ThreeModel f y a =
          mfderiv SpatialNeckCylinderModel (𝓡 3) F y.val a := by
      have h1 := mfderiv_comp_apply (I := SpatialNeckCylinderModel) (I' := ThreeModel)
        (I'' := ThreeModel) y ((isLocalDiffeomorph_subtype_val (standardCapWindow Dwin)
          (f y)).mdifferentiableAt (by decide)) (hf.mdifferentiable (by decide) y) a
      have h2 : ((Subtype.val : standardCapWindow Dwin → EuclideanSpace ℝ (Fin 3)) ∘ f) =
          (F : SpatialNeckCylinder → EuclideanSpace ℝ (Fin 3)) ∘ Subtype.val := by
        rw [hFΦ]
        rfl
      rw [mfderiv_subtype_val_apply] at h1
      rw [← h1, h2, mfderiv_comp_apply y ((F.mdifferentiableAt (by decide) (hUs (hKU (hVK y)))))
        ((isLocalDiffeomorph_subtype_val (cylBand_C12X L) y).mdifferentiableAt (by decide)),
        mfderiv_subtype_val_apply]
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hd, hd, hGU y.val (hKU (hVK y)) v w]
    rw [hFΦ]
  have ha : ∀ y : cylBand_C12X L, ∀ k ≤ p, metricDerivNorm k (localPullMetric g f hf)
      (localPullMetric Qw f hf) (localPullMetric Qw f hf) y ≤ δA := by
    intro y k hk
    rw [metricDerivNorm_localPullMetric]
    have hsum : (∑ i ∈ Finset.range (p + 1), metricDerivNorm i g Qw
        (StandardCap.metric.restrictOpen (standardCapWindow Dwin)) (f y)) ≤
          ((p : ℝ) + 1) * (δA / ((Dref + 1) * ((p : ℝ) + 1))) := by
      calc _ ≤ ∑ _i ∈ Finset.range (p + 1), δA / ((Dref + 1) * ((p : ℝ) + 1)) :=
            Finset.sum_le_sum fun i hi =>
              (hg i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (f y)).le
        _ = _ := by simp
    have hfin : Dref * (((p : ℝ) + 1) * (δA / ((Dref + 1) * ((p : ℝ) + 1)))) ≤ δA := by
      rw [show ((p : ℝ) + 1) * (δA / ((Dref + 1) * ((p : ℝ) + 1))) = δA / (Dref + 1) by
        field_simp]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    exact (hbound (standardCapWindow Dwin) Q T hT g Qw k hk (f y)).trans
      ((mul_le_mul_of_nonneg_left hsum hDref).trans hfin)
  set CV := (cylFam_C12X T).restrictOpen (cylBand_C12X L) with hCV
  have hb : ∀ y : cylBand_C12X L, ∀ k ≤ p,
      metricDerivNorm k (localPullMetric Qw f hf) CV CV y ≤ δB := by
    intro y k hk
    rw [hQV, hCV, metricDerivNorm_restrictOpen]
    exact (hclose k hk y.val (hVK y)).le
  have hc : ∀ y : cylBand_C12X L, ∀ k ≤ p, metricDerivNorm k CV
      (localPullMetric Qw f hf) (localPullMetric Qw f hf) y ≤ δA := fun y k hk =>
    metric_deriv_norm_reference_change_le isOpen_univ CV (localPullMetric Qw f hf) CV p hδB.le
      hδB1.le hδBdim hδBbud
      (fun y' _ k' _ => by rw [metricDerivNorm_self]; exact hδB.le)
      (fun y' _ k' hk' => hb y' k' hk') y (mem_univ _) k hk
  exact metric_deriv_norm_reference_change_le isOpen_univ (localPullMetric g f hf)
    CV (localPullMetric Qw f hf) p hδA.le hδA1.le hδAdim hδAbud
    (fun y' _ k' hk' => ha y' k' hk') (fun y' _ k' hk' => hc y' k' hk') z (mem_univ _) q hq

open DifferentialGeometry.PDE.RicciFlow.StandardCap in
/-- **Far window ⇒ cylinder.**  On the band `S² × (-(L+1), L+1)` the radial chart
`f (ω, z) = (‖x‖ + z) • rot_x ω` into the window `standardCapWindow Dwin` pulls back every window
metric `g` which is `εc`-close in `C^{max p 2}` to a standard solution at time `T ∈ [0, Θ]`
(reference: the initial metric) to a metric `ε₁`-close in `C^p` to `cylFam T` (reference:
`cylFam T`); and the scalar curvature of `g` at `x` is `ε₁`-close to `(1 - T)⁻¹`. -/
theorem exists_far_window_cylinder_close_C12X {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1) (p : ℕ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) {L : ℝ} (hL : 0 ≤ L) :
    ∃ εc : ℝ, 0 < εc ∧ ∃ D₁ : ℝ, 0 < D₁ ∧
    ∀ (Q : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ → ∀ x : EuclideanSpace ℝ (Fin 3), D₁ ≤ ‖x‖ →
    ∀ Dwin : ℝ, ‖x‖ + L + 1 ≤ Dwin + 1 →
    ∃ (f : cylBand_C12X L → standardCapWindow Dwin)
      (hf : IsLocalDiffeomorph SpatialNeckCylinderModel ThreeModel ∞ f),
      (∀ z, (f z).val = (‖x‖ + z.val.2) • pointedInitialRotation x z.val.1.val) ∧
      ∀ g : SmoothRiemannianMetric ThreeModel (standardCapWindow Dwin),
        (∀ i ≤ max p 2, ∀ v, metricDerivNorm i g
          ((Q.val.metric T).restrictOpen (standardCapWindow Dwin))
          (StandardCap.metric.restrictOpen (standardCapWindow Dwin)) v < εc) →
        (∀ q ≤ p, ∀ z, metricDerivNorm q (localPullMetric g f hf)
          ((cylFam_C12X T).restrictOpen (cylBand_C12X L))
          ((cylFam_C12X T).restrictOpen (cylBand_C12X L)) z ≤ ε₁) ∧
        ∀ hx : x ∈ standardCapWindow Dwin, |metricScalarAt g ⟨x, hx⟩ - (1 - T)⁻¹| ≤ ε₁ := by
  set c₀ := (2 * (1 - Θ))⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := inv_pos.mpr (by linarith)
  set ε' := min (1 / 2) (ε₁ / (6 * (720 + c₀))) with hε'
  have hε'pos : 0 < ε' := lt_min (by norm_num) (by positivity)
  have hε'half : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'ε : ε' ≤ ε₁ / (6 * (720 + c₀)) := min_le_right _ _
  have hε'1 : ε' ≤ ε₁ := hε'ε.trans (div_le_self hε₁.le (by nlinarith))
  obtain ⟨εc, hεc, D₁, hD₁, hcore⟩ := s16j_far_window_core hΘ0 hΘ (max p 2) hε'pos L
  refine ⟨εc, hεc, D₁, hD₁, fun Q T hT x hx Dwin hfit => ?_⟩
  obtain ⟨f, hf, hform, hcl⟩ := hcore Q T hT x hx Dwin hfit
  refine ⟨f, hf, hform, fun g hg => ⟨fun q hq z =>
    (hcl g hg q (le_max_of_le_left hq) z).trans hε'1, fun hxw => ?_⟩⟩
  have hT1 : T < 1 := hT.2.trans_lt hΘ
  let z0 : cylBand_C12X L :=
    ⟨(DifferentialGeometry.Geometry.Neck.spherePoint, 0), mem_univ _, by linarith, by linarith⟩
  have hfz : f z0 = ⟨x, hxw⟩ := by
    apply Subtype.ext
    rw [hform]
    exact (initialPolarDiffeomorph_apply _ _ _).symm.trans (pointedInitialRotation_center x)
  have hsc := abs_scalar_sub_le_of_cylFam_close_C12X hT1 (cylBand_C12X L)
    (localPullMetric g f hf) z0 hε'half fun m hm => hcl g hg m (le_max_of_le_right hm) z0
  rw [metricScalarAt_localPull, hfz] at hsc
  refine hsc.trans ?_
  have hc : (2 * (1 - T))⁻¹ ≤ c₀ := by
    rw [hc₀]
    exact inv_anti₀ (by linarith) (by linarith [hT.2])
  have hc0 : 0 ≤ (2 * (1 - T))⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : (240 * 3 * ε' + ε' * (2 * (1 - T))⁻¹) / (1 - ε') ≤ 2 * (ε' * (720 + c₀)) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hc hε'pos.le, mul_nonneg hε'pos.le hc0]
  have h2 : ε' * (6 * (720 + c₀)) ≤ ε₁ := (le_div_iff₀ (by positivity)).mp hε'ε
  nlinarith

end FarWindow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
