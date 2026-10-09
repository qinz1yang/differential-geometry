import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Euler field and the smooth radial lift of the soul flow field (lane CMS3-CARRIER2, G4b)

LFR47 (blueprint master207A, `lem:collapse-soul-flow-smooth-carrier`): "the retained ray formula
identifies `V` with unit radial differentiation in `Ê`. Inside, it identifies `V` with
`a(|w|) ∂_{|w|}`, zero near zero ... This is a global smooth field on the smooth bundle."

For a smooth vector bundle `V → B` with a smooth fibre metric:

* `carrierFiberScale (t, z) = ⟨z.proj, t • z.snd⟩` (smooth, `contMDiff_totalSpace_smul`);
* `carrierEulerVector z = d/dt|_{t=1} ⟨z.proj, t • z.snd⟩`, the Euler (position) field; the section
  `z ↦ ⟨z, carrierEulerVector z⟩` is smooth (tangent map of the scaling, evaluated on the smooth
  section `z ↦ ((1, 1), (z, 0))` of `T(ℝ × TotalSpace)`);
* `carrierRadialCoeff prof q = prof (√q) / √q`: smooth when `prof` is smooth and vanishes on
  `(-∞, δ]`, `δ > 0`;
* `carrierRadialField prof z = carrierRadialCoeff prof ⟪z.2, z.2⟫ • carrierEulerVector z`
  `= prof(|w|) ∂_{|w|}`: a smooth section;
* `mfderiv_carrierRadialField`: if a differentiable `e : TotalSpace F V → M` and a field `X` on `M`
  satisfy LFR46's ray identification (`X (e ⟨s, τ w⟩) = prof τ • ∂_τ e ⟨s, τ w⟩` for unit `w`,
  `τ > 0`) and `X = 0` on `e` of the zero section, then `de (carrierRadialField prof z) = X (e z)`
  for every `z`;
* `exists_smooth_carrierLift`: the first conclusion of the frozen LFR47 statement.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Euler

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, AddCommGroup (V s)]
  [∀ s, Module ℝ (V s)] [∀ s, TopologicalSpace (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V IB]

variable (F V) in
/-- Fibrewise scaling `(t, z) ↦ t • z` on the total space. -/
def carrierFiberScale (p : ℝ × TotalSpace F V) : TotalSpace F V :=
  ⟨p.2.proj, p.1 • p.2.snd⟩

omit [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem contMDiff_carrierFiberScale :
    ContMDiff (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞ (carrierFiberScale F V) :=
  DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [∀ s, TopologicalSpace (V s)] [ChartedSpace HB B]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem carrierFiberScale_one (z : TotalSpace F V) : carrierFiberScale F V (1, z) = z := by
  change (⟨z.proj, (1 : ℝ) • z.snd⟩ : TotalSpace F V) = z
  rw [one_smul]

variable (IB) in
/-- The Euler (position) vector at `z`: the velocity at `t = 1` of `t ↦ t • z`. -/
def carrierEulerVector (z : TotalSpace F V) : TangentSpace (IB.prod 𝓘(ℝ, F)) z :=
  mfderiv (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) (carrierFiberScale F V) (1, z)
    ((1 : ℝ), (0 : EB × F))

/-- **The Euler field is a smooth section of the tangent bundle of the total space.** -/
theorem contMDiff_carrierEulerVector :
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)).tangent ∞
      (fun z => (⟨z, carrierEulerVector IB z⟩ : TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V))) := by
  have hσ : ContMDiff (IB.prod 𝓘(ℝ, F)) (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))).tangent ∞
      (fun z : TotalSpace F V =>
        (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ (IB.prod 𝓘(ℝ, F)) (TotalSpace F V)).symm
          ((⟨(1 : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ),
            (Bundle.zeroSection (EB × F) (TangentSpace (IB.prod 𝓘(ℝ, F)) :
              TotalSpace F V → Type _) z))) :=
    contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace (IB.prod 𝓘(ℝ, F)) :
          TotalSpace F V → Type _)))
  have hT := (contMDiff_carrierFiberScale (IB := IB) (F := F) (V := V)).contMDiff_tangentMap
    (m := ∞) (by simp)
  refine (hT.comp hσ).congr ?_
  intro z
  change (⟨z, carrierEulerVector IB z⟩ : TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V)) =
    ⟨carrierFiberScale F V (1, z), carrierEulerVector IB z⟩
  exact congrArg (fun b => (⟨b, carrierEulerVector IB z⟩ :
    TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V))) (carrierFiberScale_one z).symm

omit [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
/-- The Euler vector is the velocity of the scaling curve `t ↦ t • z` at `t = 1`. -/
theorem hasMFDerivAt_carrierScaleCurve (z : TotalSpace F V) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (IB.prod 𝓘(ℝ, F))
      (fun t : ℝ => (⟨z.proj, t • z.snd⟩ : TotalSpace F V)) 1
      ((1 : ℝ →L[ℝ] ℝ).smulRight (carrierEulerVector IB z)) := by
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (fun t : ℝ => (t, z)) 1
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) :=
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) (1 : ℝ)).prodMk (hasMFDerivAt_const z 1)
  have hμ : HasMFDerivAt (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F))
      (carrierFiberScale F V) (1, z)
      (mfderiv (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) (carrierFiberScale F V) (1, z)) :=
    (contMDiff_carrierFiberScale.mdifferentiable (by simp) (1, z)).hasMFDerivAt
  have h := hμ.comp 1 hc
  have hd : ((1 : ℝ →L[ℝ] ℝ).smulRight (carrierEulerVector IB z) : ℝ →L[ℝ] EB × F) =
      (mfderiv (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) (carrierFiberScale F V)
        (1, z)).comp ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] EB × F)) := by
    refine ContinuousLinearMap.ext_ring ?_
    change (1 : ℝ →L[ℝ] ℝ) 1 • carrierEulerVector IB z = carrierEulerVector IB z
    rw [one_apply_eq_self, one_smul]
  exact h.congr_mfderiv hd.symm

end Euler

section Coefficient

/-- The radial coefficient `q ↦ prof (√q) / √q` (so that `coeff (|w|²) • w = prof (|w|) • w/|w|`). -/
def carrierRadialCoeff (prof : ℝ → ℝ) (q : ℝ) : ℝ :=
  prof (Real.sqrt q) / Real.sqrt q

/-- The radial coefficient is smooth when `prof` is smooth and vanishes on `(-∞, δ]`, `δ > 0`. -/
theorem contDiff_carrierRadialCoeff {δ : ℝ} (hδ : 0 < δ) {prof : ℝ → ℝ}
    (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) :
    ContDiff ℝ ∞ (carrierRadialCoeff prof) := by
  refine contDiff_iff_contDiffAt.mpr fun q => ?_
  rcases lt_or_ge q (δ ^ 2) with hq | hq
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hq] with q' hq'
    have hs : Real.sqrt q' < δ := (Real.sqrt_lt' hδ).mpr hq'
    simp [carrierRadialCoeff, hprof0 _ hs.le]
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le (by positivity) hq).ne'
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity) hq)).ne'
    exact (hprof.contDiffAt.comp q (Real.contDiffAt_sqrt hq0)).div
      (Real.contDiffAt_sqrt hq0) hsq

theorem carrierRadialCoeff_mul_self {prof : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ) :
    carrierRadialCoeff prof (τ * τ) = prof τ / τ := by
  simp [carrierRadialCoeff, Real.sqrt_mul_self hτ.le]

theorem carrierRadialCoeff_zero (prof : ℝ → ℝ) : carrierRadialCoeff prof 0 = 0 := by
  simp [carrierRadialCoeff]

end Coefficient

section Radial

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V IB]

variable (IB) in
/-- The radial field `prof (|w|) ∂_{|w|} = (prof (|w|) / |w|) • (Euler field)` on the total space. -/
def carrierRadialField (prof : ℝ → ℝ) (z : TotalSpace F V) : TangentSpace (IB.prod 𝓘(ℝ, F)) z :=
  carrierRadialCoeff prof (inner ℝ z.snd z.snd) • carrierEulerVector IB z

/-- **The radial field is a smooth section** (`prof` smooth, vanishing on `(-∞, δ]`, `δ > 0`). -/
theorem contMDiff_carrierRadialField [IsContMDiffRiemannianBundle IB ∞ F V] {δ : ℝ} (hδ : 0 < δ)
    {prof : ℝ → ℝ} (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) :
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)).tangent ∞
      (fun z => (⟨z, carrierRadialField IB prof z⟩ :
        TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V))) := by
  have hq : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun z : TotalSpace F V => inner ℝ z.snd z.snd) :=
    contMDiff_id.inner_bundle contMDiff_id
  have hc : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun z : TotalSpace F V => carrierRadialCoeff prof (inner ℝ z.snd z.snd)) :=
    (contDiff_carrierRadialCoeff hδ hprof hprof0).comp_contMDiff hq
  exact hc.smul_section contMDiff_carrierEulerVector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
/-- The differential of `e` on the Euler vector at `τ • w` is `τ` times the ray velocity. -/
theorem mfderiv_carrierEulerVector_of_ray {e : TotalSpace F V → M} (s : B) (w : V s) (τ : ℝ)
    (he : MDifferentiableAt (IB.prod 𝓘(ℝ, F)) I e ⟨s, τ • w⟩)
    {Y : TangentSpace I (e ⟨s, τ • w⟩)}
    (hY : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y)) :
    mfderiv (IB.prod 𝓘(ℝ, F)) I e ⟨s, τ • w⟩ (carrierEulerVector IB ⟨s, τ • w⟩) = τ • Y := by
  have h1 : (⟨s, (1 : ℝ) • τ • w⟩ : TotalSpace F V) = ⟨s, τ • w⟩ :=
    carrierFiberScale_one (⟨s, τ • w⟩ : TotalSpace F V)
  have hez : HasMFDerivAt (IB.prod 𝓘(ℝ, F)) I e (⟨s, (1 : ℝ) • τ • w⟩ : TotalSpace F V)
      (mfderiv (IB.prod 𝓘(ℝ, F)) I e ⟨s, τ • w⟩) := by
    rw [h1]
    exact he.hasMFDerivAt
  have hA := hez.comp 1 (hasMFDerivAt_carrierScaleCurve (IB := IB) (⟨s, τ • w⟩ : TotalSpace F V))
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ => u * τ) 1
      ((1 : ℝ →L[ℝ] ℝ).smulRight τ) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr (hasDerivAt_mul_const τ).hasFDerivAt
  have hτ1 : (fun u : ℝ => u * τ) 1 = τ := one_mul τ
  have hY' : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) ((fun u : ℝ => u * τ) 1)
      ((1 : ℝ →L[ℝ] ℝ).smulRight Y) := by
    rw [hτ1]
    exact hY
  have hB := hY'.comp 1 hlin
  have hfun : (fun t : ℝ => e ⟨s, t • w⟩) ∘ (fun u : ℝ => u * τ) =
      e ∘ (fun t : ℝ => (⟨s, t • τ • w⟩ : TotalSpace F V)) := by
    funext u
    change e ⟨s, (u * τ) • w⟩ = e ⟨s, u • τ • w⟩
    rw [smul_smul]
  rw [hfun] at hB
  have hL := congrArg (fun L : ℝ →L[ℝ] E => L 1) (hA.mfderiv.symm.trans hB.mfderiv)
  change mfderiv (IB.prod 𝓘(ℝ, F)) I e ⟨s, τ • w⟩
      ((1 : ℝ →L[ℝ] ℝ) 1 • carrierEulerVector IB (⟨s, τ • w⟩ : TotalSpace F V)) =
    (1 : ℝ →L[ℝ] ℝ) ((1 : ℝ →L[ℝ] ℝ) 1 • τ) • Y at hL
  rwa [one_apply_eq_self, one_smul, one_apply_eq_self, smul_eq_mul, one_mul] at hL

omit [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
/-- **The radial field lifts `X`** along any differentiable `e` with LFR46's ray identification. -/
theorem mfderiv_carrierRadialField {e : TotalSpace F V → M}
    (he : ∀ z, MDifferentiableAt (IB.prod 𝓘(ℝ, F)) I e z)
    (X : (x : M) → TangentSpace I x) (prof : ℝ → ℝ) (hXS : ∀ s : B, X (e ⟨s, 0⟩) = 0)
    (hXray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
        X (e ⟨s, τ • w⟩) = prof τ • Y)
    (z : TotalSpace F V) :
    mfderiv (IB.prod 𝓘(ℝ, F)) I e z (carrierRadialField IB prof z) = X (e z) := by
  have key : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ →
      mfderiv (IB.prod 𝓘(ℝ, F)) I e ⟨s, τ • w⟩ (carrierRadialField IB prof ⟨s, τ • w⟩) =
        X (e ⟨s, τ • w⟩) := by
    intro s w hw τ hτ
    obtain ⟨Y, hY, hXY⟩ := hXray s w hw τ hτ
    have hin : inner ℝ (τ • w) (τ • w) = τ * τ := by
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hw]
      ring
    have hcoef : carrierRadialField IB prof (⟨s, τ • w⟩ : TotalSpace F V) =
        (prof τ / τ) • carrierEulerVector IB (⟨s, τ • w⟩ : TotalSpace F V) := by
      change carrierRadialCoeff prof (inner ℝ (τ • w) (τ • w)) • _ = _
      rw [hin, carrierRadialCoeff_mul_self hτ]
    rw [hcoef, map_smul, mfderiv_carrierEulerVector_of_ray s w τ (he _) hY, smul_smul,
      div_mul_cancel₀ _ hτ.ne', hXY]
  obtain ⟨s, v⟩ := z
  by_cases hv : v = 0
  · subst hv
    have h0 : carrierRadialField IB prof (⟨s, 0⟩ : TotalSpace F V) = 0 := by
      change carrierRadialCoeff prof (inner ℝ (0 : V s) 0) • _ = _
      rw [inner_zero_left, carrierRadialCoeff_zero, zero_smul]
    rw [h0, map_zero, hXS]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have h := key s (‖v‖⁻¹ • v) (norm_smul_inv_norm hv) ‖v‖ (norm_pos_iff.mpr hv)
    rwa [smul_inv_smul₀ hn] at h

/-- **LFR47, first conclusion (the smooth lift of the soul-flow field).** -/
theorem exists_smooth_carrierLift [IsContMDiffRiemannianBundle IB ∞ F V]
    {e : TotalSpace F V → M} (he : ∀ z, MDifferentiableAt (IB.prod 𝓘(ℝ, F)) I e z)
    (X : (x : M) → TangentSpace I x) {δ : ℝ} (hδ : 0 < δ) (prof : ℝ → ℝ)
    (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) (hXS : ∀ s : B, X (e ⟨s, 0⟩) = 0)
    (hXray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
        X (e ⟨s, τ • w⟩) = prof τ • Y) :
    ∃ Xhat : (z : TotalSpace F V) → TangentSpace (IB.prod 𝓘(ℝ, F)) z,
      ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)).tangent ∞
        (fun z => (⟨z, Xhat z⟩ : TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V))) ∧
      ∀ z, mfderiv (IB.prod 𝓘(ℝ, F)) I e z (Xhat z) = X (e z) :=
  ⟨carrierRadialField IB prof, contMDiff_carrierRadialField hδ hprof hprof0,
    mfderiv_carrierRadialField he X prof hXS hXray⟩

end Radial

end DifferentialGeometry.Geometry.FiniteSoul
