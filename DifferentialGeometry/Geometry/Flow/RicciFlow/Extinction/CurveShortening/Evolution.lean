import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem normSq_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) (x t : ℝ) : 0 ≤ c.normSq g V x t := by
  rcases eq_or_ne (V x t) 0 with hv | hv
  · simp [normSq, hv]
  · exact ((g t).pos (c.lift x t) (V x t) hv).le

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curvature_sq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (x t : ℝ) : c.curvature g x t ^ 2 = c.curvatureSq g x t :=
  Real.sq_sqrt (c.normSq_nonneg g (c.curvatureVector g) x t)

def ricciTangent (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) (x t : ℝ) : ℝ :=
  G.ricciAt t (c.lift x t) (vec2 (c.unitTangent G.metric x t) (c.unitTangent G.metric x t))

def q (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) (x t : ℝ) : ℝ :=
  c.curvatureSq G.metric x t + c.ricciTangent G x t


def normalCurvatureDerivative (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) :
    c.Field (I := I) := fun x t =>
  c.Ds g (c.curvatureVector g) x t + c.curvatureSq g x t • c.unitTangent g x t

def regularizedCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (ε x t : ℝ) : ℝ := Real.sqrt (c.curvatureSq g x t + ε ^ 2)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem regularizedCurvature_error (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (ε : ℝ) (hε : 0 ≤ ε) (x t : ℝ) :
    0 ≤ c.regularizedCurvature g ε x t - c.curvature g x t ∧
      c.regularizedCurvature g ε x t - c.curvature g x t ≤ ε := by
  have hk := c.curvature_nonneg g x t
  have hsq := c.curvature_sq g x t
  constructor
  · exact sub_nonneg.mpr (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε)))
  · apply sub_le_iff_le_add.mpr
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact add_nonneg hε hk
    · nlinarith [mul_nonneg hε hk]

end CurveMap

variable [hBoundary : I.Boundaryless] {D : RealTimeInterval} {a b s u : ℝ}
include hBoundary

section TangentGeometry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary

private theorem tangent_geometry_smul_along_smooth (gamma : ℝ → M)
    (V : ∀ x, TangentSpace I (gamma x))
    (f : ℝ → ℝ) (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (f x • V x)) := by
  intro x
  have hv := (contMDiffAt_totalSpace.mp (hV x))
  rw [contMDiffAt_totalSpace]
  refine ⟨hv.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (gamma x)
  have he : gamma x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma x)
  have hnear : ∀ᶠ y in 𝓝 x, gamma y ∈ e.baseSet :=
    hv.1.continuousAt (e.open_baseSet.mem_nhds he)
  apply ((hf x).smul hv.2).congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  exact (e.linear ℝ hy).2 (f y) (V y)

private theorem tangent_geometry_inner_along_smooth (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (V W : ∀ x, TangentSpace I (gamma x))
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (W x))) :
    ContDiff ℝ ∞ (fun x => g.inner (gamma x) (V x) (W x)) := by
  have htotal : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (gamma x) (g.inner (gamma x) (V x) (W x))) := by
    apply ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.comp hg
    · exact hV
    · exact hW
  apply contMDiff_iff_contDiff.mp
  intro x
  have hx := htotal x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

private theorem tangent_geometry_velocity_smooth (gamma : ℝ → M)
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (mfderiv 𝓘(ℝ, ℝ) I gamma x (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ)) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I gamma ∘ fun x : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ))
  exact (hg.contMDiff_tangentMap (le_refl _)).comp hunit

private theorem tangent_geometry_cov_along_smooth
    [FiniteDimensional ℝ E] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (V : ∀ x, TangentSpace I (gamma x))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (covDerivAlong g gamma V x)) := by
  have htwo := cov_fst_smooth g (fun x _ : ℝ => gamma x) (fun x _ => V x)
    (hV.comp contMDiff_fst)
  exact htwo.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ))))

omit [IsManifold I ∞ M] in
private theorem tangent_geometry_slice_smooth (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) := by
  have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => (x, t)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact contMDiffOn_univ.mp (hc.comp hp.contMDiffOn (fun _ _ => ⟨mem_univ _, ht⟩))

private theorem tangent_geometry_unit_smooth (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.unitTangent g x t)) := by
  have hg := tangent_geometry_slice_smooth c J hc t ht
  have hX := tangent_geometry_velocity_smooth (fun x => c.lift x t) hg
  have hi2 := tangent_geometry_inner_along_smooth (g t) (fun x => c.lift x t)
    (fun x => c.X x t) (fun x => c.X x t) hg hX hX
  have hs : ContDiff ℝ ∞ (fun x => c.speed g x t) :=
    hi2.sqrt (fun x => ne_of_gt ((g t).pos _ _ (hi x t ht)))
  exact tangent_geometry_smul_along_smooth (fun x => c.lift x t) (fun x => c.X x t)
    (fun x => (c.speed g x t)⁻¹)
    (hs.inv (fun x => ne_of_gt (c.speed_pos g hi x t ht))).contMDiff hX

private theorem tangent_geometry_curvature_smooth
    [FiniteDimensional ℝ E] [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.curvatureVector g x t)) := by
  have hg := tangent_geometry_slice_smooth c J hc t ht
  have hX := tangent_geometry_velocity_smooth (fun x => c.lift x t) hg
  have hi2 := tangent_geometry_inner_along_smooth (g t) (fun x => c.lift x t)
    (fun x => c.X x t) (fun x => c.X x t) hg hX hX
  have hs : ContDiff ℝ ∞ (fun x => c.speed g x t) :=
    hi2.sqrt (fun x => ne_of_gt ((g t).pos _ _ (hi x t ht)))
  have hDT := tangent_geometry_cov_along_smooth (g t) (fun x => c.lift x t)
    (fun x => c.unitTangent g x t) (tangent_geometry_unit_smooth g c J hc hi t ht)
  exact tangent_geometry_smul_along_smooth (fun x => c.lift x t)
    (fun x => c.Dx g (c.unitTangent g) x t) (fun x => (c.speed g x t)⁻¹)
    (hs.inv (fun x => ne_of_gt (c.speed_pos g hi x t ht))).contMDiff hDT

private theorem tangent_geometry_unit_norm (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.unitTangent g x t) (c.unitTangent g x t) = 1 := by
  have hs := c.speed_pos g hi x t ht
  have hsq : c.speed g x t ^ 2 = (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
    Real.sq_sqrt ((g t).pos _ _ (hi x t ht)).le
  simp only [CurveMap.unitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [← hsq]
  field_simp [ne_of_gt hs]

end TangentGeometry


theorem tangent_curvature_geometry (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.unitTangent g x t) (c.unitTangent g x t) = 1 ∧
    (g t).inner (c.lift x t) (c.curvatureVector g x t) (c.unitTangent g x t) = 0 ∧
    (g t).inner (c.lift x t) (c.Ds g (c.curvatureVector g) x t)
      (c.unitTangent g x t) = -c.curvatureSq g x t := by
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : SigmaCompactSpace M)
  let _ := (inferInstance : T2Space M)
  have hg := tangent_geometry_slice_smooth c J hc t ht
  have hT := tangent_geometry_unit_smooth g c J hc hi t ht
  have hH := tangent_geometry_curvature_smooth g c J hc hi t ht
  have hunit := tangent_geometry_unit_norm g c J hi
  have hDxT : ∀ y, (g t).inner (c.lift y t)
      (c.Dx g (c.unitTangent g) y t) (c.unitTangent g y t) = 0 := by
    intro y
    have hd := metric_compat_hasDerivAt_inner (by simp : (1 : WithTop ℕ∞) ≤ ∞)
      (g t) (fun y => c.lift y t) (fun y => c.unitTangent g y t)
      (fun y => c.unitTangent g y t) y hg
      (chartRep_diff _ _ hT y) (chartRep_diff _ _ hT y)
    have hf : (fun y => (g t).inner (c.lift y t)
        (c.unitTangent g y t) (c.unitTangent g y t)) = fun _ => (1 : ℝ) :=
      funext (fun y => hunit y t ht)
    rw [hf] at hd
    have hz := hd.unique (hasDerivAt_const (x := y) (c := (1 : ℝ)))
    change (g t).inner (c.lift y t) (c.Dx g (c.unitTangent g) y t)
      (c.unitTangent g y t) + (g t).inner (c.lift y t) (c.unitTangent g y t)
      (c.Dx g (c.unitTangent g) y t) = 0 at hz
    rw [(g t).symm (c.lift y t) (c.unitTangent g y t)
      (c.Dx g (c.unitTangent g) y t)] at hz
    linarith
  have horth : ∀ y, (g t).inner (c.lift y t)
      (c.curvatureVector g y t) (c.unitTangent g y t) = 0 := by
    intro y
    simp only [CurveMap.curvatureVector, CurveMap.Ds, map_smul,
      smul_apply, smul_eq_mul]
    rw [hDxT y, mul_zero]
  refine ⟨hunit x t ht, horth x, ?_⟩
  have hd := metric_compat_hasDerivAt_inner (by simp : (1 : WithTop ℕ∞) ≤ ∞)
    (g t) (fun y => c.lift y t) (fun y => c.curvatureVector g y t)
    (fun y => c.unitTangent g y t) x hg
    (chartRep_diff _ _ hH x) (chartRep_diff _ _ hT x)
  have hf : (fun y => (g t).inner (c.lift y t)
      (c.curvatureVector g y t) (c.unitTangent g y t)) = fun _ => (0 : ℝ) :=
    funext horth
  rw [hf] at hd
  have hz := hd.unique (hasDerivAt_const (x := x) (c := (0 : ℝ)))
  change (g t).inner (c.lift x t) (c.Dx g (c.curvatureVector g) x t)
    (c.unitTangent g x t) + (g t).inner (c.lift x t) (c.curvatureVector g x t)
    (c.Dx g (c.unitTangent g) x t) = 0 at hz
  have hs := congrArg (fun z : ℝ => (c.speed g x t)⁻¹ * z) hz
  simp only [mul_add, mul_zero] at hs
  have hHH : (c.speed g x t)⁻¹ * (g t).inner (c.lift x t)
      (c.curvatureVector g x t) (c.Dx g (c.unitTangent g) x t) =
      c.curvatureSq g x t := by
    simp only [CurveMap.curvatureSq, CurveMap.normSq, CurveMap.curvatureVector,
      CurveMap.Ds, map_smul, smul_apply, smul_eq_mul]
  rw [hHH] at hs
  simp only [CurveMap.Ds, map_smul, smul_apply, smul_eq_mul]
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem chartRepAtBase_smulFun {β : M} {γ : ℝ → M}
    (a : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) :
    chartRepAtBase (I := I) β γ (fun s => a s • V s) =
      fun s => a s • chartRepAtBase (I := I) β γ V s := by
  funext s
  simp only [chartRepAtBase_apply, map_smul]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem Dt_smulFun_at
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (a : ℝ → ℝ → ℝ) (V : c.Field (I := I)) (x t : ℝ)
    (huniq : UniqueDiffWithinAt ℝ J t)
    (ha : DifferentiableWithinAt ℝ (fun r => a x r) J t)
    (hV : DifferentiableWithinAt ℝ
      (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r) (fun r => V x r)) J t) :
    c.Dt g J (fun y r => a y r • V y r) x t =
      derivWithin (fun r => a x r) J t • V x t + a x t • c.Dt g J V x t := by
  set β : M := c.lift x t with hβ
  set γ : ℝ → M := fun r => c.lift x r with hγ
  set rep : ℝ → E := chartRepAtBase (I := I) β γ (fun r => V x r) with hrep
  rw [Dt_eq_symmL_chart, Dt_eq_symmL_chart]
  have hrepa : chartRepAtBase (I := I) β γ (fun r => a x r • V x r) =
      fun r => a x r • rep r := by
    rw [hγ, hrep]
    exact chartRepAtBase_smulFun (I := I) (fun r => a x r) (fun r => V x r)
  have hVdiff : DifferentiableWithinAt ℝ rep J t := by
    rw [hrep, hβ, hγ]
    exact hV
  rw [hrepa]
  rw [← hrep]
  have hderiv : derivWithin (fun r => a x r • rep r) J t =
      a x t • derivWithin rep J t + derivWithin (fun r => a x r) J t • rep t :=
    (ha.hasDerivWithinAt.smul hVdiff.hasDerivWithinAt).derivWithin huniq
  rw [hderiv]
  rw [DifferentialGeometry.Geometry.Riemannian.AlongCurve.ChartChristoffel.contraction_smul_right]
  have hself : (trivializationAt E (TangentSpace I) β).symmL ℝ β (rep t) = V x t := by
    rw [hrep, hβ, hγ]
    exact symmL_chartRepAt_self (I := I) (fun r => c.lift x r) (fun r => V x r) t
  conv_lhs => rw [map_add, map_add, map_smul, map_smul, map_smul, hself]
  rw [map_add, smul_add]
  module

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem normSq_velocity_eq_speed_sq (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (x r : ℝ) :
    c.normSq g (c.X) x r = c.speed g x r ^ 2 := by
  rw [CurveMap.speed]
  exact (Real.sq_sqrt
    (DifferentialGeometry.metric_inner_self_nonneg (g r) (c.lift x r) (c.X x r))).symm

def CurveMap.PairingEvolution (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) : Prop :=
  ∀ x t, t ∈ Icc s u → HasDerivWithinAt
    (fun r => c.normSq B.family.metric (c.X) x r)
    (-2 * c.normSq B.family.metric (c.X) x t * c.q B.family x t) (Icc s u) t

omit [SigmaCompactSpace M] hBoundary in
theorem rfs_csf_speed (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (hX : CurveMap.Field.SmoothOn (I := I) (c.X) (Icc s u))
    (hpair : CurveMap.PairingEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c)
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.speed B.family.metric x) (Icc s u) t =
      -c.q B.family x t * c.speed B.family.metric x t ∧
    c.Dt B.family.metric (Icc s u) (c.unitTangent B.family.metric) x t =
      c.Ds B.family.metric (c.curvatureVector B.family.metric) x t +
        c.q B.family x t • c.unitTangent B.family.metric x t := by
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) t := (uniqueDiffOn_Icc hsu) t ht
  have hvpos : 0 < c.speed B.family.metric x t :=
    c.speed_pos B.family.metric hc.immersed x t ht
  have hvnn : 0 ≤ c.speed B.family.metric x t := hvpos.le
  have hsq : HasDerivWithinAt (fun r => c.speed B.family.metric x r ^ 2)
      (-2 * c.speed B.family.metric x t ^ 2 * c.q B.family x t) (Icc s u) t := by
    convert hpair x t ht using 1
    · funext r
      exact (normSq_velocity_eq_speed_sq c B.family.metric x r).symm
    · rw [normSq_velocity_eq_speed_sq]
  have hspeed : HasDerivWithinAt (c.speed B.family.metric x)
      (-c.q B.family x t * c.speed B.family.metric x t) (Icc s u) t := by
    have h := hsq.sqrt (by positivity)
    convert h using 1
    · funext r
      exact (Real.sqrt_sq (c.speed_nonneg B.family.metric x r)).symm
    · rw [Real.sqrt_sq hvnn]
      field_simp
  constructor
  · exact hspeed.derivWithin huniq
  · have hslice : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift x r) (c.X x r) : TangentBundle I M)) (Icc s u) t := by
      have h0 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
          (fun p : ℝ × ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (c.lift p.1 p.2) (c.X p.1 p.2) : TangentBundle I M))
          (univ ×ˢ Icc s u) (x, t) :=
        hX (x, t) ⟨mem_univ x, ht⟩
      refine h0.comp t ?_ ?_
      · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
      · intro r hr
        exact ⟨mem_univ x, hr⟩
    have hV : DifferentiableWithinAt ℝ
        (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r) (fun r => c.X x r))
        (Icc s u) t :=
      chartRepAtBase_differentiableWithinAt (I := I) hslice
    have ha : DifferentiableWithinAt ℝ
        (fun r => (c.speed B.family.metric x r)⁻¹) (Icc s u) t :=
      hspeed.differentiableWithinAt.inv (ne_of_gt hvpos)
    have hleib := Dt_smulFun_at c B.family.metric (Icc s u)
      (fun y r => (c.speed B.family.metric y r)⁻¹) (c.X) x t huniq ha hV
    have hinv : derivWithin (fun r => (c.speed B.family.metric x r)⁻¹) (Icc s u) t =
        c.q B.family x t * (c.speed B.family.metric x t)⁻¹ := by
      have hfun : (fun r => (c.speed B.family.metric x r)⁻¹) =
          (c.speed B.family.metric x)⁻¹ := rfl
      rw [hfun]
      have h := hspeed.inv (ne_of_gt hvpos)
      rw [h.derivWithin huniq]
      field_simp
    have hDTX : c.Dt B.family.metric (Icc s u) (c.X) x t =
        c.Dx B.family.metric (c.velocity (Icc s u)) x t :=
      pullback_torsion_free B.toSmoothMetricWindow hsu hwindow c hc.smooth x t ht
    have hvel : c.Dx B.family.metric (c.velocity (Icc s u)) x t =
        c.Dx B.family.metric (c.curvatureVector B.family.metric) x t := by
      simp only [CurveMap.Dx]
      congr 1
      funext y
      exact hc.equation y t ht
    have hDs : c.Ds B.family.metric (c.curvatureVector B.family.metric) x t =
        (c.speed B.family.metric x t)⁻¹ •
          c.Dx B.family.metric (c.curvatureVector B.family.metric) x t := rfl
    have hTan : c.unitTangent B.family.metric x t =
        (c.speed B.family.metric x t)⁻¹ • c.X x t := rfl
    have hTanFun : c.unitTangent B.family.metric =
        (fun y r => (c.speed B.family.metric y r)⁻¹ • c.X y r) := rfl
    rw [hTan, hTanFun, hleib, hinv, hDTX, hvel, hDs, smul_smul]
    module


theorem scalar_arclength_commutator (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (f : ℝ → ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.ds B.family.metric f x) (Icc s u) t -
      c.ds B.family.metric (fun y r => derivWithin (f y) (Icc s u) r) x t =
    c.q B.family x t * c.ds B.family.metric f x t := by
  sorry

theorem rfs_csf_curvature (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.curvatureSq B.family.metric x) (Icc s u) t =
      c.ds B.family.metric (c.ds B.family.metric (c.curvatureSq B.family.metric)) x t -
      2 * c.normSq B.family.metric (c.normalCurvatureDerivative B.family.metric) x t +
      2 * c.curvatureSq B.family.metric x t ^ 2 +
      4 * c.curvatureSq B.family.metric x t * c.ricciTangent B.family x t -
      2 * B.family.ricciAt t (c.lift x t)
        (vec2 (c.curvatureVector B.family.metric x t) (c.curvatureVector B.family.metric x t)) +
      2 * (B.family.metric t).inner (c.lift x t)
        (riemannVector B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
          (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t))
        (c.curvatureVector B.family.metric x t) -
      4 * nablaRicci B.family t (c.lift x t) (c.unitTangent B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.curvatureVector B.family.metric x t) +
      2 * nablaRicci B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t) := by
  sorry

omit [SigmaCompactSpace M] in
theorem riemannVector_eq_riemannOp (G : SolutionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (A V W : TangentSpace I p) :
    riemannVector G t p A V W =
      riemannOp (LeviCivita (G.metric t)) p A V W := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (G.metric t)) ∞ :=
    leviCivita_contMDiffCovariantDerivativeLocally (I := I) (G.metric t)
  change connectionRiemannCurvatureField (G.connection t)
      (tangentConstAt (I := I) p A) (tangentConstAt (I := I) p V)
      (tangentConstAt (I := I) p W) p = _
  exact connectionRiemannCurvatureField_tangentConst_eq_riemannOp (I := I)
    (cov := LeviCivita (G.metric t)) hcov p A V W

omit [SigmaCompactSpace M] in
theorem riemann_pair_eq_rm04 (G : SolutionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (A V : TangentSpace I p) :
    (G.metric t).inner p (riemannVector G t p A V V) A =
      (G.rm04At t p) (vec4 A V V A) := by
  have hrm : metricRm04StandardAt (I := I) (G.metric t) p A V V A =
      (G.rm04At t p) (vec4 A V V A) :=
    metricRm04StandardAt_apply (I := I) (G.metric t) p A V V A
  rw [riemannVector_eq_riemannOp G t p A V V, ← hrm,
    rm04_eq_inner (I := I) (G.metric t) p A V A]
  exact ((G.metric t).symm p A _).symm

omit [SigmaCompactSpace M] hBoundary in
theorem rm04_unit_le (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) {p : M} (X T : TangentSpace I p)
    (hTT : (B.family.metric t).inner p T T = 1) :
    (B.family.rm04At t p) (vec4 X T T X) ≤
      B.B₁ * (B.family.metric t).inner p X X := by
  have h1 := abs_apply_le_norm0S (B.family.metric t) p 4 (B.family.rm04At t p) (vec4 X T T X)
  have hprod : (∏ a : Fin 4, Real.sqrt ((B.family.metric t).inner p ((vec4 X T T X) a)
      ((vec4 X T T X) a))) = (B.family.metric t).inner p X X := by
    rw [Fin.prod_univ_four]
    simp only [vec4, Fin.isValue, ↓reduceIte, one_ne_zero, hTT, Real.sqrt_one, mul_one, Fin.reduceEq]
    exact Real.mul_self_sqrt (DifferentialGeometry.metric_inner_self_nonneg (B.family.metric t) p X)
  rw [hprod] at h1
  have hnorm : Real.sqrt (normSq0S (B.family.metric t) p 4 (B.family.rm04At t p)) ≤ B.B₁ :=
    Real.sqrt_le_iff.mpr ⟨B.B₁_nonneg, B.riemann_bound t ht p⟩
  exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right hnorm
    (DifferentialGeometry.metric_inner_self_nonneg (B.family.metric t) p X)))

omit [SigmaCompactSpace M] hBoundary in
theorem ricci_unit_le (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) {p : M} (T : TangentSpace I p)
    (hTT : (B.family.metric t).inner p T T = 1) :
    B.family.ricciAt t p (vec2 T T) ≤ B.B₀ := by
  have h1 := abs_apply_le_norm0S (B.family.metric t) p 2 (B.family.ricciAt t p) (vec2 T T)
  have hprod : (∏ a : Fin 2, Real.sqrt ((B.family.metric t).inner p ((vec2 T T) a)
      ((vec2 T T) a))) = 1 := by
    rw [Fin.prod_univ_two]
    simp [vec2, hTT]
  rw [hprod, mul_one] at h1
  have hnorm : Real.sqrt (normSq0S (B.family.metric t) p 2 (B.family.ricciAt t p)) ≤ B.B₀ :=
    Real.sqrt_le_iff.mpr ⟨B.B₀_nonneg, B.ricci_bound t ht p⟩
  exact (le_abs_self _).trans (h1.trans hnorm)

omit [SigmaCompactSpace M] hBoundary in
theorem ricci_pair_ge (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) {p : M} (X : TangentSpace I p) :
    -(B.B₀ * (B.family.metric t).inner p X X) ≤ B.family.ricciAt t p (vec2 X X) := by
  have h1 := abs_apply_le_norm0S (B.family.metric t) p 2 (B.family.ricciAt t p) (vec2 X X)
  have hprod : (∏ a : Fin 2, Real.sqrt ((B.family.metric t).inner p ((vec2 X X) a)
      ((vec2 X X) a))) = (B.family.metric t).inner p X X := by
    rw [Fin.prod_univ_two]
    simp only [vec2, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    exact Real.mul_self_sqrt (DifferentialGeometry.metric_inner_self_nonneg (B.family.metric t) p X)
  rw [hprod] at h1
  have hnorm : Real.sqrt (normSq0S (B.family.metric t) p 2 (B.family.ricciAt t p)) ≤ B.B₀ :=
    Real.sqrt_le_iff.mpr ⟨B.B₀_nonneg, B.ricci_bound t ht p⟩
  exact (abs_le.mp (h1.trans (mul_le_mul_of_nonneg_right hnorm
    (DifferentialGeometry.metric_inner_self_nonneg (B.family.metric t) p X)))).1

omit [SigmaCompactSpace M] hBoundary in
theorem nablaRicci_vec3 (G : SolutionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (A V Z : TangentSpace I p) :
    nablaRicci G t p A V Z =
      (totalNabla0SFun 2 (G.connection t) (G.ricci t) p) (vec3 A V Z) := by
  change (totalNabla0SFun 2 (G.connection t) (G.ricci t) p) (Fin.cons A (vec2 V Z)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [SigmaCompactSpace M] hBoundary in
theorem nablaRicci_unit_le (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) {p : M} (T X : TangentSpace I p)
    (hTT : (B.family.metric t).inner p T T = 1) :
    |nablaRicci B.family t p T T X| ≤ B.B₂ * Real.sqrt ((B.family.metric t).inner p X X) := by
  rw [nablaRicci_vec3 B.family t p T T X]
  have h1 := abs_apply_le_norm0S (B.family.metric t) p 3
    (totalNabla0SFun 2 (B.family.connection t) (B.family.ricci t) p) (vec3 T T X)
  have hprod : (∏ a : Fin 3, Real.sqrt
      ((B.family.metric t).inner p ((vec3 T T X) a) ((vec3 T T X) a)))
      = Real.sqrt ((B.family.metric t).inner p X X) := by
    rw [Fin.prod_univ_three]
    simp [vec3, hTT]
  rw [hprod] at h1
  have hnorm : Real.sqrt (normSq0S (B.family.metric t) p 3
      (totalNabla0SFun 2 (B.family.connection t) (B.family.ricci t) p)) ≤ B.B₂ :=
    Real.sqrt_le_iff.mpr ⟨B.B₂_nonneg, B.nablaRicci_bound t ht p⟩
  exact h1.trans (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))

omit [SigmaCompactSpace M] hBoundary in
theorem nablaRicci_unit_right_le (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) {p : M} (T X : TangentSpace I p)
    (hTT : (B.family.metric t).inner p T T = 1) :
    |nablaRicci B.family t p X T T| ≤ B.B₂ * Real.sqrt ((B.family.metric t).inner p X X) := by
  rw [nablaRicci_vec3 B.family t p X T T]
  have h1 := abs_apply_le_norm0S (B.family.metric t) p 3
    (totalNabla0SFun 2 (B.family.connection t) (B.family.ricci t) p) (vec3 X T T)
  have hprod : (∏ a : Fin 3, Real.sqrt
      ((B.family.metric t).inner p ((vec3 X T T) a) ((vec3 X T T) a)))
      = Real.sqrt ((B.family.metric t).inner p X X) := by
    rw [Fin.prod_univ_three]
    simp [vec3, hTT]
  rw [hprod] at h1
  have hnorm : Real.sqrt (normSq0S (B.family.metric t) p 3
      (totalNabla0SFun 2 (B.family.connection t) (B.family.ricci t) p)) ≤ B.B₂ :=
    Real.sqrt_le_iff.mpr ⟨B.B₂_nonneg, B.nablaRicci_bound t ht p⟩
  exact h1.trans (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))


omit [SigmaCompactSpace M] hBoundary in
private theorem expDecay_antitone
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M)
    (x : ℝ) (A : ℝ)
    (hsp : ∀ τ, τ ∈ Icc s u → HasDerivWithinAt (c.speed B.family.metric x)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) (Icc s u) τ)
    (hA : ∀ τ ∈ Icc s u, -A ≤ c.q B.family x τ) :
    AntitoneOn (fun τ => c.speed B.family.metric x τ * Real.exp (-A * (τ - s))) (Icc s u) := by
  have hcont : ContinuousOn (fun τ => c.speed B.family.metric x τ * Real.exp (-A * (τ - s)))
      (Icc s u) := by
    apply ContinuousOn.mul
    · exact fun τ hτ => (hsp τ hτ).continuousWithinAt
    · exact Real.continuous_exp.comp_continuousOn
        ((continuousOn_id.sub continuousOn_const).const_mul (-A))
  refine antitoneOn_of_deriv_nonpos (convex_Icc s u) hcont ?_ ?_
  · intro τ hτ
    rw [interior_Icc] at hτ
    have h1 : HasDerivAt (fun τ => c.speed B.family.metric x τ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp τ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have h2 : HasDerivAt (fun τ => Real.exp (-A * (τ - s)))
        (Real.exp (-A * (τ - s)) * (-A)) τ := by
      have h3 : HasDerivAt (fun τ : ℝ => -A * (τ - s)) (-A) τ := by
        simpa using ((hasDerivAt_id τ).sub_const s).const_mul (-A)
      simpa using h3.exp
    exact ((h1.mul h2).differentiableAt).differentiableWithinAt
  · intro τ hτ
    rw [interior_Icc] at hτ
    have hτI : τ ∈ Icc s u := ⟨hτ.1.le, hτ.2.le⟩
    have h1 : HasDerivAt (fun τ => c.speed B.family.metric x τ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp τ hτI).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have h2 : HasDerivAt (fun τ => Real.exp (-A * (τ - s)))
        (Real.exp (-A * (τ - s)) * (-A)) τ := by
      have h3 : HasDerivAt (fun τ : ℝ => -A * (τ - s)) (-A) τ := by
        simpa using ((hasDerivAt_id τ).sub_const s).const_mul (-A)
      simpa using h3.exp
    have hdv : deriv ((fun τ => c.speed B.family.metric x τ) *
        fun τ => Real.exp (-A * (τ - s))) τ
        = (-(c.q B.family x τ) * c.speed B.family.metric x τ) * Real.exp (-A * (τ - s))
          + c.speed B.family.metric x τ * (Real.exp (-A * (τ - s)) * (-A)) :=
      (h1.mul h2).deriv
    have hsame : deriv (fun τ => c.speed B.family.metric x τ * Real.exp (-A * (τ - s))) τ
        = deriv ((fun τ => c.speed B.family.metric x τ) *
            fun τ => Real.exp (-A * (τ - s))) τ := by
      congr 1
    rw [hsame, hdv]
    have hvnn : 0 ≤ c.speed B.family.metric x τ := c.speed_nonneg B.family.metric x τ
    have hexp : 0 < Real.exp (-A * (τ - s)) := Real.exp_pos _
    have hq : -A ≤ c.q B.family x τ := hA τ hτI
    have hfac : (-(c.q B.family x τ) * c.speed B.family.metric x τ)
          * Real.exp (-A * (τ - s))
        + c.speed B.family.metric x τ * (Real.exp (-A * (τ - s)) * (-A))
        = -(Real.exp (-A * (τ - s)) *
            (c.speed B.family.metric x τ * (c.q B.family x τ + A))) := by ring
    rw [hfac]
    have hnn : 0 ≤ c.speed B.family.metric x τ * (c.q B.family x τ + A) :=
      mul_nonneg hvnn (by linarith)
    nlinarith [hexp, hnn]

omit [SigmaCompactSpace M] hBoundary in
private theorem expGrowth_monotone
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M)
    (x : ℝ) (A : ℝ)
    (hsp : ∀ τ, τ ∈ Icc s u → HasDerivWithinAt (c.speed B.family.metric x)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) (Icc s u) τ)
    (hA : ∀ τ ∈ Icc s u, c.q B.family x τ ≤ A) :
    MonotoneOn (fun τ => c.speed B.family.metric x τ * Real.exp (A * (τ - s))) (Icc s u) := by
  have hcont : ContinuousOn (fun τ => c.speed B.family.metric x τ * Real.exp (A * (τ - s)))
      (Icc s u) := by
    apply ContinuousOn.mul
    · exact fun τ hτ => (hsp τ hτ).continuousWithinAt
    · exact Real.continuous_exp.comp_continuousOn
        ((continuousOn_id.sub continuousOn_const).const_mul A)
  refine monotoneOn_of_deriv_nonneg (convex_Icc s u) hcont ?_ ?_
  · intro τ hτ
    rw [interior_Icc] at hτ
    have h1 : HasDerivAt (fun τ => c.speed B.family.metric x τ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp τ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have h2 : HasDerivAt (fun τ => Real.exp (A * (τ - s)))
        (Real.exp (A * (τ - s)) * A) τ := by
      have h3 : HasDerivAt (fun τ : ℝ => A * (τ - s)) A τ := by
        simpa using ((hasDerivAt_id τ).sub_const s).const_mul A
      simpa using h3.exp
    exact ((h1.mul h2).differentiableAt).differentiableWithinAt
  · intro τ hτ
    rw [interior_Icc] at hτ
    have hτI : τ ∈ Icc s u := ⟨hτ.1.le, hτ.2.le⟩
    have h1 : HasDerivAt (fun τ => c.speed B.family.metric x τ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp τ hτI).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have h2 : HasDerivAt (fun τ => Real.exp (A * (τ - s)))
        (Real.exp (A * (τ - s)) * A) τ := by
      have h3 : HasDerivAt (fun τ : ℝ => A * (τ - s)) A τ := by
        simpa using ((hasDerivAt_id τ).sub_const s).const_mul A
      simpa using h3.exp
    have hdv : deriv ((fun τ => c.speed B.family.metric x τ) *
        fun τ => Real.exp (A * (τ - s))) τ
        = (-(c.q B.family x τ) * c.speed B.family.metric x τ) * Real.exp (A * (τ - s))
          + c.speed B.family.metric x τ * (Real.exp (A * (τ - s)) * A) :=
      (h1.mul h2).deriv
    have hsame : deriv (fun τ => c.speed B.family.metric x τ * Real.exp (A * (τ - s))) τ
        = deriv ((fun τ => c.speed B.family.metric x τ) *
            fun τ => Real.exp (A * (τ - s))) τ := by
      congr 1
    rw [hsame, hdv]
    have hvnn : 0 ≤ c.speed B.family.metric x τ := c.speed_nonneg B.family.metric x τ
    have hexp : 0 < Real.exp (A * (τ - s)) := Real.exp_pos _
    have hq : c.q B.family x τ ≤ A := hA τ hτI
    have hfac : (-(c.q B.family x τ) * c.speed B.family.metric x τ)
          * Real.exp (A * (τ - s))
        + c.speed B.family.metric x τ * (Real.exp (A * (τ - s)) * A)
        = Real.exp (A * (τ - s)) *
            (c.speed B.family.metric x τ * (A - c.q B.family x τ)) := by ring
    rw [hfac]
    have hnn : 0 ≤ c.speed B.family.metric x τ * (A - c.q B.family x τ) :=
      mul_nonneg hvnn (by linarith)
    nlinarith [hexp, hnn]

private theorem q_lower_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x τ : ℝ) (hτ : τ ∈ Icc s u) :
    -B.B₀ ≤ c.q B.family x τ := by
  have htt : (B.family.metric τ).inner (c.lift x τ) (c.unitTangent B.family.metric x τ)
      (c.unitTangent B.family.metric x τ) = 1 :=
    (tangent_curvature_geometry B.family.metric c (Icc s u) hc.smooth hc.immersed x τ hτ).1
  have h1 : -B.B₀ ≤ c.ricciTangent B.family x τ := by
    have h := ricci_pair_ge B τ (hwindow hτ) (c.unitTangent B.family.metric x τ)
    rw [htt, mul_one] at h
    exact h
  have h2 : 0 ≤ c.curvatureSq B.family.metric x τ := by
    rw [← CurveMap.curvature_sq c B.family.metric x τ]
    exact sq_nonneg _
  have hq : c.q B.family x τ =
      c.curvatureSq B.family.metric x τ + c.ricciTangent B.family x τ := rfl
  rw [hq]
  linarith

private theorem q_upper_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (K : ℝ)
    (hcurv : ∀ x t, t ∈ Icc s u → c.curvature B.family.metric x t ≤ K)
    (x τ : ℝ) (hτ : τ ∈ Icc s u) :
    c.q B.family x τ ≤ K ^ 2 + B.B₀ := by
  have htt : (B.family.metric τ).inner (c.lift x τ) (c.unitTangent B.family.metric x τ)
      (c.unitTangent B.family.metric x τ) = 1 :=
    (tangent_curvature_geometry B.family.metric c (Icc s u) hc.smooth hc.immersed x τ hτ).1
  have h1 : c.ricciTangent B.family x τ ≤ B.B₀ :=
    ricci_unit_le B τ (hwindow hτ) (c.unitTangent B.family.metric x τ) htt
  have h2 : c.curvatureSq B.family.metric x τ ≤ K ^ 2 := by
    rw [← CurveMap.curvature_sq c B.family.metric x τ]
    exact pow_le_pow_left₀ (c.curvature_nonneg B.family.metric x τ) (hcurv x τ hτ) 2
  have hq : c.q B.family x τ =
      c.curvatureSq B.family.metric x τ + c.ricciTangent B.family x τ := rfl
  rw [hq]
  linarith

def CurveMap.SpeedEvolution (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) : Prop :=
  ∀ x t, t ∈ Icc s u → HasDerivWithinAt (c.speed B.family.metric x)
    (-(c.q B.family x t) * c.speed B.family.metric x t) (Icc s u) t

omit [SigmaCompactSpace M] hBoundary in
theorem CurveMap.speedEvolution_of_pairingEvolution
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) (hi : c.ImmersedOn (I := I) (Icc s u))
    (hpair : CurveMap.PairingEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c) :
    CurveMap.SpeedEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c := by
  intro x t ht
  have hsq : HasDerivWithinAt (fun r => c.speed B.family.metric x r ^ 2)
      (-2 * c.speed B.family.metric x t ^ 2 * c.q B.family x t) (Icc s u) t := by
    convert hpair x t ht using 1
    · funext r
      exact (normSq_velocity_eq_speed_sq c B.family.metric x r).symm
    · rw [normSq_velocity_eq_speed_sq]
  have h := hsq.sqrt (pow_ne_zero 2 (ne_of_gt (c.speed_pos B.family.metric hi x t ht)))
  convert h using 1
  · funext r
    exact (Real.sqrt_sq (c.speed_nonneg B.family.metric x r)).symm
  · rw [Real.sqrt_sq (c.speed_nonneg B.family.metric x t)]
    field_simp

theorem speed_exponential_bounds (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (K : ℝ)
    (hcurv : ∀ x t, t ∈ Icc s u → c.curvature B.family.metric x t ≤ K)
    (hsp : CurveMap.SpeedEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c)
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)) ≤
      c.speed B.family.metric x t ∧
    c.speed B.family.metric x t ≤
      c.speed B.family.metric x s * Real.exp (B.B₀ * (t - s)) := by
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  constructor
  · have hmono := expGrowth_monotone B c x (K ^ 2 + B.B₀) (fun τ hτ => hsp x τ hτ)
      (fun τ hτ => q_upper_bound B hwindow c hc K hcurv x τ hτ)
    have h0 : c.speed B.family.metric x s ≤
        c.speed B.family.metric x t * Real.exp ((K ^ 2 + B.B₀) * (t - s)) := by
      have h := hmono hs ht ht.1
      simpa using h
    have hmul := mul_le_mul_of_nonneg_right h0
      (Real.exp_nonneg (-(K ^ 2 + B.B₀) * (t - s)))
    have hkey : Real.exp ((K ^ 2 + B.B₀) * (t - s)) *
        Real.exp (-(K ^ 2 + B.B₀) * (t - s)) = 1 := by
      rw [← Real.exp_add, Real.exp_eq_one_iff]
      ring
    rw [mul_assoc, hkey, mul_one] at hmul
    exact hmul
  · have hanti := expDecay_antitone B c x B.B₀ (fun τ hτ => hsp x τ hτ)
      (fun τ hτ => by simpa using q_lower_bound B hwindow c hc x τ hτ)
    have h0 : c.speed B.family.metric x t * Real.exp (-B.B₀ * (t - s)) ≤
        c.speed B.family.metric x s := by
      have h := hanti hs ht ht.1
      simpa using h
    have hmul := mul_le_mul_of_nonneg_right h0 (Real.exp_nonneg (B.B₀ * (t - s)))
    have hkey : Real.exp (-B.B₀ * (t - s)) * Real.exp (B.B₀ * (t - s)) = 1 := by
      rw [← Real.exp_add, Real.exp_eq_one_iff]
      ring
    rw [mul_assoc, hkey, mul_one] at hmul
    exact hmul

theorem curvature_evolution_le_of_rfs_csf_curvature
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.curvatureSq B.family.metric x) (Icc s u) t ≤
      c.ds B.family.metric (c.ds B.family.metric (c.curvatureSq B.family.metric)) x t -
      2 * c.normSq B.family.metric (c.normalCurvatureDerivative B.family.metric) x t +
      2 * c.curvatureSq B.family.metric x t ^ 2 +
      2 * B.C * (c.curvatureSq B.family.metric x t + c.curvature B.family.metric x t) := by
  have hmain := rfs_csf_curvature B hsu hwindow c hc x t ht
  have htt : (B.family.metric t).inner (c.lift x t)
      (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t) = 1 :=
    (tangent_curvature_geometry B.family.metric c (Icc s u) hc.smooth hc.immersed x t ht).1
  have hk2 : 0 ≤ c.curvatureSq B.family.metric x t :=
    c.normSq_nonneg B.family.metric (c.curvatureVector B.family.metric) x t
  have hk : 0 ≤ c.curvature B.family.metric x t := c.curvature_nonneg B.family.metric x t
  have hRic1 : c.ricciTangent B.family x t ≤ B.B₀ :=
    ricci_unit_le B t (hwindow ht) (c.unitTangent B.family.metric x t) htt
  have hRic2 : -(B.B₀ * c.curvatureSq B.family.metric x t) ≤
      B.family.ricciAt t (c.lift x t)
        (vec2 (c.curvatureVector B.family.metric x t) (c.curvatureVector B.family.metric x t)) :=
    ricci_pair_ge B t (hwindow ht) (c.curvatureVector B.family.metric x t)
  have hRi : (B.family.metric t).inner (c.lift x t)
      (riemannVector B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t))
      (c.curvatureVector B.family.metric x t) ≤ B.B₁ * c.curvatureSq B.family.metric x t := by
    rw [riemann_pair_eq_rm04 B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
      (c.unitTangent B.family.metric x t)]
    exact rm04_unit_le B t (hwindow ht) (c.curvatureVector B.family.metric x t)
      (c.unitTangent B.family.metric x t) htt
  have hN1 : -(B.B₂ * c.curvature B.family.metric x t) ≤
      nablaRicci B.family t (c.lift x t) (c.unitTangent B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.curvatureVector B.family.metric x t) :=
    (abs_le.mp (nablaRicci_unit_le B t (hwindow ht) (c.unitTangent B.family.metric x t)
      (c.curvatureVector B.family.metric x t) htt)).1
  have hN2 : nablaRicci B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
      (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t) ≤
      B.B₂ * c.curvature B.family.metric x t :=
    (abs_le.mp (nablaRicci_unit_right_le B t (hwindow ht) (c.unitTangent B.family.metric x t)
      (c.curvatureVector B.family.metric x t) htt)).2
  have hb1 : 4 * c.curvatureSq B.family.metric x t * c.ricciTangent B.family x t ≤
      4 * B.B₀ * c.curvatureSq B.family.metric x t := by
    have h := mul_le_mul_of_nonneg_left hRic1 (show (0:ℝ) ≤ 4 * c.curvatureSq B.family.metric x t by positivity)
    linarith [h]
  have hb2 : -(2 * B.family.ricciAt t (c.lift x t)
        (vec2 (c.curvatureVector B.family.metric x t) (c.curvatureVector B.family.metric x t))) ≤
      2 * B.B₀ * c.curvatureSq B.family.metric x t := by
    linarith [hRic2]
  have hb3 : 2 * (B.family.metric t).inner (c.lift x t)
      (riemannVector B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t))
      (c.curvatureVector B.family.metric x t) ≤ 2 * B.B₁ * c.curvatureSq B.family.metric x t := by
    linarith [hRi]
  have hb4 : -(4 * nablaRicci B.family t (c.lift x t) (c.unitTangent B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.curvatureVector B.family.metric x t)) ≤
      4 * B.B₂ * c.curvature B.family.metric x t := by
    linarith [hN1]
  have hb5 : 2 * nablaRicci B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
      (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t) ≤
      2 * B.B₂ * c.curvature B.family.metric x t := by
    linarith [hN2]
  have hbound : 4 * c.curvatureSq B.family.metric x t * c.ricciTangent B.family x t -
      2 * B.family.ricciAt t (c.lift x t)
        (vec2 (c.curvatureVector B.family.metric x t) (c.curvatureVector B.family.metric x t)) +
      2 * (B.family.metric t).inner (c.lift x t)
        (riemannVector B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
          (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t))
        (c.curvatureVector B.family.metric x t) -
      4 * nablaRicci B.family t (c.lift x t) (c.unitTangent B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.curvatureVector B.family.metric x t) +
      2 * nablaRicci B.family t (c.lift x t) (c.curvatureVector B.family.metric x t)
        (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t) ≤
      2 * B.C * (c.curvatureSq B.family.metric x t + c.curvature B.family.metric x t) := by
    rw [RicciBackground.C]
    nlinarith [hb1, hb2, hb3, hb4, hb5, hk2, hk, B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  rw [hmain]
  linarith [hbound]

theorem curvature_evolution_le (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.curvatureSq B.family.metric x) (Icc s u) t ≤
      c.ds B.family.metric (c.ds B.family.metric (c.curvatureSq B.family.metric)) x t -
      2 * c.normSq B.family.metric (c.normalCurvatureDerivative B.family.metric) x t +
      2 * c.curvatureSq B.family.metric x t ^ 2 +
      2 * B.C * (c.curvatureSq B.family.metric x t + c.curvature B.family.metric x t) :=
  curvature_evolution_le_of_rfs_csf_curvature B hsu hwindow c hc x t ht


theorem rfs_csf_regularized_curvature (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (ε : ℝ) (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.regularizedCurvature B.family.metric ε p.1 p.2)
      (univ ×ˢ Icc s u) ∧
    (∀ x t, t ∈ Icc s u →
      0 ≤ c.regularizedCurvature B.family.metric ε x t - c.curvature B.family.metric x t ∧
      c.regularizedCurvature B.family.metric ε x t - c.curvature B.family.metric x t ≤ ε) ∧
    (∀ x t, t ∈ Icc s u →
      derivWithin (c.regularizedCurvature B.family.metric ε x) (Icc s u) t ≤
        c.ds B.family.metric (c.ds B.family.metric (c.regularizedCurvature B.family.metric ε)) x t +
        c.curvatureSq B.family.metric x t * c.regularizedCurvature B.family.metric ε x t +
        B.C * (c.regularizedCurvature B.family.metric ε x t + 1)) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
