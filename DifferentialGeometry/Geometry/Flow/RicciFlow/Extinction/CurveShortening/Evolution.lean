import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Constructions.SumProd

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
  have hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c J hc t ht)
  have hT := CurveMap.unitTangent_contMDiff g c J hc hi t ht
  have hH := CurveMap.curvatureVector_contMDiff g c J hc hi t ht
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

theorem CurveMap.pairingEvolution {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    CurveMap.PairingEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c := by
  intro x t ht
  have hX : CurveMap.Field.SmoothOn (I := I) (c.X) (Icc s u) :=
    CurveMap.Field.smoothOn_X c (Icc s u) hc.smooth
  have hmov := hasDerivWithinAt_moving_inner B hsu hwindow c hc.smooth (c.X) (c.X) hX hX x t ht
  have hmov' : HasDerivWithinAt (fun r => c.normSq B.family.metric (c.X) x r)
      (-2 * B.family.ricciAt t (c.lift x t) (vec2 (c.X x t) (c.X x t)) +
        ((B.family.metric t).inner (c.lift x t)
          (c.Dt B.family.metric (Icc s u) (c.X) x t) (c.X x t) +
        (B.family.metric t).inner (c.lift x t) (c.X x t)
          (c.Dt B.family.metric (Icc s u) (c.X) x t)))
      (Icc s u) t := hmov
  have hdtx : c.Dt B.family.metric (Icc s u) (c.X) x t =
      c.Dx B.family.metric (c.curvatureVector B.family.metric) x t := by
    rw [pullback_torsion_free B.toSmoothMetricWindow hsu hwindow c hc.smooth x t ht]
    simp only [CurveMap.Dx]
    congr 1
    funext y
    exact hc.equation y t ht
  have hspeed : 0 < c.speed B.family.metric x t :=
    c.speed_pos B.family.metric hc.immersed x t ht
  have hXs : c.X x t = c.speed B.family.metric x t • c.unitTangent B.family.metric x t := by
    rw [CurveMap.unitTangent, smul_smul, mul_inv_cancel₀ (ne_of_gt hspeed), one_smul]
  have hDxH : c.Dx B.family.metric (c.curvatureVector B.family.metric) x t =
      c.speed B.family.metric x t •
        c.Ds B.family.metric (c.curvatureVector B.family.metric) x t := by
    rw [CurveMap.Ds, smul_smul, mul_inv_cancel₀ (ne_of_gt hspeed), one_smul]
  have hgeom : (B.family.metric t).inner (c.lift x t)
      (c.Ds B.family.metric (c.curvatureVector B.family.metric) x t)
      (c.unitTangent B.family.metric x t) = -c.curvatureSq B.family.metric x t :=
    (tangent_curvature_geometry B.family.metric c (Icc s u) hc.smooth hc.immersed x t ht).2.2
  have hcross : (B.family.metric t).inner (c.lift x t)
      (c.Dx B.family.metric (c.curvatureVector B.family.metric) x t) (c.X x t) =
      -(c.speed B.family.metric x t ^ 2 * c.curvatureSq B.family.metric x t) := by
    rw [hDxH, hXs]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hgeom]
    ring
  have hric : B.family.ricciAt t (c.lift x t) (vec2 (c.X x t) (c.X x t)) =
      c.speed B.family.metric x t ^ 2 * c.ricciTangent B.family x t := by
    have hvec : vec2 (c.X x t) (c.X x t) =
        fun i : Fin 2 => c.speed B.family.metric x t •
          vec2 (c.unitTangent B.family.metric x t)
            (c.unitTangent B.family.metric x t) i := by
      funext i
      fin_cases i <;> simp [vec2, hXs]
    rw [hvec, CurveMap.ricciTangent]
    rw [(B.family.ricciAt t (c.lift x t)).map_smul_univ
      (fun _ : Fin 2 => c.speed B.family.metric x t)
      (vec2 (c.unitTangent B.family.metric x t) (c.unitTangent B.family.metric x t))]
    simp only [Fin.prod_univ_two, smul_eq_mul]
    ring
  have hval : -2 * B.family.ricciAt t (c.lift x t) (vec2 (c.X x t) (c.X x t)) +
      ((B.family.metric t).inner (c.lift x t)
          (c.Dx B.family.metric (c.curvatureVector B.family.metric) x t) (c.X x t) +
        (B.family.metric t).inner (c.lift x t) (c.X x t)
          (c.Dx B.family.metric (c.curvatureVector B.family.metric) x t)) =
      -2 * c.normSq B.family.metric (c.X) x t * c.q B.family x t := by
    have hsymm := (B.family.metric t).symm (c.lift x t) (c.X x t)
      (c.Dx B.family.metric (c.curvatureVector B.family.metric) x t)
    rw [hric, hsymm, hcross, normSq_velocity_eq_speed_sq]
    simp only [CurveMap.q, pow_two]
    ring
  rw [hdtx] at hmov'
  rw [hval] at hmov'
  exact hmov'

theorem rfs_csf_speed (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.speed B.family.metric x) (Icc s u) t =
      -c.q B.family x t * c.speed B.family.metric x t ∧
    c.Dt B.family.metric (Icc s u) (c.unitTangent B.family.metric) x t =
      c.Ds B.family.metric (c.curvatureVector B.family.metric) x t +
        c.q B.family x t • c.unitTangent B.family.metric x t := by
  have hX : CurveMap.Field.SmoothOn (I := I) (c.X) (Icc s u) :=
    CurveMap.Field.smoothOn_X c (Icc s u) hc.smooth
  have hpair : CurveMap.PairingEvolution (I := I) (D := D) (a := a) (b := b)
      (s := s) (u := u) B c :=
    CurveMap.pairingEvolution B hsu hwindow c hc
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


omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem fderivWithin_strip_inl {a b : ℝ} (Φ : ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ Icc a b)
    (h : DifferentiableWithinAt ℝ Φ (univ ×ˢ Icc a b) p) :
    fderivWithin ℝ Φ (univ ×ˢ Icc a b) p (1, 0) = deriv (fun y => Φ (y, p.2)) p.1 := by
  have hι : HasFDerivWithinAt (fun y : ℝ => (y, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ)
      univ p.1 :=
    (hasFDerivAt_prodMk_left p.1 p.2).hasFDerivWithinAt
  have hmap : MapsTo (fun y : ℝ => (y, p.2)) univ (univ ×ˢ Icc a b) := fun y _ => hp
  have hcomp := (h.hasFDerivWithinAt).comp p.1 hι hmap
  have hderiv : HasDerivAt (fun y : ℝ => Φ (y, p.2))
      ((fderivWithin ℝ Φ (univ ×ˢ Icc a b) p ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ) 1) p.1 :=
    (hcomp.hasFDerivAt univ_mem).hasDerivAt
  rw [hderiv.deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem fderivWithin_strip_inr {a b : ℝ} (Φ : ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ Icc a b) (hab : a < b)
    (h : DifferentiableWithinAt ℝ Φ (univ ×ˢ Icc a b) p) :
    fderivWithin ℝ Φ (univ ×ˢ Icc a b) p (0, 1) =
      derivWithin (fun r => Φ (p.1, r)) (Icc a b) p.2 := by
  have hι : HasFDerivWithinAt (fun r : ℝ => (p.1, r)) (ContinuousLinearMap.inr ℝ ℝ ℝ)
      (Icc a b) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).hasFDerivWithinAt
  have hmap : MapsTo (fun r : ℝ => (p.1, r)) (Icc a b) (univ ×ˢ Icc a b) :=
    fun r hr => ⟨trivial, hr⟩
  have hcomp := (h.hasFDerivWithinAt).comp p.2 hι hmap
  have hderiv : HasDerivWithinAt (fun r : ℝ => Φ (p.1, r))
      ((fderivWithin ℝ Φ (univ ×ˢ Icc a b) p ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ) 1)
      (Icc a b) p.2 :=
    hcomp.hasDerivWithinAt
  have huniq : UniqueDiffWithinAt ℝ (Icc a b) p.2 := (uniqueDiffOn_Icc hab) p.2 hp.2
  rw [hderiv.derivWithin huniq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem derivWithin_deriv_eq_deriv_derivWithin {a b : ℝ} (F : ℝ × ℝ → ℝ) (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Icc a b)) {x t : ℝ} (ht : t ∈ Icc a b) :
    derivWithin (fun r => deriv (fun y => F (y, r)) x) (Icc a b) t =
      deriv (fun y => derivWithin (fun r => F (y, r)) (Icc a b) t) x := by
  have hSunique : UniqueDiffOn ℝ (univ ×ˢ Icc a b) :=
    UniqueDiffOn.prod (𝕜 := ℝ) (s := (univ : Set ℝ)) (t := Icc a b)
    uniqueDiffOn_univ (uniqueDiffOn_Icc hab)
  have hmem : (x, t) ∈ univ ×ˢ Icc a b := ⟨mem_univ x, ht⟩
  have hclos : (x, t) ∈ closure (interior (univ ×ˢ Icc a b)) := by
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq, closure_univ,
      closure_Ioo (ne_of_lt hab)]
    exact ⟨mem_univ x, ht⟩
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) :
      ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))
  have hsymm := (hF (x, t) hmem).isSymmSndFDerivWithinAt hmin hSunique hclos hmem
  have htwo : (1 : ℕ∞ω) + 1 ≤ ∞ := by
    have hone : (1 : ℕ∞ω) + 1 = (2 : ℕ∞ω) := by norm_num
    rw [hone]
    exact WithTop.coe_le_coe.mpr le_top
  have hcont1 : ContDiffWithinAt ℝ (1 : ℕ∞ω) (fderivWithin ℝ F (univ ×ˢ Icc a b))
      (univ ×ˢ Icc a b) (x, t) :=
    (hF (x, t) hmem).fderivWithin_right hSunique htwo hmem
  have hdiff : DifferentiableWithinAt ℝ (fderivWithin ℝ F (univ ×ˢ Icc a b))
      (univ ×ˢ Icc a b) (x, t) := hcont1.differentiableWithinAt (by norm_num)
  have hd1 : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (0, 1))
      (univ ×ˢ Icc a b) (x, t) :=
    hdiff.clm_apply (differentiableWithinAt_const (0, 1))
  have hd0 : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (1, 0))
      (univ ×ˢ Icc a b) (x, t) :=
    hdiff.clm_apply (differentiableWithinAt_const (1, 0))
  have hident1 : fderivWithin ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (0, 1))
      (univ ×ˢ Icc a b) (x, t) (1, 0) =
      fderivWithin ℝ (fderivWithin ℝ F (univ ×ˢ Icc a b)) (univ ×ˢ Icc a b) (x, t)
        (1, 0) (0, 1) := by
    rw [fderivWithin_clm_apply (hSunique (x, t) hmem)
      hdiff (differentiableWithinAt_const (0, 1))]
    simp
  have hident0 : fderivWithin ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (1, 0))
      (univ ×ˢ Icc a b) (x, t) (0, 1) =
      fderivWithin ℝ (fderivWithin ℝ F (univ ×ˢ Icc a b)) (univ ×ˢ Icc a b) (x, t)
        (0, 1) (1, 0) := by
    rw [fderivWithin_clm_apply (hSunique (x, t) hmem)
      hdiff (differentiableWithinAt_const (1, 0))]
    simp
  have hA : fderivWithin ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (1, 0))
      (univ ×ˢ Icc a b) (x, t) (0, 1) =
      derivWithin (fun r => deriv (fun y => F (y, r)) x) (Icc a b) t := by
    rw [fderivWithin_strip_inr
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (1, 0)) hmem hab hd0]
    exact derivWithin_congr (fun r hr =>
      fderivWithin_strip_inl F ⟨mem_univ x, hr⟩
        ((hF (x, r) ⟨mem_univ x, hr⟩).differentiableWithinAt (by norm_num)))
      (fderivWithin_strip_inl F ⟨mem_univ x, ht⟩
        ((hF (x, t) hmem).differentiableWithinAt (by norm_num)))
  have hB : fderivWithin ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (0, 1))
      (univ ×ˢ Icc a b) (x, t) (1, 0) =
      deriv (fun y => derivWithin (fun r => F (y, r)) (Icc a b) t) x := by
    rw [fderivWithin_strip_inl
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (0, 1)) hmem hd1]
    exact Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall fun y =>
      fderivWithin_strip_inr F ⟨mem_univ y, ht⟩ hab
        ((hF (y, t) ⟨mem_univ y, ht⟩).differentiableWithinAt (by norm_num)))
  rw [← hA, ← hB, hident0, hident1]
  exact hsymm (0, 1) (1, 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem hasDerivWithinAt_deriv_strip {a b : ℝ} (F : ℝ × ℝ → ℝ) (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Icc a b)) {x t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => deriv (fun y => F (y, r)) x)
      (deriv (fun y => derivWithin (fun r => F (y, r)) (Icc a b) t) x) (Icc a b) t := by
  have hval := derivWithin_deriv_eq_deriv_derivWithin F hab hF (x := x) ht
  have hSunique : UniqueDiffOn ℝ (univ ×ˢ Icc a b) :=
    UniqueDiffOn.prod (𝕜 := ℝ) (s := (univ : Set ℝ)) (t := Icc a b)
    uniqueDiffOn_univ (uniqueDiffOn_Icc hab)
  have hmem : (x, t) ∈ univ ×ˢ Icc a b := ⟨mem_univ x, ht⟩
  have htwo : (1 : ℕ∞ω) + 1 ≤ ∞ := by
    have hone : (1 : ℕ∞ω) + 1 = (2 : ℕ∞ω) := by norm_num
    rw [hone]
    exact WithTop.coe_le_coe.mpr le_top
  have hcont1 : ContDiffWithinAt ℝ (1 : ℕ∞ω) (fderivWithin ℝ F (univ ×ˢ Icc a b))
      (univ ×ˢ Icc a b) (x, t) :=
    (hF (x, t) hmem).fderivWithin_right hSunique htwo hmem
  have hdiff : DifferentiableWithinAt ℝ (fderivWithin ℝ F (univ ×ˢ Icc a b))
      (univ ×ˢ Icc a b) (x, t) := hcont1.differentiableWithinAt (by norm_num)
  have hd1 : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) q (1, 0))
      (univ ×ˢ Icc a b) (x, t) :=
    hdiff.clm_apply (differentiableWithinAt_const (1, 0))
  have hinner : DifferentiableWithinAt ℝ (fun r : ℝ => (x, r)) (Icc a b) t :=
    (differentiableWithinAt_const x).prodMk differentiableWithinAt_id
  have hmap : MapsTo (fun r : ℝ => (x, r)) (Icc a b) (univ ×ˢ Icc a b) :=
    fun r hr => ⟨trivial, hr⟩
  have hline : DifferentiableWithinAt ℝ
      (fun r : ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) (x, r) (1, 0)) (Icc a b) t :=
    hd1.comp t hinner hmap
  have hon : EqOn (fun r : ℝ => fderivWithin ℝ F (univ ×ˢ Icc a b) (x, r) (1, 0))
      (fun r => deriv (fun y => F (y, r)) x) (Icc a b) :=
    fun r hr => fderivWithin_strip_inl F ⟨mem_univ x, hr⟩
      ((hF (x, r) ⟨mem_univ x, hr⟩).differentiableWithinAt (by norm_num))
  rw [← hval]
  exact (hline.congr hon.symm (hon ht).symm).hasDerivWithinAt


theorem scalar_arclength_commutator (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (f : ℝ → ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.ds B.family.metric f x) (Icc s u) t -
      c.ds B.family.metric (fun y r => derivWithin (f y) (Icc s u) r) x t =
    c.q B.family x t * c.ds B.family.metric f x t := by
  have hds : c.ds B.family.metric f x =
      fun r => (c.speed B.family.metric x r)⁻¹ * deriv (fun y => f y r) x := rfl
  rw [hds]
  simp only [CurveMap.ds]
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) t := (uniqueDiffOn_Icc hsu) t ht
  have hvpos : 0 < c.speed B.family.metric x t :=
    c.speed_pos B.family.metric hc.immersed x t ht
  have hvnn : 0 ≤ c.speed B.family.metric x t := hvpos.le
  have hspeed : HasDerivWithinAt (c.speed B.family.metric x)
      (-c.q B.family x t * c.speed B.family.metric x t) (Icc s u) t := by
    have hpair := CurveMap.pairingEvolution B hsu hwindow c hc
    have hsq : HasDerivWithinAt (fun r => c.speed B.family.metric x r ^ 2)
        (-2 * c.speed B.family.metric x t ^ 2 * c.q B.family x t) (Icc s u) t := by
      convert hpair x t ht using 1
      · funext r
        exact (normSq_velocity_eq_speed_sq c B.family.metric x r).symm
      · rw [normSq_velocity_eq_speed_sq]
    have h := hsq.sqrt (by positivity)
    convert h using 1
    · funext r
      exact (Real.sqrt_sq (c.speed_nonneg B.family.metric x r)).symm
    · rw [Real.sqrt_sq hvnn]
      field_simp
  have hinv : HasDerivWithinAt (fun r => (c.speed B.family.metric x r)⁻¹)
      (-(-c.q B.family x t * c.speed B.family.metric x t) /
        (c.speed B.family.metric x t) ^ 2) (Icc s u) t :=
    hspeed.inv (ne_of_gt hvpos)
  have hgd : HasDerivWithinAt (fun r => deriv (fun y => f y r) x)
      (deriv (fun y => derivWithin (f y) (Icc s u) t) x) (Icc s u) t :=
    hasDerivWithinAt_deriv_strip (fun p : ℝ × ℝ => f p.1 p.2) hsu hf ht
  have hmul := hinv.mul hgd
  have hmul' : HasDerivWithinAt
      (fun r => (c.speed B.family.metric x r)⁻¹ * deriv (fun y => f y r) x)
      ((-(-c.q B.family x t * c.speed B.family.metric x t) /
          (c.speed B.family.metric x t) ^ 2) * deriv (fun y => f y t) x +
        (c.speed B.family.metric x t)⁻¹ *
          deriv (fun y => derivWithin (f y) (Icc s u) t) x) (Icc s u) t := hmul
  rw [hmul'.derivWithin huniq]
  field_simp [ne_of_gt hvpos]
  ring_nf

omit [SigmaCompactSpace M] in
theorem CurveMap.derivWithin_curvatureSq (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (fun r => c.curvatureSq B.family.metric x r) (Icc s u) t =
      2 * (B.family.metric t).inner (c.lift x t)
          (c.Dt B.family.metric (Icc s u) (c.curvatureVector B.family.metric) x t)
          (c.curvatureVector B.family.metric x t) -
      2 * B.family.ricciAt t (c.lift x t)
          (vec2 (c.curvatureVector B.family.metric x t)
            (c.curvatureVector B.family.metric x t)) := by
  have hk : CurveMap.Field.SmoothOn (I := I) (c.curvatureVector B.family.metric) (Icc s u) :=
    CurveMap.Field.smoothOn_curvatureVector B.family.metric B.smooth
      (fun r hr => B.regular (hwindow hr)) (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have h := moving_inner_derivative B hsu hwindow c hc.smooth
    (c.curvatureVector B.family.metric) (c.curvatureVector B.family.metric) hk hk x t ht
  have hsymm := (B.family.metric t).symm (c.lift x t)
    (c.Dt B.family.metric (Icc s u) (c.curvatureVector B.family.metric) x t)
    (c.curvatureVector B.family.metric x t)
  simp only [CurveMap.curvatureSq, CurveMap.normSq]
  rw [h, hsymm]
  ring

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
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)) ≤
      c.speed B.family.metric x t ∧
    c.speed B.family.metric x t ≤
      c.speed B.family.metric x s * Real.exp (B.B₀ * (t - s)) := by
  have hsp : CurveMap.SpeedEvolution (I := I) (D := D) (a := a) (b := b) (s := s) (u := u) B c :=
    CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
      (CurveMap.pairingEvolution B hsu hwindow c hc)
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

omit [CompleteSpace E] in
theorem CurveMap.inner_normalCurvatureDerivative_curvatureVector_sq
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.normalCurvatureDerivative g x t) (c.curvatureVector g x t) =
      (1 / 2) * c.ds g (c.curvatureSq g) x t := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y : ℝ => c.lift y t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c J hc t ht)
  have hVc := CurveMap.curvatureVector_contMDiff g c J hc hi t ht
  have hd := metric_compat_hasDerivAt_inner (by simp : (1 : WithTop ℕ∞) ≤ ∞)
    (g t) (fun y : ℝ => c.lift y t) (fun y => c.curvatureVector g y t)
    (fun y => c.curvatureVector g y t) x hγ
    (chartRep_diff (I := I) (fun y : ℝ => c.lift y t)
      (fun y => c.curvatureVector g y t) hVc x)
    (chartRep_diff (I := I) (fun y : ℝ => c.lift y t)
      (fun y => c.curvatureVector g y t) hVc x)
  have hsymm : (g t).inner (c.lift x t) (c.curvatureVector g x t)
      (covDerivAlong (g t) (fun y : ℝ => c.lift y t) (fun y => c.curvatureVector g y t) x) =
      (g t).inner (c.lift x t)
      (covDerivAlong (g t) (fun y : ℝ => c.lift y t) (fun y => c.curvatureVector g y t) x)
      (c.curvatureVector g x t) :=
    (g t).symm (c.lift x t) (c.curvatureVector g x t)
      (covDerivAlong (g t) (fun y : ℝ => c.lift y t) (fun y => c.curvatureVector g y t) x)
  have hfun : (fun y : ℝ => c.curvatureSq g y t) =
      (fun y : ℝ => (g t).inner (c.lift y t) (c.curvatureVector g y t)
        (c.curvatureVector g y t)) := rfl
  have hderiv : deriv (fun y : ℝ => c.curvatureSq g y t) x =
      2 * (g t).inner (c.lift x t) (c.Dx g (c.curvatureVector g) x t)
        (c.curvatureVector g x t) := by
    rw [hfun, hd.deriv, hsymm]
    simp only [CurveMap.Dx]
    ring
  have hgeom := tangent_curvature_geometry g c J hc hi x t ht
  have horth : (g t).inner (c.lift x t) (c.curvatureVector g x t) (c.unitTangent g x t) = 0 :=
    hgeom.2.1
  have hspos : 0 < c.speed g x t := c.speed_pos g hi x t ht
  have hds : c.ds g (c.curvatureSq g) x t =
      (c.speed g x t)⁻¹ * deriv (fun y : ℝ => c.curvatureSq g y t) x := rfl
  have hDs : c.Ds g (c.curvatureVector g) x t =
      (c.speed g x t)⁻¹ • c.Dx g (c.curvatureVector g) x t := rfl
  have hN : c.normalCurvatureDerivative g x t =
      c.Ds g (c.curvatureVector g) x t + c.curvatureSq g x t • c.unitTangent g x t := rfl
  rw [hN, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    (g t).symm (c.lift x t) (c.unitTangent g x t) (c.curvatureVector g x t),
    horth, mul_zero, add_zero]
  rw [hDs, map_smul, smul_apply, smul_eq_mul]
  rw [hds, hderiv]
  field_simp

omit [CompleteSpace E] in
theorem CurveMap.ds_curvatureSq_sq_le_mul_normSq_normalCurvatureDerivative
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (c.ds g (c.curvatureSq g) x t) ^ 2 ≤
      4 * c.curvatureSq g x t * c.normSq g (c.normalCurvatureDerivative g) x t := by
  have hkey := CurveMap.inner_normalCurvatureDerivative_curvatureVector_sq g c J hc hi x t ht
  have hcs := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
    (I := I) (M := M) (g t) (c.lift x t)
    (c.normalCurvatureDerivative g x t) (c.curvatureVector g x t)
  have hnn : c.normSq g (c.normalCurvatureDerivative g) x t =
      (g t).inner (c.lift x t) (c.normalCurvatureDerivative g x t)
        (c.normalCurvatureDerivative g x t) := rfl
  have hkk : c.curvatureSq g x t =
      (g t).inner (c.lift x t) (c.curvatureVector g x t) (c.curvatureVector g x t) := rfl
  rw [hkey] at hcs
  rw [← hnn, ← hkk] at hcs
  nlinarith [hcs]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem CurveMap.ds_regularizedCurvature (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (ε : ℝ) (hε : 0 < ε) (x t : ℝ) (ht : t ∈ J) :
    c.ds g (c.regularizedCurvature g ε) x t =
      (1 / (2 * c.regularizedCurvature g ε x t)) * c.ds g (c.curvatureSq g) x t := by
  have hu : ContDiff ℝ ∞ (fun y => c.curvatureSq g y t) :=
    c.curvatureSq_contDiff g J hc hi t ht
  have hd : DifferentiableAt ℝ (fun y => c.curvatureSq g y t) x :=
    hu.contDiffAt.differentiableAt (by norm_num)
  have hpos : c.curvatureSq g x t + ε ^ 2 ≠ 0 := by
    have h0 : 0 ≤ c.curvatureSq g x t := c.normSq_nonneg g (c.curvatureVector g) x t
    nlinarith [sq_nonneg ε]
  have hsqrt : HasDerivAt (fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2))
      (deriv (fun y => c.curvatureSq g y t) x /
        (2 * Real.sqrt (c.curvatureSq g x t + ε ^ 2))) x :=
    (hd.hasDerivAt.add_const (ε ^ 2)).sqrt hpos
  have hderiv : deriv (fun y => c.regularizedCurvature g ε y t) x =
      (1 / (2 * c.regularizedCurvature g ε x t)) *
        deriv (fun y => c.curvatureSq g y t) x := by
    have h1 : (fun y => c.regularizedCurvature g ε y t)
        = fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2) := rfl
    rw [h1, hsqrt.deriv]
    simp only [CurveMap.regularizedCurvature]
    ring
  simp only [CurveMap.ds]
  rw [hderiv]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem CurveMap.derivWithin_regularizedCurvature (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (ε : ℝ) (hε : 0 < ε) (x t : ℝ)
    (huniq : UniqueDiffWithinAt ℝ J t)
    (hu : HasDerivWithinAt (fun r => c.curvatureSq g x r)
      (derivWithin (fun r => c.curvatureSq g x r) J t) J t) :
    derivWithin (fun r => c.regularizedCurvature g ε x r) J t =
      (1 / (2 * c.regularizedCurvature g ε x t)) *
        derivWithin (fun r => c.curvatureSq g x r) J t := by
  have hpos : c.curvatureSq g x t + ε ^ 2 ≠ 0 := by
    have h0 : 0 ≤ c.curvatureSq g x t := c.normSq_nonneg g (c.curvatureVector g) x t
    nlinarith [sq_nonneg ε]
  have h1 : HasDerivWithinAt (fun r => c.curvatureSq g x r + ε ^ 2)
      (derivWithin (fun r => c.curvatureSq g x r) J t) J t :=
    hu.add_const (ε ^ 2)
  have h2 := h1.sqrt hpos
  have hfun : (fun r => c.regularizedCurvature g ε x r) =
      fun r => Real.sqrt (c.curvatureSq g x r + ε ^ 2) := rfl
  rw [hfun, h2.derivWithin huniq]
  simp only [CurveMap.regularizedCurvature]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem CurveMap.differentiableAt_ds_curvatureSq (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    DifferentiableAt ℝ (fun y => c.ds g (c.curvatureSq g) y t) x := by
  have hu : ContDiff ℝ ∞ (fun y => c.curvatureSq g y t) :=
    c.curvatureSq_contDiff g J hc hi t ht
  have hdu : ContDiff ℝ ∞ (fun y => deriv (fun z => c.curvatureSq g z t) y) := by
    simpa using hu.iterate_deriv 1
  have hs : ContDiff ℝ ∞ (fun y => (c.speed g y t)⁻¹) :=
    (c.speed_contDiff g J hc hi t ht).inv (fun y => ne_of_gt (c.speed_pos g hi y t ht))
  have hmul : ContDiff ℝ ∞ (fun y => (c.speed g y t)⁻¹ *
      deriv (fun z => c.curvatureSq g z t) y) := hs.mul hdu
  have hfun : (fun y => c.ds g (c.curvatureSq g) y t) =
      fun y => (c.speed g y t)⁻¹ * deriv (fun z => c.curvatureSq g z t) y := rfl
  rw [hfun]
  exact hmul.contDiffAt.differentiableAt (by norm_num)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem CurveMap.ds_ds_regularizedCurvature (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (ε : ℝ) (hε : 0 < ε) (x t : ℝ) (ht : t ∈ J) :
    c.ds g (c.ds g (c.regularizedCurvature g ε)) x t =
      (1 / (2 * c.regularizedCurvature g ε x t)) *
          c.ds g (c.ds g (c.curvatureSq g)) x t -
        (c.ds g (c.curvatureSq g) x t) ^ 2 /
          (4 * c.regularizedCurvature g ε x t ^ 3) := by
  have hdy : DifferentiableAt ℝ (fun y => c.ds g (c.curvatureSq g) y t) x :=
    CurveMap.differentiableAt_ds_curvatureSq g c J hc hi x t ht
  set d : ℝ → ℝ := fun y => c.ds g (c.curvatureSq g) y t with hd
  set f : ℝ → ℝ := fun y => 1 / (2 * c.regularizedCurvature g ε y t) with hfdef
  have hu : ContDiff ℝ ∞ (fun y => c.curvatureSq g y t) :=
    c.curvatureSq_contDiff g J hc hi t ht
  have hdu : DifferentiableAt ℝ (fun y => c.curvatureSq g y t) x :=
    hu.contDiffAt.differentiableAt (by norm_num)
  have hsqpos : 0 < c.curvatureSq g x t + ε ^ 2 := by
    have h0 : 0 ≤ c.curvatureSq g x t := c.normSq_nonneg g (c.curvatureVector g) x t
    nlinarith [sq_nonneg ε]
  have hreg : DifferentiableAt ℝ (fun y => c.regularizedCurvature g ε y t) x := by
    have h1 : HasDerivAt (fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2))
        (deriv (fun y => c.curvatureSq g y t) x /
          (2 * Real.sqrt (c.curvatureSq g x t + ε ^ 2))) x :=
      (hdu.hasDerivAt.add_const (ε ^ 2)).sqrt (ne_of_gt hsqpos)
    have hfun : (fun y => c.regularizedCurvature g ε y t) =
        fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2) := rfl
    rw [hfun]
    exact h1.differentiableAt
  have hregne : c.regularizedCurvature g ε x t ≠ 0 := by
    simp only [CurveMap.regularizedCurvature]
    exact ne_of_gt (Real.sqrt_pos.mpr hsqpos)
  have hd' : DifferentiableAt ℝ d x := hdy
  have hsne : c.speed g x t ≠ 0 := ne_of_gt (c.speed_pos g hi x t ht)
  have hu' : deriv (fun y => c.curvatureSq g y t) x =
      c.speed g x t * c.ds g (c.curvatureSq g) x t := by
    have hident : c.ds g (c.curvatureSq g) x t =
        (c.speed g x t)⁻¹ * deriv (fun y => c.curvatureSq g y t) x := rfl
    rw [hident]
    field_simp
  have hreg' : deriv (fun y => c.regularizedCurvature g ε y t) x =
      (1 / (2 * c.regularizedCurvature g ε x t)) *
        (c.speed g x t * c.ds g (c.curvatureSq g) x t) := by
    have h1 : HasDerivAt (fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2))
        (deriv (fun y => c.curvatureSq g y t) x /
          (2 * Real.sqrt (c.curvatureSq g x t + ε ^ 2))) x :=
      (hdu.hasDerivAt.add_const (ε ^ 2)).sqrt (ne_of_gt hsqpos)
    have hfun : (fun y => c.regularizedCurvature g ε y t) =
        fun y => Real.sqrt (c.curvatureSq g y t + ε ^ 2) := rfl
    rw [hfun, h1.deriv, hu']
    simp only [CurveMap.regularizedCurvature]
    ring
  have hf' : DifferentiableAt ℝ f x := by
    rw [hfdef]
    exact (differentiableAt_const (c := (1 : ℝ))).div
      ((differentiableAt_const (c := (2 : ℝ))).mul hreg)
      (mul_ne_zero two_ne_zero hregne)
  have hfder : deriv f x = -(c.speed g x t * d x) /
      (4 * c.regularizedCurvature g ε x t ^ 3) := by
    rw [hfdef]
    have hfe : (fun y => 1 / (2 * c.regularizedCurvature g ε y t)) =
        fun y => (2 * c.regularizedCurvature g ε y t)⁻¹ := by
      funext y
      rw [one_div]
    rw [hfe, deriv_fun_inv''
      (c := fun y => 2 * c.regularizedCurvature g ε y t)
      ((differentiableAt_const (c := (2 : ℝ))).mul hreg)
      (mul_ne_zero two_ne_zero hregne),
      deriv_const_mul (d := fun y => c.regularizedCurvature g ε y t) (2 : ℝ) hreg, hreg']
    simp only [hd]
    field_simp
    ring
  have hfun : (fun y => c.ds g (c.regularizedCurvature g ε) y t) = f * d := by
    funext y
    simp only [Pi.mul_apply, hfdef, hd]
    exact CurveMap.ds_regularizedCurvature g c J hc hi ε hε y t ht
  have hkey : c.ds g (c.ds g (c.regularizedCurvature g ε)) x t =
      (c.speed g x t)⁻¹ * deriv (fun y => c.ds g (c.regularizedCurvature g ε) y t) x := rfl
  have hder : deriv (fun y => c.ds g (c.regularizedCurvature g ε) y t) x = deriv (f * d) x := by
    rw [hfun]
  have hds2 : c.ds g (c.ds g (c.curvatureSq g)) x t = (c.speed g x t)⁻¹ * deriv d x := by
    rw [hd]
    rfl
  rw [hkey, hder, deriv_mul hf' hd', hds2, hfder]
  have hdval : d x = c.ds g (c.curvatureSq g) x t := by rw [hd]
  have hfval : f x = 1 / (2 * c.regularizedCurvature g ε x t) := by rw [hfdef]
  simp only [hdval, hfval]
  field_simp
  ring


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem CurveMap.ds_inner (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (V W : c.Field (I := I))
    (x t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift y t) (V y t) : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift y t) (W y t) : TangentBundle I M))) :
    c.ds g (fun y r => (g r).inner (c.lift y r) (V y r) (W y r)) x t =
      (g t).inner (c.lift x t) (c.Ds g V x t) (W x t) +
        (g t).inner (c.lift x t) (V x t) (c.Ds g W x t) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y : ℝ => c.lift y t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c J hc t ht)
  have hd := metric_compat_hasDerivAt_inner (by simp : (1 : WithTop ℕ∞) ≤ ∞) (g t)
    (fun y : ℝ => c.lift y t) (fun y => V y t) (fun y => W y t) x hγ
    (chartRep_diff (I := I) (fun y : ℝ => c.lift y t) (fun y => V y t) hV x)
    (chartRep_diff (I := I) (fun y : ℝ => c.lift y t) (fun y => W y t) hW x)
  rw [CurveMap.ds, hd.deriv]
  simp only [CurveMap.Ds, CurveMap.Dx, map_smul, smul_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] in
theorem CurveMap.derivWithin_curvatureSq_le_regularized
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (s u : ℝ) (hsu : s < u) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u)) (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C)
    (x t : ℝ) (ht : t ∈ Icc s u)
    (hu : HasDerivWithinAt (fun r => c.curvatureSq g x r)
      (derivWithin (fun r => c.curvatureSq g x r) (Icc s u) t) (Icc s u) t)
    (hce : derivWithin (fun r => c.curvatureSq g x r) (Icc s u) t ≤
      c.ds g (c.ds g (c.curvatureSq g)) x t -
      2 * c.normSq g (c.normalCurvatureDerivative g) x t +
      2 * c.curvatureSq g x t ^ 2 +
      2 * C * (c.curvatureSq g x t + c.curvature g x t)) :
    derivWithin (fun r => c.regularizedCurvature g ε x r) (Icc s u) t ≤
      c.ds g (c.ds g (c.regularizedCurvature g ε)) x t +
        c.curvatureSq g x t * c.regularizedCurvature g ε x t +
        C * (c.regularizedCurvature g ε x t + 1) := by
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) t := (uniqueDiffOn_Icc hsu) t ht
  have hk2nn : 0 ≤ c.curvatureSq g x t :=
    c.normSq_nonneg g (c.curvatureVector g) x t
  have hN2nn : 0 ≤ c.normSq g (c.normalCurvatureDerivative g) x t :=
    c.normSq_nonneg g (c.normalCurvatureDerivative g) x t
  have hsqpos : 0 < c.curvatureSq g x t + ε ^ 2 := by nlinarith [sq_nonneg ε]
  have hregpos : 0 < c.regularizedCurvature g ε x t := by
    simp only [CurveMap.regularizedCurvature]
    exact Real.sqrt_pos.mpr hsqpos
  have hrsq : c.regularizedCurvature g ε x t ^ 2 = c.curvatureSq g x t + ε ^ 2 :=
    Real.sq_sqrt hsqpos.le
  have hksq : c.curvature g x t ^ 2 = c.curvatureSq g x t := c.curvature_sq g x t
  have hknn : 0 ≤ c.curvature g x t := c.curvature_nonneg g x t
  have hkle : c.curvature g x t ≤ c.regularizedCurvature g ε x t := by
    simp only [CurveMap.regularizedCurvature, CurveMap.curvature]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hchain := CurveMap.derivWithin_regularizedCurvature g c (Icc s u) ε hε x t huniq hu
  have hds2 := CurveMap.ds_ds_regularizedCurvature g c (Icc s u) hc hi ε hε x t ht
  have hcs := CurveMap.ds_curvatureSq_sq_le_mul_normSq_normalCurvatureDerivative
    (g := g) c (Icc s u) hc hi x t ht
  rw [hchain, hds2]
  have hstep : (1 / (2 * c.regularizedCurvature g ε x t)) *
      derivWithin (fun r => c.curvatureSq g x r) (Icc s u) t ≤
      (1 / (2 * c.regularizedCurvature g ε x t)) *
        (c.ds g (c.ds g (c.curvatureSq g)) x t -
          2 * c.normSq g (c.normalCurvatureDerivative g) x t +
          2 * c.curvatureSq g x t ^ 2 +
          2 * C * (c.curvatureSq g x t + c.curvature g x t)) :=
    mul_le_mul_of_nonneg_left hce (by positivity)
  refine hstep.trans ?_
  have hD : 0 ≤ c.regularizedCurvature g ε x t ^ 2 - c.curvatureSq g x t := by
    rw [hrsq]
    nlinarith [sq_nonneg ε]
  have hE : 0 ≤ c.regularizedCurvature g ε x t - c.curvature g x t := by linarith [hkle]
  have hr2 : 0 ≤ c.regularizedCurvature g ε x t ^ 2 := sq_nonneg _
  have hCr2 : 0 ≤ C * c.regularizedCurvature g ε x t ^ 2 := mul_nonneg hC hr2
  have hp1 : 0 ≤ (c.regularizedCurvature g ε x t ^ 2 - c.curvatureSq g x t) *
      c.normSq g (c.normalCurvatureDerivative g) x t := mul_nonneg hD hN2nn
  have hp2 : 0 ≤ (c.regularizedCurvature g ε x t ^ 2 - c.curvatureSq g x t) *
      (c.curvatureSq g x t * c.regularizedCurvature g ε x t ^ 2) :=
    mul_nonneg hD (mul_nonneg hk2nn hr2)
  have hp3 : 0 ≤ (c.regularizedCurvature g ε x t ^ 2 - c.curvatureSq g x t) *
      (C * c.regularizedCurvature g ε x t ^ 2) := mul_nonneg hD hCr2
  have hp4 : 0 ≤ (c.regularizedCurvature g ε x t - c.curvature g x t) *
      (C * c.regularizedCurvature g ε x t ^ 2) := mul_nonneg hE hCr2
  field_simp
  nlinarith [hcs, hp1, hp2, hp3, hp4, hknn, hksq]


theorem CurveMap.normSq_normalCurvatureDerivative (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    c.normSq g (c.normalCurvatureDerivative g) x t =
      c.normSq g (c.Ds g (c.curvatureVector g)) x t - c.curvatureSq g x t ^ 2 := by
  have hgeom := tangent_curvature_geometry g c J hc hi x t ht
  have hN : c.normalCurvatureDerivative g x t =
      c.Ds g (c.curvatureVector g) x t + c.curvatureSq g x t • c.unitTangent g x t := rfl
  rw [CurveMap.normSq, CurveMap.normSq, hN]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [(g t).symm (c.lift x t) (c.unitTangent g x t) (c.Ds g (c.curvatureVector g) x t),
    hgeom.1, hgeom.2.2]
  ring

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
