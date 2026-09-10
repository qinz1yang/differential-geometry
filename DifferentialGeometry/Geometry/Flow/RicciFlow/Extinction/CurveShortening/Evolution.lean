import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

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

theorem rfs_csf_speed (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.speed B.family.metric x) (Icc s u) t =
      -c.q B.family x t * c.speed B.family.metric x t ∧
    c.Dt B.family.metric (Icc s u) (c.unitTangent B.family.metric) x t =
      c.Ds B.family.metric (c.curvatureVector B.family.metric) x t +
        c.q B.family x t • c.unitTangent B.family.metric x t := by
  sorry


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

theorem speed_exponential_bounds (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Icc s u → c.curvature B.family.metric x t ≤ K)
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)) ≤
      c.speed B.family.metric x t ∧
    c.speed B.family.metric x t ≤
      c.speed B.family.metric x s * Real.exp (B.B₀ * (t - s)) := by
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

theorem curvature_evolution_le (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.curvatureSq B.family.metric x) (Icc s u) t ≤
      c.ds B.family.metric (c.ds B.family.metric (c.curvatureSq B.family.metric)) x t -
      2 * c.normSq B.family.metric (c.normalCurvatureDerivative B.family.metric) x t +
      2 * c.curvatureSq B.family.metric x t ^ 2 +
      2 * B.C * (c.curvatureSq B.family.metric x t + c.curvature B.family.metric x t) := by
  sorry


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
