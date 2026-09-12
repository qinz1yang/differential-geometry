import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def productCoverProjection : C(M × ℝ, M × Surgery.Topology.Circle) :=
  ⟨fun p => (p.1, (p.2 : Surgery.Topology.Circle)), continuous_fst.prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)⟩

structure ProductCurve (M : Type*) where
  map : CurveMap (M × Surgery.Topology.Circle)
  y : ℝ → ℝ → ℝ
  degree : ℤ
  lift_eq : ∀ x t, (y x t : Surgery.Topology.Circle) = (map (x : Surgery.Topology.Circle) t).2
  increment : ∀ x t, y (x + 1) t = y x t + degree

namespace ProductCurve

variable (c : ProductCurve M)


def projection : CurveMap M := fun x t => (c.map x t).1


def coverLift (x t : ℝ) : M × ℝ := (c.projection.lift x t, c.y x t)

@[simp] theorem coverProjection_lift (x t : ℝ) :
    productCoverProjection (c.coverLift x t) = c.map (x : Surgery.Topology.Circle) t := by
  apply Prod.ext
  · rfl
  · exact c.lift_eq x t


abbrev Field := (x t : ℝ) → TangentSpace I (c.projection.lift x t) × ℝ


def inner (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ)
    (v w : TangentSpace I (c.projection.lift x t) × ℝ) : ℝ :=
  (g t).inner (c.projection.lift x t) v.1 w.1 + lambda ^ 2 * v.2 * w.2

def X : c.Field (I := I) := fun x t =>
  (c.projection.X (I := I) x t, deriv (fun z => c.y z t) x)

def velocity (J : Set ℝ) : c.Field (I := I) := fun x t =>
  (c.projection.velocity (I := I) J x t, derivWithin (c.y x) J t)

def speed (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt (c.inner g lambda x t (c.X x t) (c.X x t))

def unitTangent (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : c.Field (I := I) :=
  fun x t => (c.speed g lambda x t)⁻¹ • c.X x t


def Dx (g : ℝ → SmoothRiemannianMetric I M) (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => (V z t).1) x, deriv (fun z => (V z t).2) x)

def Ds (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (c.speed g lambda x t)⁻¹ • c.Dx g V x t

def curvatureVector (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : c.Field (I := I) :=
  c.Ds g lambda (c.unitTangent g lambda)

def normSq (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) (x t : ℝ) : ℝ := c.inner g lambda x t (V x t) (V x t)

def curvatureSq (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ → ℝ :=
  c.normSq g lambda (c.curvatureVector g lambda)

def curvature (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt (c.curvatureSq g lambda x t)

def iteratedDs (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (m : ℕ) (V : c.Field (I := I)) : c.Field (I := I) := (c.Ds g lambda)^[m] V

def ds (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (c.speed g lambda x t)⁻¹ * deriv (fun z => f z t) x

def integral (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (f : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, f x t * c.speed g lambda x t

def length (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ) : ℝ :=
  c.integral g lambda (fun _ _ => 1) t

def totalCurvature (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ :=
  c.integral g lambda (c.curvature g lambda)

def energy (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ :=
  c.integral g lambda (c.curvatureSq g lambda)

def arcLength (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.speed g lambda x t

def arcTotalCurvature (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.curvature g lambda x t * c.speed g lambda x t

def arcEnergy (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.curvatureSq g lambda x t * c.speed g lambda x t


def SmoothOn (J : Set ℝ) : Prop :=
  c.projection.SmoothOn (I := I) J ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.y p.1 p.2) (univ ×ˢ J)

def ImmersedOn (J : Set ℝ) : Prop := ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0

structure IsSolutionOn (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (J : Set ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t = c.curvatureVector g lambda x t


def verticalUnit (lambda : ℝ) : c.Field (I := I) := fun _ _ => (0, lambda⁻¹)


def angle (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  c.inner g lambda x t (c.unitTangent g lambda x t) (c.verticalUnit lambda x t)


def IsRampOn (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (J : Set ℝ) : Prop :=
  c.ImmersedOn (I := I) J ∧ ∀ x t, t ∈ J → 0 < c.angle g lambda x t

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    0 ≤ c.speed g lambda x t := Real.sqrt_nonneg _

omit [CompleteSpace E] in
theorem curvature_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    0 ≤ c.curvature g lambda x t := Real.sqrt_nonneg _

end ProductCurve

theorem exists_coverProductMetric (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ ĝ : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ),
      ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
        ĝ.inner p v w = g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2 := by
  sorry

def coverProductMetric (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) :=
  (exists_coverProductMetric g lambda hlambda).choose

theorem coverProductMetric_inner (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (coverProductMetric g lambda hlambda).inner p v w =
      g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2 :=
  (exists_coverProductMetric g lambda hlambda).choose_spec p v w


theorem coverProductMetric_unique (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (ĝ : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hĝ : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      ĝ.inner p v w = g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2) :
    ĝ = coverProductMetric g lambda hlambda := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [hĝ, coverProductMetric_inner]

structure QuotientProductAtlas (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  charts : ChartedSpace (ModelProd H ℝ) (M × Surgery.Topology.Circle)
  smoothManifold : letI := charts
    IsManifold (I.prod 𝓘(ℝ, ℝ)) ∞ (M × Surgery.Topology.Circle)
  cover_smooth : letI := charts
    letI := smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (productCoverProjection (M := M))
  cover_derivative_bijective : letI := charts
    letI := smoothManifold
    ∀ p : M × ℝ, Function.Bijective
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p)

theorem exists_quotientProductAtlas : Nonempty (QuotientProductAtlas I M) := by
  sorry

def quotientProductAtlas : QuotientProductAtlas I M := exists_quotientProductAtlas.some

structure QuotientProductGeometry (A : QuotientProductAtlas I M)
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) where
  metric : letI := A.charts
    letI := A.smoothManifold
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × Surgery.Topology.Circle)
  cover_pullback : letI := A.charts
    letI := A.smoothManifold
    ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      metric.inner (productCoverProjection p)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p v)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p w) =
          (coverProductMetric g lambda hlambda).inner p v w

theorem exists_quotientProductGeometry (A : QuotientProductAtlas I M)
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    Nonempty (QuotientProductGeometry A g lambda hlambda) := by
  sorry


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem ProductCurve.cover_spatial_derivative (c : ProductCurve M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.coverLift z t) x (1 : ℝ) =
      c.X (I := I) x t := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ => (z, t)) univ x :=
    contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hz' : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hz
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞
        ((fun p : ℝ × ℝ => c.projection.lift p.1 p.2) ∘ fun z : ℝ => (z, t)) univ x :=
      (hc.1 (x, t) hmem).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun z : ℝ => (z, t)) univ x :=
      ((hc.2 (x, t) hmem).contMDiffWithinAt).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  have hpair := h1.mfderiv_prod h2
  change (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
    (fun z => (c.projection.lift z t, c.y z t)) x) (1 : ℝ) = c.X (I := I) x t
  rw [hpair]
  change (((mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x).prod
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x))
      (1 : TangentSpace 𝓘(ℝ, ℝ) x)) = c.X (I := I) x t
  rw [show ((mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x).prod
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x))
      (1 : TangentSpace 𝓘(ℝ, ℝ) x) = _ from
    ContinuousLinearMap.prod_apply (f₁ := mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x)
      (f₂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x)
      (x := (1 : TangentSpace 𝓘(ℝ, ℝ) x))]
  refine Prod.ext rfl ?_
  change ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x : ℝ →L[ℝ] ℝ)
      (1 : TangentSpace 𝓘(ℝ, ℝ) x)) =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).symm (deriv (fun z => c.y z t) x)
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).injective
  rw [(NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).apply_symm_apply]
  change mvfderiv (I := 𝓘(ℝ, ℝ)) (fun z => c.y z t) x
      (1 : TangentSpace 𝓘(ℝ, ℝ) x) = deriv (fun z => c.y z t) x
  rw [DifferentialGeometry.mvfderiv_real_model_eq_fderiv,
    show (1 : TangentSpace 𝓘(ℝ, ℝ) x) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1 from rfl,
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).apply_symm_apply, fderiv_apply_one_eq_deriv]

theorem ProductCurve.cover_covariantDerivative (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (V : c.Field (I := I))
    (hV : ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x t : ℝ) (ht : t ∈ J) :
    covDerivAlong (coverProductMetric (g t) lambda hlambda) (fun z => c.coverLift z t)
      (fun z => V z t) x = c.Dx g V x t := by
  sorry

section QuotientGeometry

variable (A : QuotientProductAtlas I M)


def quotientProductMetric (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × Surgery.Topology.Circle) :=
  (exists_quotientProductGeometry A g lambda hlambda).some.metric

theorem product_solution_iff (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ProductCurve M) {s u : ℝ} (hsu : s < u)
    (J : Set ℝ) (hJ : J = Ico s u ∨ J = Icc s u)
    (hylift : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (univ ×ˢ J)) :
    letI := A.charts
    letI := A.smoothManifold
    c.IsSolutionOn g lambda J ↔
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  sorry

theorem product_solution_lift (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : CurveMap (M × Surgery.Topology.Circle)) {s u : ℝ} (hsu : s < u)
    (J : Set ℝ) (hJ : J = Ico s u ∨ J = Icc s u)
    (hc : letI := A.charts
      letI := A.smoothManifold
      c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    ∃ ĉ : ProductCurve M, ĉ.IsSolutionOn g lambda J ∧
      ∀ z t, t ∈ J → ĉ.map z t = c z t := by
  sorry

variable [SigmaCompactSpace M] [T2Space M]

def quotientProductFamily (G : SolutionFamily (I := I) (M := M)) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    SolutionFamily (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) :=
  by
    letI := A.charts
    letI := A.smoothManifold
    exact ⟨fun t => quotientProductMetric A (G.metric t) lambda hlambda⟩

theorem quotientProduct_ricciBackground {D : Geometry.Curvature.RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D a b,
      Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
      Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ := by
  sorry

end QuotientGeometry

theorem exists_productCurve_lift (c : CurveMap (M × Surgery.Topology.Circle)) {a b : ℝ} (hab : a < b)
    (hbase : CurveMap.SmoothOn (I := I) (fun z t => (c z t).1) (Icc a b))
    (hcircle : ∀ x t, t ∈ Icc a b → ∃ localLift : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ localLift (univ ×ˢ Icc a b) (x, t) ∧
      ∀ᶠ p in 𝓝[univ ×ˢ Icc a b] (x, t),
        (localLift p : Surgery.Topology.Circle) = (c (p.1 : Surgery.Topology.Circle) p.2).2) :
    ∃ ĉ : ProductCurve M, ĉ.SmoothOn (I := I) (Icc a b) ∧
      ∀ z t, t ∈ Icc a b → ĉ.map z t = c z t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
