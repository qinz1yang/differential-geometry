import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev CurveMap (M : Type*) := AddCircle (1 : ℝ) → ℝ → M

namespace CurveMap

def lift (c : CurveMap M) (x t : ℝ) : M := c (x : AddCircle (1 : ℝ)) t


def X (c : CurveMap M) (x t : ℝ) : TangentSpace I (c.lift x t) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x (1 : ℝ)


def velocity (c : CurveMap M) (J : Set ℝ) (x t : ℝ) :
    TangentSpace I (c.lift x t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t (1 : ℝ)

def speed (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) : ℝ :=
  Real.sqrt ((g t).inner (c.lift x t) (c.X (I := I) x t) (c.X (I := I) x t))

abbrev Field (c : CurveMap M) := (x t : ℝ) → TangentSpace I (c.lift x t)

def unitTangent (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : c.Field (I := I) :=
  fun x t => (c.speed g x t)⁻¹ • c.X x t


def Dx (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => covDerivAlong (g t) (fun y => c.lift y t) (fun y => V y t) x

def Dt (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (V : c.Field (I := I)) : c.Field (I := I) := fun x t =>
  let γ := c.lift x
  let rep := chartRepAt (I := I) γ (V x) t
  (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
    (derivWithin rep J t +
      chartChristoffelContraction (g t) (γ t)
        (derivWithin (chartCurve (I := I) (γ t) γ) J t) (rep t)
        (chartCurve (I := I) (γ t) γ t))

def Ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (c.speed g x t)⁻¹ • c.Dx g V x t

def curvatureVector (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) :
    c.Field (I := I) := c.Ds g (c.unitTangent g)

def normSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) (x t : ℝ) : ℝ :=
  (g t).inner (c.lift x t) (V x t) (V x t)

def curvatureSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ → ℝ :=
  c.normSq g (c.curvatureVector g)

def curvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) : ℝ :=
  Real.sqrt (c.curvatureSq g x t)

def ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (c.speed g x t)⁻¹ * deriv (fun y => f y t) x

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_add (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ + h y τ) x t = c.ds g f x t + c.ds g h x t := by
  simp only [ds, deriv_fun_add hf hh, mul_add]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_sub (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ - h y τ) x t = c.ds g f x t - c.ds g h x t := by
  simp only [ds, deriv_fun_sub hf hh, mul_sub]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_mul (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ * h y τ) x t = c.ds g f x t * h x t + f x t * c.ds g h x t := by
  simp only [ds, deriv_fun_mul hf hh]
  ring

def integral (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, f x t * c.speed g x t

def length (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) : ℝ :=
  c.integral g (fun _ _ => 1) t

def totalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ :=
  c.integral g (c.curvature g)

def energy (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ :=
  c.integral g (c.curvatureSq g)

def iteratedDs (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (m : ℕ) (V : c.Field (I := I)) : c.Field (I := I) :=
  (c.Ds g)^[m] V


def SmoothOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p => c.lift p.1 p.2) (univ ×ˢ J)

def ImmersedOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0


structure IsSolutionOn (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t = c.curvatureVector g x t


structure IsGeometricSolutionOn (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (α : ℝ → ℝ → ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  tangentSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (univ ×ˢ J)
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t =
    c.curvatureVector g x t + α x t • c.unitTangent g x t

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) :
    0 ≤ c.speed g x t := Real.sqrt_nonneg _

omit [CompleteSpace E] in
theorem curvature_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) :
    0 ≤ c.curvature g x t := Real.sqrt_nonneg _

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_pos (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g x t :=
  Real.sqrt_pos.2 ((g t).pos (c.lift x t) (c.X x t) (hc x t ht))

end CurveMap

variable [SigmaCompactSpace M] [T2Space M]

structure SmoothMetricWindow (D : RealTimeInterval) (a b : ℝ) where
  family : SolutionFamily (I := I) (M := M)
  smooth : MetricFamilySmoothOn (I := I) D family.metric
  lt : a < b
  regular : Icc a b ⊆ D.regular

structure RicciBackground (D : RealTimeInterval) (a b : ℝ) extends
    SmoothMetricWindow (I := I) (M := M) D a b where
  equation : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
    (show SolutionOn (I := I) (M := M) D from ⟨family⟩)
  B₀ : ℝ
  B₁ : ℝ
  B₂ : ℝ
  B₀_nonneg : 0 ≤ B₀
  B₁_nonneg : 0 ≤ B₁
  B₂_nonneg : 0 ≤ B₂
  ricci_bound : ∀ t ∈ Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 2 (family.ricciAt t p) ≤ B₀ ^ 2
  riemann_bound : ∀ t ∈ Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 4 (family.rm04At t p) ≤ B₁ ^ 2
  nablaRicci_bound : ∀ t ∈ Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 3
      (totalNabla0SFun 2 (family.connection t) (family.ricci t) p) ≤ B₂ ^ 2

def RicciBackground.C {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) : ℝ :=
  1 + 3 * B.B₀ + B.B₁ + 3 * B.B₂

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J t := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((univ : Set ℝ) ×ˢ J) :=
    fun s _ => ⟨mem_univ x, by assumption⟩
  exact (hc (x, t) hmem).comp t hz hto

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x : ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J :=
  fun t ht => time_slice_contMDiffWithinAt c J hc x t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) univ x := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  exact (hc (x, t) hmem).comp x hz hto

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) univ :=
  fun x _ => space_slice_contMDiffWithinAt c J hc x t ht

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
