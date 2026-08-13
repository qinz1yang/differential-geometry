import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Curvature.Realized.Stationary
import DifferentialGeometry.Geometry.Operator.GradientRegularity

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section


open Set
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

structure IsHeatPotOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (V u : Real → M → Real) : Prop where
  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)
  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)
  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)
  equation :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => u s x)
        (laplacianAt (I := I) G t (u t) x + V t x * u t x) t

abbrev IsHeatOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (u : Real → M → Real) : Prop :=
  IsHeatPotOn D G (fun _ _ => 0) u

abbrev IsHeatOnStationary
    (D : RealTimeInterval)
    (g : SmoothRiemannianMetric I M)
    (u : Real → M → Real) : Prop :=
  IsHeatOn D (stationaryMetricFamily (I := I) (M := M) g) u

structure IsHeatForcedOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (f u : Real → M → Real) : Prop where
  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)
  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)
  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)
  equation :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => u s x)
        (laplacianAt (I := I) G t (u t) x + f t x) t

abbrev IsHeatForcedOnStationary
    (D : RealTimeInterval)
    (g : SmoothRiemannianMetric I M)
    (f u : Real → M → Real) : Prop :=
  IsHeatForcedOn D (stationaryMetricFamily (I := I) (M := M) g) f u

namespace IsHeatForcedOn

theorem mono
    {D D' : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {f u : Real → M → Real}
    (h : IsHeatForcedOn D G f u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatForcedOn D' G f u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  equation t ht x := h.equation t (hregular ht) x

end IsHeatForcedOn

structure IsHeatPotSubsolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (V u : Real → M → Real) : Prop where
  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)
  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)
  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)
  timeDiff :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      DifferentiableAt Real (fun s : Real => u s x) t
  equation_le :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      deriv (fun s : Real => u s x) t ≤
        laplacianAt (I := I) G t (u t) x + V t x * u t x

structure IsHeatPotSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (V u : Real → M → Real) : Prop where
  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)
  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)
  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)
  timeDiff :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      DifferentiableAt Real (fun s : Real => u s x) t
  equation_ge :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      laplacianAt (I := I) G t (u t) x + V t x * u t x ≤
        deriv (fun s : Real => u s x) t

abbrev IsHeatSubsolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (u : Real → M → Real) : Prop :=
  IsHeatPotSubsolutionOn D G (fun _ _ ↦ 0) u

abbrev IsHeatSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (u : Real → M → Real) : Prop :=
  IsHeatPotSupersolutionOn D G (fun _ _ ↦ 0) u

namespace IsHeatPotOn

theorem mono
    {D D' : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotOn D G V u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatPotOn D' G V u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  equation t ht x := h.equation t (hregular ht) x

theorem sub
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u v : Real → M → Real}
    (hu : IsHeatPotOn D G V u)
    (hv : IsHeatPotOn D G V v) :
    IsHeatPotOn D G V (fun t x => u t x - v t x) where
  jointSmooth := hu.jointSmooth.sub hv.jointSmooth
  jointCont := hu.jointCont.sub hv.jointCont
  sliceSmooth t ht := (hu.sliceSmooth t ht).sub (hv.sliceSmooth t ht)
  equation t ht x := by
    have htcarrier : t ∈ D.carrier := D.regular_subset ht
    have husmooth := hu.sliceSmooth t htcarrier
    have hvsmooth := hv.sliceSmooth t htcarrier
    have hlaplacian := laplacianAt_sub (I := I) G t
      (fun y => husmooth.mdifferentiable (by simp) y)
      (fun y => hvsmooth.mdifferentiable (by simp) y)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) husmooth x)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) hvsmooth x)
    convert (hu.equation t ht x).sub (hv.equation t ht x) using 1
    rw [hlaplacian]
    ring

theorem toSubsolution
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotOn D G V u) :
    IsHeatPotSubsolutionOn D G V u where
  jointSmooth := h.jointSmooth
  jointCont := h.jointCont
  sliceSmooth := h.sliceSmooth
  timeDiff t ht x := (h.equation t ht x).differentiableAt
  equation_le t ht x := (h.equation t ht x).deriv.le

theorem toSupersolution
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotOn D G V u) :
    IsHeatPotSupersolutionOn D G V u where
  jointSmooth := h.jointSmooth
  jointCont := h.jointCont
  sliceSmooth := h.sliceSmooth
  timeDiff t ht x := (h.equation t ht x).differentiableAt
  equation_ge t ht x := (h.equation t ht x).deriv.ge

end IsHeatPotOn

namespace IsHeatPotSupersolutionOn

theorem mono
    {D D' : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotSupersolutionOn D G V u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatPotSupersolutionOn D' G V u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  timeDiff t ht x := h.timeDiff t (hregular ht) x
  equation_ge t ht x := h.equation_ge t (hregular ht) x

theorem sub
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u v : Real → M → Real}
    (hu : IsHeatPotSupersolutionOn D G V u)
    (hv : IsHeatPotSubsolutionOn D G V v) :
    IsHeatPotSupersolutionOn D G V (fun t x => u t x - v t x) where
  jointSmooth := hu.jointSmooth.sub hv.jointSmooth
  jointCont := hu.jointCont.sub hv.jointCont
  sliceSmooth t ht := (hu.sliceSmooth t ht).sub (hv.sliceSmooth t ht)
  timeDiff t ht x := (hu.timeDiff t ht x).sub (hv.timeDiff t ht x)
  equation_ge t ht x := by
    have htcarrier : t ∈ D.carrier := D.regular_subset ht
    have husmooth := hu.sliceSmooth t htcarrier
    have hvsmooth := hv.sliceSmooth t htcarrier
    have hlaplacian := laplacianAt_sub (I := I) G t
      (fun y => husmooth.mdifferentiable (by simp) y)
      (fun y => hvsmooth.mdifferentiable (by simp) y)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) husmooth x)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) hvsmooth x)
    have hderiv : deriv (fun s => u s x - v s x) t =
        deriv (fun s => u s x) t - deriv (fun s => v s x) t := by
      simpa only [Pi.sub_apply] using
        deriv_sub (hu.timeDiff t ht x) (hv.timeDiff t ht x)
    rw [hlaplacian, hderiv]
    linarith [hu.equation_ge t ht x, hv.equation_le t ht x]

theorem neg
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotSupersolutionOn D G V u) :
    IsHeatPotSubsolutionOn D G V (fun t x => -u t x) where
  jointSmooth := h.jointSmooth.neg
  jointCont := h.jointCont.neg
  sliceSmooth t ht := (h.sliceSmooth t ht).neg
  timeDiff t ht x := (h.timeDiff t ht x).neg
  equation_le t ht x := by
    have htcarrier : t ∈ D.carrier := D.regular_subset ht
    have husmooth := h.sliceSmooth t htcarrier
    have hlaplacian := laplacianAt_smul (I := I) G t (-1)
      (fun y => husmooth.mdifferentiable (by simp) y)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) husmooth x)
    have hfun : (fun y : M => -u t y) = (-1 : Real) • u t := by
      funext y
      simp
    have hderiv : deriv (fun s => -u s x) t =
        -deriv (fun s => u s x) t := by
      simpa only using (h.timeDiff t ht x).hasDerivAt.neg.deriv
    rw [hfun, hlaplacian, hderiv]
    linarith [h.equation_ge t ht x]

end IsHeatPotSupersolutionOn

namespace IsHeatPotSubsolutionOn

theorem mono
    {D D' : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotSubsolutionOn D G V u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatPotSubsolutionOn D' G V u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  timeDiff t ht x := h.timeDiff t (hregular ht) x
  equation_le t ht x := h.equation_le t (hregular ht) x

theorem neg
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotSubsolutionOn D G V u) :
    IsHeatPotSupersolutionOn D G V (fun t x => -u t x) where
  jointSmooth := h.jointSmooth.neg
  jointCont := h.jointCont.neg
  sliceSmooth t ht := (h.sliceSmooth t ht).neg
  timeDiff t ht x := (h.timeDiff t ht x).neg
  equation_ge t ht x := by
    have htcarrier : t ∈ D.carrier := D.regular_subset ht
    have husmooth := h.sliceSmooth t htcarrier
    have hlaplacian := laplacianAt_smul (I := I) G t (-1)
      (fun y => husmooth.mdifferentiable (by simp) y)
      (DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt
        (I := I) (G.metric t) husmooth x)
    have hfun : (fun y : M => -u t y) = (-1 : Real) • u t := by
      funext y
      simp
    have hderiv : deriv (fun s => -u s x) t =
        -deriv (fun s => u s x) t := by
      simpa only using (h.timeDiff t ht x).hasDerivAt.neg.deriv
    rw [hfun, hlaplacian, hderiv]
    linarith [h.equation_le t ht x]

end IsHeatPotSubsolutionOn

end

end DifferentialGeometry.Analysis.Parabolic
