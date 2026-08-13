import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.BoundaryHopf
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem heat_pot_hopf_boundary_point_of_subsolution_barrier
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval} {V u v : Real → M → Real}
    (hu : IsHeatPotSupersolutionOn D G V u)
    (hv : IsHeatPotSubsolutionOn D G V v)
    {T : Real} (hT : 0 < T)
    (hcarrier : Set.Icc 0 T ⊆ D.carrier)
    (hregular : Set.Ioc 0 T ⊆ D.regular)
    (hV : ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ I.interior M, V t x ≤ 0)
    (hinit : ∀ x : M, v 0 x ≤ u 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ q : BoundaryManifold I M,
      v t (q : M) ≤ u t (q : M))
    {p : BoundaryManifold I M}
    (heq : u T (p : M) = v T (p : M))
    (hv_inward : 0 < (G.metric T).inner (p : M)
      (gradientFun (I := I) (G.metric T) (v T) (p : M))
      (inwardCoord (M := M) p))
    (hmin : IsLocalMin
      (fun q : BoundaryManifold I M ↦ u T (q : M)) p) :
    outwardNormalDerivative (M := M) (G.metric T) (u T) p < 0 := by
  let w : Real → M → Real := fun t x ↦ u t x - v t x
  let X : Real → (x : M) → TangentSpace I x := fun _ x ↦ 0
  have hw : IsHeatPotSupersolutionOn D G V w := hu.sub hv
  have hwcont : ContinuousOn (fun q : Real × M ↦ w q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    exact hw.jointCont.mono (Set.prod_mono hcarrier Set.Subset.rfl)
  have hwtime : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s ↦ w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x _hx
    exact (hw.timeDiff t (hregular ⟨htpos, ht.2⟩) x).differentiableWithinAt
  have hwspace : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht _htpos x _hx
    exact (hw.sliceSmooth t (hcarrier ht)).mdifferentiable (by simp) x
  have hwgrad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M ↦
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht _htpos x _hx
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (hw.sliceSmooth t (hcarrier ht)) x
  have hwoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      w t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hx hwneg
    have htregular : t ∈ D.regular := hregular ⟨htpos, ht.2⟩
    have hdiff := hw.timeDiff t htregular x
    have hderiv : derivWithin (fun s ↦ w s x) (Set.Icc 0 T) t =
        deriv (fun s ↦ w s x) t :=
      hdiff.hasDerivAt.hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
    have hpot : 0 ≤ V t x * w t x :=
      mul_nonneg_of_nonpos_of_nonpos (hV t ⟨htpos, ht.2⟩ x hx) hwneg.le
    have heqge := hw.equation_ge t htregular x
    unfold parabolicOperatorWithDrift heatOperatorWithDrift X
    rw [hderiv]
    simp only [driftTerm_zero_drift, add_zero]
    linarith
  have hTcarrier : T ∈ D.carrier := hcarrier ⟨hT.le, le_rfl⟩
  exact scalar_hopf_boundary_point_of_barrier_with_boundary
    (I := I) G T hT.le X u v
    (by simpa only [w] using hwcont)
    (fun x ↦ sub_nonneg.mpr (hinit x))
    (fun t ht q ↦ sub_nonneg.mpr (hboundary t ht q))
    (by simpa only [w] using hwtime)
    (by simpa only [w] using hwspace)
    (by simpa only [w] using hwgrad)
    (by simpa only [w] using hwoperator)
    heq
    ((hu.sliceSmooth T hTcarrier).mdifferentiable (by simp) (p : M))
    ((hv.sliceSmooth T hTcarrier).mdifferentiable (by simp) (p : M))
    hv_inward hmin

theorem heat_hopf_boundary_point_of_subsolution_barrier
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval} {u v : Real → M → Real}
    (hu : IsHeatSupersolutionOn D G u)
    (hv : IsHeatSubsolutionOn D G v)
    {T : Real} (hT : 0 < T)
    (hcarrier : Set.Icc 0 T ⊆ D.carrier)
    (hregular : Set.Ioc 0 T ⊆ D.regular)
    (hinit : ∀ x : M, v 0 x ≤ u 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ q : BoundaryManifold I M,
      v t (q : M) ≤ u t (q : M))
    {p : BoundaryManifold I M}
    (heq : u T (p : M) = v T (p : M))
    (hv_inward : 0 < (G.metric T).inner (p : M)
      (gradientFun (I := I) (G.metric T) (v T) (p : M))
      (inwardCoord (M := M) p))
    (hmin : IsLocalMin
      (fun q : BoundaryManifold I M ↦ u T (q : M)) p) :
    outwardNormalDerivative (M := M) (G.metric T) (u T) p < 0 := by
  exact heat_pot_hopf_boundary_point_of_subsolution_barrier
    (I := I) G hu hv hT hcarrier hregular (by simp) hinit hboundary
    heq hv_inward hmin

end

end DifferentialGeometry.Analysis.Parabolic
