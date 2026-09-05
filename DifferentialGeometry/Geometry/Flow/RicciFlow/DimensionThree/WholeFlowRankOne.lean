import DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.DimensionThree

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Integral.Measure
open scoped Manifold _root_.Topology ContDiff InnerProductSpace BigOperators

variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
variable [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [LocallyPathConnectedSpace M]
variable [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
variable [Inhabited M]

structure WholeFlowRankOneProductData
    (g : Real → SmoothRiemannianMetric I M) where
  N : Type
  [topologyN : TopologicalSpace N]
  [chartedN : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [manifoldN : IsManifold
    (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
  [t2N : T2Space N]
  surfaceMetric : Real → SmoothRiemannianMetric
    (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) N
  F : Diffeomorph
    ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
      𝓘(Real, Real)) I (N × Real)
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (↑(⊤ : ℕ∞) : WithTop ℕ∞)
  horizontal_inner : ∀ (t : Real) (y : N) (s : Real)
      (u v : TangentSpace
        (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) y),
    (liftedMetric (I := I) (g t)).inner (F (y, s))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (u, 0))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (v, 0)) =
      (surfaceMetric t).inner y u v
  vertical_inner : ∀ (t : Real) (y : N) (s r q : Real),
    (liftedMetric (I := I) (g t)).inner (F (y, s))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (0, r))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (0, q)) = r * q
  mixed_inner : ∀ (t : Real) (y : N) (s : Real)
      (u : TangentSpace
        (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) y)
      (r : Real),
    (liftedMetric (I := I) (g t)).inner (F (y, s))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (u, 0))
        ((mfderiv
          ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (0, r)) = 0

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [Nonempty M] in
theorem whole_flow_rank_one_product_identity
    (g : Real → SmoothRiemannianMetric I M)
    (data : WholeFlowRankOneProductData (I := I) (M := M) g) :
    let _ : TopologicalSpace data.N := data.topologyN
    let _ : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel 2) data.N := data.chartedN
    let _ : IsManifold
        (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
    let _ : T2Space data.N := data.t2N
    ∀ t : Real,
      Diffeomorph.pullbackMetricCross
          (I := (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(Real, Real))
          (J := I) (liftedMetric (I := I) (g t)) data.F =
        (data.surfaceMetric t).prod (flatModelMetric Real) := by
  dsimp
  let _ : TopologicalSpace data.N := data.topologyN
  let _ : ChartedSpace
      (DifferentialGeometry.Topology.Morse.MorseModel 2) data.N := data.chartedN
  let _ : IsManifold
      (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
  let _ : T2Space data.N := data.t2N
  intro t
  apply SmoothRiemannianMetric.ext_inner
  intro z u v
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [SmoothRiemannianMetric.prod_inner]
  have hfst (w : TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z) :
      (mfderiv ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)
        Prod.fst z) w = w.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd (w : TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z) :
      (mfderiv ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) 𝓘(Real, Real) Prod.snd z) w = w.2 := by
    rw [mfderiv_snd]
    rfl
  rw [hfst u, hfst v, hsnd u, hsnd v]
  have hu : u =
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (u.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, u.2)) := by
    change u = (show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from
      (((show TangentSpace
          (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) z.1 from u.1),
          (0 : TangentSpace 𝓘(Real, Real) z.2)) +
        ((0 : TangentSpace
          (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) z.1),
          (show TangentSpace 𝓘(Real, Real) z.2 from u.2))))
    apply Prod.ext
    · change u.1 = u.1 +
        (0 : DifferentialGeometry.Topology.Morse.MorseModel 2)
      rw [add_zero]
    · change u.2 = (0 : Real) + u.2
      rw [zero_add]
  have hv : v =
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (v.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, v.2)) := by
    change v = (show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from
      (((show TangentSpace
          (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) z.1 from v.1),
          (0 : TangentSpace 𝓘(Real, Real) z.2)) +
        ((0 : TangentSpace
          (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) z.1),
          (show TangentSpace 𝓘(Real, Real) z.2 from v.2))))
    apply Prod.ext
    · change v.1 = v.1 +
        (0 : DifferentialGeometry.Topology.Morse.MorseModel 2)
      rw [add_zero]
    · change v.2 = (0 : Real) + v.2
      rw [zero_add]
  rw [hu, hv]
  rw [(mfderiv
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) z).map_add]
  rw [(mfderiv
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) z).map_add]
  have hufst : ((show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from (u.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, u.2))).1 = u.1 := by
    change u.1 + (0 : DifferentialGeometry.Topology.Morse.MorseModel 2) = u.1
    rw [add_zero]
  have husnd : ((show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from (u.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, u.2))).2 = u.2 := by
    change (0 : Real) + u.2 = u.2
    rw [zero_add]
  have hvfst : ((show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from (v.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, v.2))).1 = v.1 := by
    change v.1 + (0 : DifferentialGeometry.Topology.Morse.MorseModel 2) = v.1
    rw [add_zero]
  have hvsnd : ((show TangentSpace
      ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
        𝓘(Real, Real)) z from (v.1, 0)) +
      (show TangentSpace
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(Real, Real)) z from (0, v.2))).2 = v.2 := by
    change (0 : Real) + v.2 = v.2
    rw [zero_add]
  rw [hufst, husnd, hvfst, hvsnd]
  have hinner_add_left (a b c : TangentSpace I (data.F z)) :
      (liftedMetric (I := I) (g t)).inner (data.F z) (a + b) c =
        (liftedMetric (I := I) (g t)).inner (data.F z) a c +
          (liftedMetric (I := I) (g t)).inner (data.F z) b c := by
    rw [map_add, add_apply]
  have hinner_add_right (a b c : TangentSpace I (data.F z)) :
      (liftedMetric (I := I) (g t)).inner (data.F z) a (b + c) =
        (liftedMetric (I := I) (g t)).inner (data.F z) a b +
          (liftedMetric (I := I) (g t)).inner (data.F z) a c := by
    exact ContinuousLinearMap.map_add
      ((liftedMetric (I := I) (g t)).inner (data.F z) a) b c
  rw [hinner_add_left, hinner_add_right, hinner_add_right]
  have hhh := data.horizontal_inner t z.1 z.2 u.1 v.1
  have hvv := data.vertical_inner t z.1 z.2 u.2 v.2
  have hmh := data.mixed_inner t z.1 z.2 u.1 v.2
  have hmv := data.mixed_inner t z.1 z.2 v.1 u.2
  have hmv' :
      (liftedMetric (I := I) (g t)).inner (data.F z)
          ((mfderiv
            ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) z)
            (0, u.2))
          ((mfderiv
            ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) z)
            (v.1, 0)) = 0 := by
    rw [(liftedMetric (I := I) (g t)).symm]
    exact hmv
  rw [hhh, hvv, hmh, hmv']
  have hflat : (flatModelMetric Real).inner z.2 u.2 v.2 = u.2 * v.2 := by
    change inner Real u.2 v.2 = _
    rw [RCLike.inner_apply]
    simp
    ring
  rw [hflat]
  ring

end DifferentialGeometry.PDE.RicciFlow.DimensionThree

end
