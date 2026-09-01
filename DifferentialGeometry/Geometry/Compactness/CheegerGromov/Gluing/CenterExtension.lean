import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricBounds
import DifferentialGeometry.Analysis.Calculus.MovingImplicit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Averaging

import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Smoothness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.InverseDistance
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential


variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

noncomputable def centerCfgOn
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r) :
    ((ι -> Real) × (ι -> E)) -> M :=
  centerAverageOn (I := I) g V (fun params => params.1)
    (fun params i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
    join (fun _ => p) (fun _ => r) (fun _ => p) h

noncomputable def chartCenterOn
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    (params : (ι -> Real) × (ι -> E)) : E :=
  NormalCoordinates.normalChartAt (I := I) g p (centerCfgOn (I := I) g p join r V h params)

theorem centerCfgOn_eq
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    {V : Set ((ι -> Real) × (ι -> E))}
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    {params : (ι -> Real) × (ι -> E)} (hparams : params ∈ V) :
    centerCfgOn (I := I) g p join r V h params =
      centerOfMass (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r (h params hparams) := by
  exact centerAverage.on_eq (I := I) (g := g)
    (μ := fun q : (ι -> Real) × (ι -> E) => q.1)
    (pts := fun q i => (NormalCoordinates.normalChartAt (I := I) g p).symm (q.2 i))
    (join := join) (p := fun _ => p) (r := fun _ => r) (qstar := fun _ => p)
    h hparams

section SmoothDomain

variable [hRiemannianBundle : RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem centerReadoutB_zero
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (mu : ι -> Real) (xi : ι -> E)
    (join : M -> M -> Real -> M) (r : Real)
    (h : CenterInput (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r)
    (hcenter : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(Real, Real)
        (CenterOfMass.halfSqDist
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)))
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)).source)
    (hsmall :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ≠
          centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h ->
        Real.sqrt
          (g.inner
            (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)) <
          centerOfMass.eqnRadius (I := I) h)
    (hread : ∀ i,
      (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) ∈ B.readDom)
    (hreal : ∀ i,
      Real.sqrt
        (g.inner
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)
          (B.inv
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd
          (B.inv
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd) <
        expDiffeoRadius (I := I) g hEnorm
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)) :
    chartCmEqnB (I := I) g hEnorm p B
      (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g mu
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
          join p r h))
      (mu, xi) = 0 := by
  let c := centerOfMass (I := I) g mu
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    join p r h
  obtain ⟨i₀, _⟩ := h.μ_pos
  have hbase : c ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    with_unfolding_all exact (hread i₀).2
  have hpt (i : ι) :
      B.inv (c, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) =
        (⟨c, (show TangentSpace I c from
          (NormalCoordinates.normalChartAt (I := I) g c
            ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E))⟩ :
          TangentBundle I M) := by
    exact B.inv_eq_normal_lt (hread i).1 (hreal i)
  have hbook := centerOfMass.expInv_eqn_of_lt (I := I) h hdiff hsrc hsmall
  have hreadout := (readoutB_zero_iff (I := I) g hEnorm p B mu c
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    hbase hpt).2 hbook
  have hdecode : (NormalCoordinates.normalChartAt (I := I) g p).symm
      (NormalCoordinates.normalChartAt (I := I) g p c) = c :=
    (NormalCoordinates.normalChartAt (I := I) g p).left_inv hcenter
  unfold chartCmEqnB
  rw [hdecode]
  exact hreadout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem centerReadout_zero
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι] (mu : ι -> Real) (xi : ι -> E)
    (join : M -> M -> Real -> M) (r : Real)
    (h : CenterInput (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r)
    (hcenter : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(Real, Real)
        (CenterOfMass.halfSqDist
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)))
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)).source)
    (hsmall :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ≠
          centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h ->
        Real.sqrt
          (g.inner
            (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)) <
          centerOfMass.eqnRadius (I := I) h)
    (hbase : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hproj : ∀ i,
      (diagExpInv (I := I) g hEnorm p
        (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h,
          (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).proj =
        centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h)
    (hintr : ∀ i,
      expMapIntrinsic (I := I) g hEnorm
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h)
        (diagExpInv (I := I) g hEnorm p
          (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd =
          (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    (hreal : ∀ i,
      Real.sqrt
        (g.inner
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)
          (diagExpInv (I := I) g hEnorm p
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd
          (diagExpInv (I := I) g hEnorm p
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd) <
        expDiffeoRadius (I := I) g hEnorm
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)) :
    chartCmEqn' (I := I) g hEnorm p
      (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g mu
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
          join p r h))
      (mu, xi) = 0 := by
  let c := centerOfMass (I := I) g mu
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    join p r h
  have hbook := centerOfMass.expInv_eqn_of_lt (I := I) h hdiff hsrc hsmall
  have hpt (i : ι) := diagInv_eq_normal_lt (I := I) g hEnorm p c
    ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    (hproj i) (hintr i) (hreal i)
  have hreadout := (readout_sum_eq_zero_iff (I := I) g hEnorm p mu c
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    hbase hpt).2 hbook
  have hdecode : (NormalCoordinates.normalChartAt (I := I) g p).symm
      (NormalCoordinates.normalChartAt (I := I) g p c) = c :=
    (NormalCoordinates.normalChartAt (I := I) g p).left_inv hcenter
  unfold chartCmEqn'
  rw [hdecode]
  exact hreadout

omit [T3Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem existsCmExtensionB
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (D : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι]
    {A B : Set ((ι -> Real) × (ι -> E))} (hA : IsCompact A) (hAB : A ⊆ B)
    (c : ((ι -> Real) × (ι -> E)) -> E) (hc : ContinuousOn c B)
    (hzero : ∀ params ∈ B,
      chartCmEqnB (I := I) g hEnorm p D (c params) params = 0)
    (hjoint : ∀ params ∈ A, ContDiffAt Real 1
      (fun w : E × ((ι -> Real) × (ι -> E)) =>
        chartCmEqnB (I := I) g hEnorm p D w.1 w.2) (c params, params))
    (hinv : ∀ params ∈ A, ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqnB (I := I) g hEnorm p D z params)
        (L : E →L[Real] E) (c params)) :
    ∃ (T : Set (E × ((ι -> Real) × (ι -> E))))
        (V : Set ((ι -> Real) × (ι -> E)))
        (z : ((ι -> Real) × (ι -> E)) -> E),
      IsOpen T ∧ IsOpen V ∧
      (∀ params ∈ A, (c params, params) ∈ T) ∧
      Set.InjOn
        (fun w : E × ((ι -> Real) × (ι -> E)) =>
          (chartCmEqnB (I := I) g hEnorm p D w.1 w.2, w.2)) T ∧
      A ⊆ V ∧ ContinuousOn z V ∧
      (∀ params ∈ V, chartCmEqnB (I := I) g hEnorm p D (z params) params = 0) ∧
      Set.EqOn z c (B ∩ V) := by
  apply Analysis.exists_root_extension_of_local_homeomorph
    (G := fun z params => chartCmEqnB (I := I) g hEnorm p D z params)
    hA hAB c hc hzero
  intro params hparams
  exact existsPinnedLocal
    (fun z params => chartCmEqnB (I := I) g hEnorm p D z params)
    (c params) params one_ne_zero (hjoint params hparams) (hinv params hparams)

omit [T3Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem existsCmExtension
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι]
    {A B : Set ((ι -> Real) × (ι -> E))} (hA : IsCompact A) (hAB : A ⊆ B)
    (c : ((ι -> Real) × (ι -> E)) -> E) (hc : ContinuousOn c B)
    (hzero : ∀ params ∈ B,
      chartCmEqn' (I := I) g hEnorm p (c params) params = 0)
    (hjoint : ∀ params ∈ A, ContDiffAt Real 1
      (fun w : E × ((ι -> Real) × (ι -> E)) =>
        chartCmEqn' (I := I) g hEnorm p w.1 w.2) (c params, params))
    (hinv : ∀ params ∈ A, ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqn' (I := I) g hEnorm p z params)
        (L : E →L[Real] E) (c params)) :
    ∃ (T : Set (E × ((ι -> Real) × (ι -> E))))
        (V : Set ((ι -> Real) × (ι -> E)))
        (z : ((ι -> Real) × (ι -> E)) -> E),
      IsOpen T ∧ IsOpen V ∧
      (∀ params ∈ A, (c params, params) ∈ T) ∧
      Set.InjOn
        (fun w : E × ((ι -> Real) × (ι -> E)) =>
          (chartCmEqn' (I := I) g hEnorm p w.1 w.2, w.2)) T ∧
      A ⊆ V ∧ ContinuousOn z V ∧
      (∀ params ∈ V, chartCmEqn' (I := I) g hEnorm p (z params) params = 0) ∧
      Set.EqOn z c (B ∩ V) := by
  apply Analysis.exists_root_extension_of_local_homeomorph
    (G := fun z params => chartCmEqn' (I := I) g hEnorm p z params)
    hA hAB c hc hzero
  intro params hparams
  exact existsPinnedLocal
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params)
    (c params) params one_ne_zero (hjoint params hparams) (hinv params hparams)

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem chartCenterOn_cont
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : ∀ params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    (hpts : Continuous (fun params : V => fun i =>
      (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i)))
    (hsrc : ∀ params : V,
      centerOfMass (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r (h params params.2) ∈
          (NormalCoordinates.normalChartAt (I := I) g p).source) :
    ContinuousOn (chartCenterOn (I := I) g p join r V h) V := by
  let _ := hRiemannianBundle
  rw [continuousOn_iff_continuous_domRestrict]
  let H : ∀ params : V,
      CenterInput (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r := fun params => h params params.2
  let f : V -> E := fun params =>
    NormalCoordinates.normalChartAt (I := I) g p
      (centerOfMass (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r (H params))
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro params
    have hμ : Continuous (fun q : V => q.1.1) :=
      continuous_fst.comp continuous_subtype_val
    have hcm := centerOfMass_cont (I := I) g
      (fun q : V => q.1.1)
      (fun q : V => fun i =>
        (NormalCoordinates.normalChartAt (I := I) g p).symm (q.1.2 i))
      join p r params H hμ hpts
    have hchart : ContinuousAt
        (fun q : M => (NormalCoordinates.normalChartAt (I := I) g p q : E))
        (centerOfMass (I := I) g params.1.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm
            (params.1.2 i)) join p r (H params)) :=
      (NormalCoordinates.normalChartAt (I := I) g p).contMDiffOn_toFun.continuousOn.continuousAt
        ((NormalCoordinates.normalChartAt (I := I) g p).open_source.mem_nhds
          (hsrc params))
    exact hchart.tendsto.comp hcm
  have heq : V.domRestrict (chartCenterOn (I := I) g p join r V h) = f := by
    funext params
    change NormalCoordinates.normalChartAt (I := I) g p
      (centerCfgOn (I := I) g p join r V h params) = f params
    rw [centerCfgOn_eq (I := I) g p join r h params.2]
  rw [heq]
  exact hf

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T3Space M] in
omit [ConnectedSpace M] in
theorem cmExtB_contDiffOn
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι]
    (z : ((ι -> Real) × (ι -> E)) -> E)
    {V : Set ((ι -> Real) × (ι -> E))} (hV : IsOpen V)
    (hchz : ∀ params0 ∈ V, forall n : Nat, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z)
      (z params0))
    (hchxi : ∀ params0 ∈ V, forall n : Nat, forall i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun xi : E => (NormalCoordinates.normalChartAt (I := I) g p).symm xi)
      (params0.2 i))
    (hsm : ∀ params0 ∈ V, forall n : Nat, forall i,
      ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
        (fun yq : M × M => B.diagReadout yq)
        ((NormalCoordinates.normalChartAt (I := I) g p).symm (z params0),
          (NormalCoordinates.normalChartAt (I := I) g p).symm (params0.2 i)))
    (hinv : ∀ params0 ∈ V, exists L : E ≃L[Real] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params0)
        (L : E →L[Real] E) (z params0))
    (hzero : ∀ params0 ∈ V,
      chartCmEqnB (I := I) g hEnorm p B (z params0) params0 = 0)
    (hzcont : ContinuousOn z V) :
    ContDiffOn Real (∞ : WithTop ℕ∞) z V := by
  rw [contDiffOn_infty]
  intro n params0 hparams
  have hsolves : ∀ᶠ eventuallyParams in nhds params0,
      chartCmEqnB (I := I) g hEnorm p B (z eventuallyParams) eventuallyParams = 0 := by
    filter_upwards [hV.mem_nhds hparams] with params hparamsV
    exact hzero params hparamsV
  have hcont : Filter.Tendsto z (nhds params0) (nhds (z params0)) :=
    (hzcont.continuousAt (hV.mem_nhds hparams)).tendsto
  obtain ⟨f, _hf0, hfcd, _hfsolves, huniq⟩ :=
    readoutSolB_cdAt (I := I) g hEnorm p B (z params0) params0
      (max 1 n) (le_max_left 1 n)
    (hchz params0 hparams (max 1 n))
    (hchxi params0 hparams (max 1 n))
    (hsm params0 hparams (max 1 n))
    (hinv params0 hparams) (hzero params0 hparams)
  have huniq' := (hcont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : z =ᶠ[nhds params0] f := by
    filter_upwards [huniq', hsolves] with params hu hs
    exact hu hs
  exact ((hfcd.congr_of_eventuallyEq hid).of_le
    (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T3Space M] in
omit [ConnectedSpace M] in
theorem cmExt_contDiffOn
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι]
    (z : ((ι -> Real) × (ι -> E)) -> E)
    {V : Set ((ι -> Real) × (ι -> E))} (hV : IsOpen V)
    (hchz : ∀ params0 ∈ V, forall n : Nat, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z)
      (z params0))
    (hchxi : ∀ params0 ∈ V, forall n : Nat, forall i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun xi : E => (NormalCoordinates.normalChartAt (I := I) g p).symm xi)
      (params0.2 i))
    (hsm : ∀ params0 ∈ V, forall n : Nat, forall i,
      ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
        (fun yq : M × M => (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p yq)).2)
        ((NormalCoordinates.normalChartAt (I := I) g p).symm (z params0),
          (NormalCoordinates.normalChartAt (I := I) g p).symm (params0.2 i)))
    (hinv : ∀ params0 ∈ V, exists L : E ≃L[Real] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params0)
        (L : E →L[Real] E) (z params0))
    (hzero : ∀ params0 ∈ V,
      chartCmEqn' (I := I) g hEnorm p (z params0) params0 = 0)
    (hzcont : ContinuousOn z V) :
    ContDiffOn Real (∞ : WithTop ℕ∞) z V := by
  rw [contDiffOn_infty]
  intro n params0 hparams
  have hsolves : ∀ᶠ eventuallyParams in nhds params0,
      chartCmEqn' (I := I) g hEnorm p (z eventuallyParams) eventuallyParams = 0 := by
    filter_upwards [hV.mem_nhds hparams] with params hparamsV
    exact hzero params hparamsV
  have hcont : Filter.Tendsto z (nhds params0) (nhds (z params0)) :=
    (hzcont.continuousAt (hV.mem_nhds hparams)).tendsto
  obtain ⟨f, _hf0, hfcd, _hfsolves, huniq⟩ :=
    readoutSol_contDiffAt (I := I) g hEnorm p (z params0) params0
      (max 1 n) (le_max_left 1 n)
    (hchz params0 hparams (max 1 n))
    (hchxi params0 hparams (max 1 n))
    (hsm params0 hparams (max 1 n))
    (hinv params0 hparams) (hzero params0 hparams)
  have huniq' := (hcont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : z =ᶠ[nhds params0] f := by
    filter_upwards [huniq', hsolves] with params hu hs
    exact hu hs
  exact ((hfcd.congr_of_eventuallyEq hid).of_le
    (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

end SmoothDomain

end HCGCompactness
end DifferentialGeometry

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem centerReadoutB_min
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {ι : Type} [Fintype ι] (mu : ι → Real) (xi : ι → E)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let pts : ι → (X.obj k).M := fun i ↦
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm (xi i)
    ∀ h : CenterInput (I := I) (X.obj k).metric mu pts join p r,
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ hb.radius k x →
      ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
      let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
      (∀ i, max (riemannianEDist I x c) (riemannianEDist I x (pts i)) <
        ENNReal.ofReal (ρ / 2)) →
      let B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x :=
        IsNormalDiag.toBranch (I := I) (Y := X.obj k)
          (hcomplete := hcomplete) (hconn := hconn) (x := x)
          (q := q) (δ := δ) (e := e) (hq := hq) (h := he)
      chartCmEqnB (I := I) (X.obj k).metric
        (normal_enorm (I := I) (X.obj k)) x B
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c)
        (mu, xi) = 0 := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro h hρ hρq hρmetric hρexp hpairs
  let pts : ι → (X.obj k).M := fun i ↦
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm (xi i)
  let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  change ∀ i, max (riemannianEDist I x c) (riemannianEDist I x (pts i)) <
    ENNReal.ofReal (ρ / 2) at hpairs
  have hdiff (i : ι) : MDifferentiableAt I 𝓘(Real, Real)
      (CenterOfMass.halfSqDist (pts i)) c := by
    let S : Set (X.obj k).M :=
      {z | max (riemannianEDist I x z) (riemannianEDist I x (pts i)) <
        ENNReal.ofReal (ρ / 2)}
    have hSopen : IsOpen S := by
      dsimp only [S]
      exact isOpen_lt
        ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
          continuous_const) continuous_const
    have hsmooth : ContMDiffOn I 𝓘(Real) ∞
        (CenterOfMass.halfSqDist (pts i)) S := by
      simpa only [S] using
        IsNormalDiag.halfSq_inf (I := I) hb k hcomplete hconn x hq he hf
          hρ hρq hρmetric hρexp
    have hcS : c ∈ S := by
      with_unfolding_all exact hpairs i
    exact (hsmooth.contMDiffAt (hSopen.mem_nhds hcS)).mdifferentiableAt (by simp)
  have hgrad (i : ι) :
      gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist (pts i)) c =
        -(show TangentSpace I c from (B.inv (c, pts i)).snd) := by
    simpa only [B] using
      IsNormalDiag.grad_half_inv (I := I) hb k hcomplete hconn x hq he hf
        hρ hρq hρmetric hρexp (hpairs i)
  have hbook : ∑ i : ι, mu i •
      (show TangentSpace I c from (B.inv (c, pts i)).snd) = 0 :=
    centerOfMass.invB_eqn (I := I) h
      (fun i ↦ show TangentSpace I c from (B.inv (c, pts i)).snd) hdiff hgrad
  obtain ⟨i₀, _hi₀⟩ := h.μ_pos
  have hcLt : riemannianEDist I x c < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i₀)
  have hcFin : riemannianEDist I x c ≠ ⊤ :=
    ne_of_lt (hcLt.trans ENNReal.ofReal_lt_top)
  have hcReal : (riemannianEDist I x c).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hcFin).mp hcLt
  have hcSource :=
    (NormalCoordMetricBounds.chart_mem_norm_le (I := I)
      k x c ⟨hcFin, hcReal.trans_le hρexp⟩).1
  have hbase : c ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    apply NormalCoordinates.exp_target_sub_chart (I := I) (X.obj k).metric x
    rwa [← NormalCoordinates.normalChartAt_source_eq]
  have hdom (i : ι) : (c, pts i) ∈ B.dom := by
    exact (IsNormalDiag.inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp (hpairs i)).choose_spec.1
  have hinvBase (i : ι) :
      B.inv (c, pts i) =
        (⟨c, (show TangentSpace I c from (B.inv (c, pts i)).snd)⟩ :
          TangentBundle I (X.obj k).M) := by
    refine Bundle.TotalSpace.ext (B.proj_eq (hdom i)) ?_
    exact heq_of_eq rfl
  have hterm (i : ι) :
      B.diagReadout (c, pts i) =
        (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt Real c hbase
          (show TangentSpace I c from (B.inv (c, pts i)).snd) := by
    unfold DiagInvBranch.diagReadout
    rw [hinvBase i]
    exact congrArg Prod.snd
      ((trivializationAt E (TangentSpace I) x).apply_eq_prod_continuousLinearEquivAt
        Real c hbase _)
  have hreadout : (∑ i : ι, mu i • B.diagReadout (c, pts i)) = 0 := by
    calc
      (∑ i : ι, mu i • B.diagReadout (c, pts i)) =
          (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt Real c hbase
            (∑ i : ι, mu i •
              (show TangentSpace I c from (B.inv (c, pts i)).snd)) := by
        simp_rw [hterm]
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => (map_smul _ (mu i) _).symm)
      _ = (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt Real c hbase 0 :=
        congrArg _ hbook
      _ = 0 := map_zero _
  have hdecode :
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm
          (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c) = c :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).left_inv hcSource
  change chartCmEqnB (I := I) (X.obj k).metric
    (normal_enorm (I := I) (X.obj k)) x B
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c) (mu, xi) = 0
  unfold chartCmEqnB
  rw [hdecode]
  exact hreadout

end HCGCompactness
end DifferentialGeometry
