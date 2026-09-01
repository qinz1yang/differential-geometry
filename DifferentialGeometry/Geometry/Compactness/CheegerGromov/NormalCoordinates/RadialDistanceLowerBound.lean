import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DistanceComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.FramedMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCoveringSeq
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology

section PathBridge

open Set Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

section General
variable {F : Type uE} [NormedAddCommGroup F] [NormedSpace Real F]
variable [FiniteDimensional Real F]
variable [NeZero (Module.finrank Real F)] [CompleteSpace F]
variable {G : Type uH} [TopologicalSpace G]
variable {J' : ModelWithCorners Real F G} [J'.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ F)] in
theorem edistLeOfEquivOn (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U)
    (γ : ℝ → Y.M)
    (hγ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      ContMDiffOn 𝓘(ℝ, ℝ) J' 1 γ (Set.Icc (0 : ℝ) 1))
    (hend : γ 0 = x)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
        = ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v))) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace G Y.M := Y.charted
    letI : IsManifold J' ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    Manifold.riemannianEDist J' x (γ 1)
      ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace G Y.M := Y.charted
  let : IsManifold J' ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have h1 : Manifold.riemannianEDist J' x (γ 1) ≤ Manifold.pathELength J' γ 0 1 :=
    Manifold.riemannianEDist_le_pathELength hγ hend rfl zero_le_one
  refine h1.trans ?_
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
    intro t ht
    rw [hderiv t ht]
    refine ENNReal.ofReal_le_ofReal ?_
    have hub := (heq (t • v) (hseg t ht) v).2
    calc Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v)
        ≤ Real.sqrt (2 * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hub
      _ = Real.sqrt 2 * ‖v‖ := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg v)]
  calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt 2 * ‖v‖) :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) * MeasureTheory.volume (Set.Icc (0 : ℝ) 1) :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
        rw [Real.volume_Icc]
        norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ F)] in
theorem normLowerOfSep (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U)
    (γ : ℝ → Y.M)
    (hγ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      ContMDiffOn 𝓘(ℝ, ℝ) J' 1 γ (Set.Icc (0 : ℝ) 1))
    (hend : γ 0 = x)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
        = ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v)))
    {lam : ℝ}
    (hlam :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x (γ 1)) :
    lam / Real.sqrt 2 ≤ ‖v‖ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace G Y.M := Y.charted
  let : IsManifold J' ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hup := edistLeOfEquivOn (J' := J') Y x heq hseg γ hγ hend hderiv
  have hchain : ENNReal.ofReal lam ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := hlam.trans hup
  have hle : lam ≤ Real.sqrt 2 * ‖v‖ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)]
  linarith [hle]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real F)] in
theorem normLowerOfSepExp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace G Y.M := Y.charted
    letI : IsManifold J' ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    U ⊆ Metric.ball (0 : F) (expMapC2Radius (I := J') Y.metric x) →
    ∀ {lam : ℝ},
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x
        (expMap (I := J') Y.metric x (show TangentSpace J' x from v)) →
      lam / Real.sqrt 2 ≤ ‖v‖ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace G Y.M := Y.charted
  let : IsManifold J' ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro hsub lam hlam
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖t • v‖ < expMapC2Radius (I := J') Y.metric x := by
    intro t ht
    simpa only [Metric.mem_ball, dist_zero_right] using hsub (hseg t ht)
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J' 1
      (fun t : ℝ => (expMap (I := J') Y.metric x
        (show TangentSpace J' x from (t • v)) : Y.M)) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (radialCurve_contMDiffAt2 (I := J') Y.metric x v t
      (hsmall t ht)).contMDiffWithinAt.of_le (by norm_num)
  have hend :
      (expMap (I := J') Y.metric x
        (show TangentSpace J' x from ((0 : ℝ) • v)) : Y.M) = x := by
    rw [zero_smul]
    exact expMap_zero (I := J') Y.metric x
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) J'
        (fun s : ℝ => (expMap (I := J') Y.metric x
          (show TangentSpace J' x from (s • v)) : Y.M)) t 1‖ₑ =
        ENNReal.ofReal (Real.sqrt
          (normalCoordMetric (I := J') Y x (t • v) v v)) := by
    intro t ht
    exact radial_enorm_normal (I := J') Y x v t (hsmall t ht)
  apply normLowerOfSep (J' := J') Y x heq hseg _ hcurve hend hderiv
  simpa only [one_smul] using hlam

end General

section IntrinsicSequence

variable {F : Type uE} [NormedAddCommGroup F]
variable [InnerProductSpace Real F] [FiniteDimensional Real F]
variable [NeZero (Module.finrank Real F)] [CompleteSpace F]
variable {G : Type uH} [TopologicalSpace G]
variable {J' : ModelWithCorners Real F G} [J'.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem seqChartNorm_ge
    {Z : PointedRiemannianSeq.{u, uE, uH} (I := J')}
    (hd : InjRadiusDecayInput (I := J') Z) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := J') (Z.obj k)) (k : Nat) {α : Nat}
    (hα : α ≠ 0) {c : (Z.obj k).M}
    (hc : seqCenter (I := J') (X := Z) hd D P k α = some c)
    {U : Set F} (heq : NormalCoordMetricEquivOn (I := J') (Z.obj k) c U) :
    letI : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
    letI : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
    letI : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
    letI : T2Space (TangentBundle J' (Z.obj k).M) :=
      (Z.obj k).t2TangentBundle
    letI : RiemannianBundle
        (fun y : (Z.obj k).M => TangentSpace J' y) :=
      ⟨(Z.obj k).metric.toRiemannianMetric⟩
    (Z.obj k).basepoint ∈
        (NormalCoordinates.normalChartAt (I := J')
          (Z.obj k).metric c).source →
    (∀ t : Real, t ∈ Set.Icc (0 : Real) 1 →
      t • NormalCoordinates.normalChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint ∈ U) →
    U ⊆ Metric.ball (0 : F)
      (expMapC2Radius (I := J') (Z.obj k).metric c) →
    hd.lambda D 0 / Real.sqrt 2 ≤
      ‖NormalCoordinates.normalChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint‖ := by
  let : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
  let : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
  let : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
  let : T2Space (TangentBundle J' (Z.obj k).M) :=
    (Z.obj k).t2TangentBundle
  let : RiemannianBundle
      (fun y : (Z.obj k).M => TangentSpace J' y) :=
    ⟨(Z.obj k).metric.toRiemannianMetric⟩
  intro hbase hseg hsub
  have hvsrc :
      NormalCoordinates.normalChartAt (I := J') (Z.obj k).metric c
          (Z.obj k).basepoint ∈
        (NormalCoordinates.expMapDiffeo (I := J')
          (Z.obj k).metric c).source :=
    (NormalCoordinates.normalChartAt (I := J')
      (Z.obj k).metric c).map_source hbase
  have hexp :
      (expMap (I := J') (Z.obj k).metric c
        (show TangentSpace J' c from
          NormalCoordinates.normalChartAt (I := J') (Z.obj k).metric c
            (Z.obj k).basepoint) : (Z.obj k).M) =
          (Z.obj k).basepoint := by
    rw [← NormalCoordinates.expMapDiffeo_apply_eq
      (I := J') (Z.obj k).metric c hvsrc]
    exact NormalCoordinates.normalChartAt_left_inv
      (I := J') (Z.obj k).metric c hbase
  have hsep : ENNReal.ofReal (hd.lambda D 0) ≤
      Manifold.riemannianEDist J' c (Z.obj k).basepoint := by
    have h := seqCenter_edist_ge (I := J') (X := Z) hd hD P k hα hc
    change ENNReal.ofReal (hd.lambda D 0) ≤
      (letI : EMetricSpace (Z.obj k).M := (Z.obj k).emetricSpace
       edist c (Z.obj k).basepoint)
    exact h
  rw [← hexp] at hsep
  exact normLowerOfSepExp (J' := J') (Z.obj k) c heq hseg hsub hsep

end IntrinsicSequence

variable {F : Type uE} [NormedAddCommGroup F]
variable [InnerProductSpace Real F] [FiniteDimensional Real F]
variable [NeZero (Module.finrank Real F)] [CompleteSpace F]
variable {G : Type uH} [TopologicalSpace G]
variable {J' : ModelWithCorners Real F G} [J'.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ F)] in
theorem normLowerOfSepFramed
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : FramedCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U)
    (γ : ℝ → Y.M)
    (hγ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      ContMDiffOn 𝓘(ℝ, ℝ) J' 1 γ (Set.Icc (0 : ℝ) 1))
    (hend : γ 0 = x)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ =
        ENNReal.ofReal
          (Real.sqrt (framedCoordMetric (I := J') Y x (t • v) v v)))
    {lam : ℝ}
    (hlam :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x (γ 1)) :
    lam / Real.sqrt 2 ≤ ‖v‖ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace G Y.M := Y.charted
  let : IsManifold J' ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have h1 : Manifold.riemannianEDist J' x (γ 1) ≤
      Manifold.pathELength J' γ 0 1 :=
    Manifold.riemannianEDist_le_pathELength hγ hend rfl zero_le_one
  have hup : Manifold.riemannianEDist J' x (γ 1) ≤
      ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
    refine h1.trans ?_
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ ≤
          ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
      intro t ht
      rw [hderiv t ht]
      refine ENNReal.ofReal_le_ofReal ?_
      have hub := (heq (t • v) (hseg t ht) v).2
      calc
        Real.sqrt (framedCoordMetric (I := J') Y x (t • v) v v) ≤
            Real.sqrt (2 * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hub
        _ = Real.sqrt 2 * ‖v‖ := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_sq (norm_nonneg v)]
    calc
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ ≤
          ∫⁻ _ in Set.Icc (0 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt 2 * ‖v‖) :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc hpt
      _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) *
          MeasureTheory.volume (Set.Icc (0 : ℝ) 1) :=
        MeasureTheory.setLIntegral_const _ _
      _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
        rw [Real.volume_Icc]
        norm_num
  have hchain : ENNReal.ofReal lam ≤
      ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := hlam.trans hup
  have hle : lam ≤ Real.sqrt 2 * ‖v‖ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)]
  linarith [hle]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normLowerOfSepFramedExp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : FramedCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace G Y.M := Y.charted
    letI : IsManifold J' ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    U ⊆ Metric.ball (0 : F) (expRadiusGp (I := J') Y.metric x) →
    ∀ {lam : ℝ},
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x
        (expMap (I := J') Y.metric x
          (show TangentSpace J' x from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) →
      lam / Real.sqrt 2 ≤ ‖v‖ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace G Y.M := Y.charted
  let : IsManifold J' ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro hsub lam hlam
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖t • v‖ < expRadiusGp (I := J') Y.metric x := by
    intro t ht
    simpa only [Metric.mem_ball, dist_zero_right] using hsub (hseg t ht)
  have hraw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖t • (show F from
        NormalCoordinates.normalFrame (I := J') Y.metric x v)‖ <
          expMapC2Radius (I := J') Y.metric x := by
    intro t ht
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := J') Y.metric x
    have hframe : t • (show F from
        NormalCoordinates.normalFrame (I := J') Y.metric x v) =
        (show F from
          NormalCoordinates.normalFrame (I := J') Y.metric x (t • v)) := by
      exact (map_smul
        (NormalCoordinates.normalFrame (I := J') Y.metric x) t v).symm
    rw [hframe, NormalCoordinates.normalFrame_sqrt]
    exact hsmall t ht
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J' 1
      (fun t : ℝ => (expMap (I := J') Y.metric x
        (show TangentSpace J' x from
          t • (show F from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M))
        (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (radialCurve_contMDiffAt2 (I := J') Y.metric x
      (show F from NormalCoordinates.normalFrame (I := J') Y.metric x v)
      t (hraw t ht)).contMDiffWithinAt.of_le
      (by norm_num)
  have hend :
      (expMap (I := J') Y.metric x
        (show TangentSpace J' x from
          (0 : ℝ) • (show F from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M) = x := by
    rw [zero_smul]
    exact expMap_zero (I := J') Y.metric x
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) J'
        (fun s : ℝ => (expMap (I := J') Y.metric x
          (show TangentSpace J' x from
            s • (show F from
              NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M)) t 1‖ₑ =
        ENNReal.ofReal
          (Real.sqrt (framedCoordMetric (I := J') Y x (t • v) v v)) := by
    intro t ht
    exact radialEnorm_framed (I := J') Y x v t (hsmall t ht)
  apply normLowerOfSepFramed (J' := J') Y x heq hseg _ hcurve hend hderiv
  rw [one_smul]
  exact hlam

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem seqFramedChartNorm_ge
    {Z : PointedRiemannianSeq.{u, uE, uH} (I := J')}
    (hd : InjRadiusDecayInput (I := J') Z) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := J') (Z.obj k)) (k : Nat) {α : Nat}
    (hα : α ≠ 0) {c : (Z.obj k).M}
    (hc : seqCenter (I := J') (X := Z) hd D P k α = some c)
    {U : Set F} (heq : FramedCoordMetricEquivOn (I := J') (Z.obj k) c U) :
    letI : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
    letI : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
    letI : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
    letI : T2Space (TangentBundle J' (Z.obj k).M) := (Z.obj k).t2TangentBundle
    letI : RiemannianBundle (fun y : (Z.obj k).M => TangentSpace J' y) :=
      ⟨(Z.obj k).metric.toRiemannianMetric⟩
    (Z.obj k).basepoint ∈
        (NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c).source →
    (∀ t : Real, t ∈ Set.Icc (0 : Real) 1 →
      t • NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint ∈ U) →
    U ⊆ Metric.ball (0 : F) (expRadiusGp (I := J') (Z.obj k).metric c) →
    hd.lambda D 0 / Real.sqrt 2 ≤
      ‖NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint‖ := by
  let : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
  let : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
  let : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
  let : T2Space (TangentBundle J' (Z.obj k).M) := (Z.obj k).t2TangentBundle
  let : RiemannianBundle (fun y : (Z.obj k).M => TangentSpace J' y) :=
    ⟨(Z.obj k).metric.toRiemannianMetric⟩
  intro hbase hseg hsub
  have hvsrc :
      NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
          (Z.obj k).basepoint ∈
        (NormalCoordinates.framedExpDiffeo (I := J')
          (Z.obj k).metric c).source :=
    (NormalCoordinates.framedChartAt (I := J')
      (Z.obj k).metric c).map_source hbase
  have hexp :
      (expMap (I := J') (Z.obj k).metric c
        (show TangentSpace J' c from
          NormalCoordinates.normalFrame (I := J') (Z.obj k).metric c
            (NormalCoordinates.framedChartAt (I := J')
              (Z.obj k).metric c (Z.obj k).basepoint)) : (Z.obj k).M) =
          (Z.obj k).basepoint := by
    rw [← NormalCoordinates.framedExpMap_apply]
    rw [← NormalCoordinates.framedExp_eq_expMap
      (I := J') (Z.obj k).metric c hvsrc]
    exact (NormalCoordinates.framedExpDiffeo (I := J')
      (Z.obj k).metric c).right_inv hbase
  have hsep : ENNReal.ofReal (hd.lambda D 0) ≤
      Manifold.riemannianEDist J' c (Z.obj k).basepoint := by
    have h := seqCenter_edist_ge (I := J') (X := Z) hd hD P k hα hc
    change ENNReal.ofReal (hd.lambda D 0) ≤
      (letI : EMetricSpace (Z.obj k).M := (Z.obj k).emetricSpace
       edist c (Z.obj k).basepoint)
    exact h
  rw [← hexp] at hsep
  exact normLowerOfSepFramedExp (J' := J') (Z.obj k) c heq hseg hsub hsep

end PathBridge

end HCGCompactness
end DifferentialGeometry
