import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.ActualEvolution
import DifferentialGeometry.Analysis.Calculus.Multilinear
import DifferentialGeometry.Analysis.Calculus.MultilinearPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackTensor
import DifferentialGeometry.Geometry.Connection.Laplacian.CovariantTensor

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem hamiltonP_time_differentiableAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M) :
    DifferentiableAt ℝ (fun s =>
      tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x
        (hamiltonPAt (S.base.metric s) x)) (t : ℝ) := by
  apply ContinuousMultilinearMap.differentiableAt_of_basis_eval (coordinateFrameAtToBasis (I := I) x)
  intro m
  exact ((hamiltonPAt_hasDerivWithinAt_of_ricci_flow S hS t x
    (fun q => coordinateFrameAtToBasis (I := I) x (m q))).hasDerivAt
      (D.regular_mem_nhds t.2)).differentiableAt

private theorem ricciEndAt_metricRicci_eq_ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M) :
    (ricciEndAt g (metricRicci g x)).toContinuousLinearMap = ricciSharp g x := by
  ext v
  apply ricciSharpVec_unique g x v
  intro w
  rw [LinearMap.coe_toContinuousLinearMap', ricciEnd_inner]
  exact metricRicciAt_apply_eq_ricciTensor g x v w

theorem hamiltonP_pullback_hasDerivWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F →L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (S.family.metric t) x (ι t v)) J t)
    (v : Fin 3 → F) :
    HasDerivWithinAt (fun s => hamiltonPAt (S.base.metric s) x (fun q => ι s (v q)))
      (deriv (fun s => hamiltonPAt (S.base.metric s) x (fun q => ι t (v q))) t +
        covariantEndomorphismAction0S (hamiltonPAt (S.base.metric t) x)
          (ricciSharp (S.family.metric t) x) (fun q => ι t (v q))) J t := by
  let A := fun s => tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x
    (hamiltonPAt (S.base.metric s) x)
  have hA : DifferentiableAt ℝ A (t : ℝ) := hamiltonP_time_differentiableAt S hS t x
  have heval := hA.hasDerivAt.continuousMultilinearMap_apply
    (fun q : Fin 3 => hasDerivAt_const (t : ℝ) (ι t (v q)))
  have heval' : deriv (fun s => hamiltonPAt (S.base.metric s) x (fun q => ι t (v q))) t =
      deriv A t (fun q => ι t (v q)) := by
    have hz : ∑ i : Fin 3, A t (Function.update (fun q => ι t (v q)) i 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact (A t).map_coord_zero i (Function.update_self i 0 _)
    have heq := heval.deriv
    rw [hz, add_zero] at heq
    simpa only [A, tensor0SSpaceFiberContinuousLinearEquiv_apply_apply] using heq
  have hd := hA.hasDerivAt.hasDerivWithinAt.continuousMultilinearMap_apply
    (fun q : Fin 3 => hι (v q))
  rw [heval', covariantEndomorphismAction0S_apply]
  exact hd

theorem hamiltonP_pullback_components_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (S.family.metric t) x (ι t v)) J t)
    (basis : Module.Basis (Fin n) ℝ F)
    (horth : ∀ i j, (S.family.metric t).inner x (ι t (basis i)) (ι t (basis j)) =
      if i = j then 1 else 0) (a b c : Fin n) :
    HasDerivWithinAt (fun s => hamiltonPAt (S.base.metric s) x
      (vec3 (ι s (basis a)) (ι s (basis b)) (ι s (basis c))))
      (roughLap0SField (S.family.metric t) (hamiltonPField (S.family.metric t)) x
          (vec3 (ι t (basis a)) (ι t (basis b)) (ι t (basis c))) +
        hamiltonPEvolutionReactionComponent
          (fun i j k l => S.base.rm04 t x
            (vec4 (ι t (basis i)) (ι t (basis j)) (ι t (basis k)) (ι t (basis l))))
          (fun i j => metricRicci (S.family.metric t) x
            (vec2 (ι t (basis i)) (ι t (basis j))))
          (fun i j k l m => nablaRm04Field S t x
            (vec5 (ι t (basis i)) (ι t (basis j)) (ι t (basis k))
              (ι t (basis l)) (ι t (basis m))))
          (fun i j k => metricNablaRic (S.family.metric t) x
            (vec3 (ι t (basis i)) (ι t (basis j)) (ι t (basis k)))) a b c) J t := by
  let B := basis.map (ι t).toLinearEquiv
  have hB : ∀ i j, (S.base.metric t).inner x (B i) (B j) =
      if i = j then 1 else 0 := horth
  have hevol := hamiltonP_fixed_heat_component_of_ricci_flow S hS t x B hB a b c
  dsimp only at hevol
  rw [ricciEndAt_metricRicci_eq_ricciSharp] at hevol
  have hlap : metricTrace0S2TensorInBasis B (identityInvMetric (Idx := Fin n))
      ((CanonicalSpatialDerivs0S.ofSmoothConnection (metricCov (S.base.metric t))
        (metricCov_smooth (S.base.metric t)) (hamiltonPField (S.base.metric t))).nabla2A x) =
      roughLap0SField (S.base.metric t) (hamiltonPField (S.base.metric t)) x := by
    ext tail
    rw [roughLap0SField_apply, roughLap0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (S.base.metric t) B
        (identityInvMetric (Idx := Fin n))
        (metricInverseInBasis_identity_of_orthonormal (S.base.metric t) B hB),
      metricTrace0S2TensorInBasis_apply]
    rfl
  rw [hlap] at hevol
  have hd := hamiltonP_pullback_hasDerivWithinAt S hS t x
    (fun s => (ι s).toContinuousLinearMap) hι
    (![basis a, basis b, basis c])
  have hslots (s : ℝ) : (fun q => ι s (![basis a, basis b, basis c] q)) =
      vec3 (ι s (basis a)) (ι s (basis b)) (ι s (basis c)) := by
    funext q
    fin_cases q <;> rfl
  simp only [ContinuousLinearEquiv.coe_coe, hslots] at hd
  apply hd.congr_deriv
  have hresult := (show ∀ d l r e : ℝ, d - l + r = e → d + r = l + e by
    intro d l r e heq
    linarith only [heq]) _ _ _ _ hevol
  convert hresult using 1 <;> rfl

private theorem hamiltonMOrigin_time_differentiableAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    {n : ℕ} (x : M) (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (horth : ∀ i j, (S.base.metric clock.time).inner x (basis i) (basis j) =
      if i = j then 1 else 0) :
    DifferentiableAt ℝ (fun s =>
      tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
        (hamiltonMOriginField clock.origin s (S.base.metric s) x)) clock.time := by
  let T := fun s => tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
    (hamiltonMOriginField clock.origin s (S.base.metric s) x)
  let R := (ricciEndAt (S.base.metric clock.time)
    (metricRicci (S.base.metric clock.time) x)).toContinuousLinearMap
  let A := fun s : ℝ => ContinuousLinearMap.id ℝ (TangentSpace I x) + (s - clock.time) • R
  have hA : DifferentiableAt ℝ A clock.time := by
    dsimp only [A]
    fun_prop
  have hTA := ContinuousMultilinearMap.differentiableAt_of_basis_eval basis
    (f := fun s => (T s).compContinuousLinearMap (fun _ => A s)) (x := clock.time)
    (fun m => by
    have hm := (hamiltonMAt_hasDerivWithinAt_of_ricci_flow S hS clock ht x basis
      horth (m 0) (m 1)).hasDerivAt (D.regular_mem_nhds ht)
    convert hm.differentiableAt using 1; try rfl
    funext s
    change hamiltonMOriginField clock.origin s (S.base.metric s) x
      (fun q => A s (basis (m q))) = _
    rw [hamiltonMOriginField_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    have hslots : (fun q => A s (basis (m q))) =
        vec2 (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (basis (m 0)))
          (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (basis (m 1))) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots])
  exact ContinuousMultilinearMap.differentiableAt_of_compContinuousLinearMap
    (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)) (by simp [A]) hA hTA

theorem hamiltonMOrigin_pullback_components_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (S.family.metric clock.time) x (ι clock.time v)) J clock.time)
    (basis : Module.Basis (Fin n) ℝ F)
    (horth : ∀ i j, (S.family.metric clock.time).inner x
      (ι clock.time (basis i)) (ι clock.time (basis j)) = if i = j then 1 else 0)
    (a b : Fin n) :
    HasDerivWithinAt (fun s => hamiltonMOriginField clock.origin s (S.base.metric s) x
      (vec2 (ι s (basis a)) (ι s (basis b))))
      (roughLap0SField (S.family.metric clock.time)
          (hamiltonMOriginField clock.origin clock.time (S.family.metric clock.time)) x
          (vec2 (ι clock.time (basis a)) (ι clock.time (basis b))) +
        hamiltonMEvolutionReactionComponent clock
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (ι clock.time (basis i)) (ι clock.time (basis j))
              (ι clock.time (basis k)) (ι clock.time (basis l))))
          (fun i j => metricRicci (S.family.metric clock.time) x
            (vec2 (ι clock.time (basis i)) (ι clock.time (basis j))))
          (fun i j k => metricNablaRic (S.family.metric clock.time) x
            (vec3 (ι clock.time (basis i)) (ι clock.time (basis j)) (ι clock.time (basis k))))
          (fun i j k l => hamiltonNablaPField (S.family.metric clock.time) x
            (vec4 (ι clock.time (basis i)) (ι clock.time (basis j))
              (ι clock.time (basis k)) (ι clock.time (basis l))))
          (fun i j => hamiltonDivPAt (S.family.metric clock.time) x
            (vec2 (ι clock.time (basis i)) (ι clock.time (basis j)))) a b) J clock.time := by
  let B := basis.map (ι clock.time).toLinearEquiv
  have hB : ∀ i j, (S.base.metric clock.time).inner x (B i) (B j) =
      if i = j then 1 else 0 := horth
  let T := fun s => tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
    (hamiltonMOriginField clock.origin s (S.base.metric s) x)
  have hT : DifferentiableAt ℝ T clock.time :=
    hamiltonMOrigin_time_differentiableAt S hS clock ht x B hB
  let v : Fin 2 → F := ![basis a, basis b]
  have hd := hT.hasDerivAt.hasDerivWithinAt.continuousMultilinearMap_apply
    (fun q : Fin 2 => hι (v q))
  have hslot (s : ℝ) : (fun q => ι s (v q)) =
      vec2 (ι s (basis a)) (ι s (basis b)) := by
    funext q
    fin_cases q <;> rfl
  have hfun : (fun s => T s (fun q => ι s (v q))) =
      fun s => hamiltonMOriginField clock.origin s (S.base.metric s) x
        (vec2 (ι s (basis a)) (ι s (basis b))) := by
    funext s
    change hamiltonMOriginField clock.origin s (S.base.metric s) x _ = _
    rw [hslot]
  rw [hfun] at hd
  apply hd.congr_deriv
  let R := (ricciEndAt (S.base.metric clock.time)
    (metricRicci (S.base.metric clock.time) x)).toContinuousLinearMap
  have hjet (q : Fin 2) : HasDerivAt
      (fun s => oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s
        (B (![a, b] q))) (R (B (![a, b] q))) clock.time := by
    convert (hasDerivAt_const clock.time (B (![a, b] q))).add
      (((hasDerivAt_id clock.time).sub_const clock.time).smul_const (R (B (![a, b] q)))) using 1 <;>
      (try simp only [zero_add, one_smul]); rfl
  have hjetT := hT.hasDerivAt.continuousMultilinearMap_apply hjet
  have hm := (hamiltonMAt_hasDerivWithinAt_of_ricci_flow S hS clock ht x B hB a b).hasDerivAt
    (D.regular_mem_nhds ht)
  have hjetfun : (fun s => T s
      (fun q => oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s
        (B (![a, b] q)))) =
      fun s => hamiltonDivPAt (S.base.metric s) x
          (vec2 (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B a))
            (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B b))) +
        hamiltonCurvatureRicciAt (S.base.metric s) x
          (vec2 (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B a))
            (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B b))) +
        (1 / (2 * (s - clock.origin))) * metricRicci (S.base.metric s) x
          (vec2 (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B a))
            (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B b))) := by
    funext s
    change hamiltonMOriginField clock.origin s (S.base.metric s) x _ = _
    rw [hamiltonMOriginField_apply, Tensor0SSpace.add_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]
    have hv : (fun q : Fin 2 => oneTimeUhlenbeckVector (S.base.metric clock.time)
        clock.time s (B (![a, b] q))) =
        vec2 (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B a))
          (oneTimeUhlenbeckVector (S.base.metric clock.time) clock.time s (B b)) := by
      funext q
      fin_cases q <;> rfl
    rw [hv]
  rw [hjetfun] at hjetT
  have hderiv := hjetT.unique hm
  have hlap := hamiltonMOriginField_rough_laplacian_component clock.origin clock.time
    (S.base.metric clock.time) x B hB a b
  dsimp only at hlap
  have htrace : metricTrace0S2TensorInBasis B (identityInvMetric (Idx := Fin n))
      ((CanonicalSpatialDerivs0S.ofSmoothConnection (metricCov (S.base.metric clock.time))
        (metricCov_smooth (S.base.metric clock.time))
        (hamiltonMOriginField clock.origin clock.time (S.base.metric clock.time))).nabla2A x) =
      roughLap0SField (S.base.metric clock.time)
        (hamiltonMOriginField clock.origin clock.time (S.base.metric clock.time)) x := by
    ext tail
    rw [roughLap0SField_apply, roughLap0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (S.base.metric clock.time) B
        (identityInvMetric (Idx := Fin n))
        (metricInverseInBasis_identity_of_orthonormal (S.base.metric clock.time) B hB),
      metricTrace0S2TensorInBasis_apply]
    rfl
  rw [htrace] at hlap
  change _ = _ + _ at hderiv
  rw [show clock.elapsed = clock.time - clock.origin from rfl, ← hlap] at hderiv
  have hR : R = ricciSharp (S.family.metric clock.time) x :=
    ricciEndAt_metricRicci_eq_ricciSharp (S.base.metric clock.time) x
  simp only [oneTimeUhlenbeckVector, sub_self, zero_smul, add_zero] at hderiv
  rw [hR] at hderiv
  have hBv (i : Fin 2) : B (![a, b] i) = ι clock.time (v i) := by
    fin_cases i <;> rfl
  simp_rw [hBv] at hderiv
  convert hderiv using 1
  rfl


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem hamiltonP_pullback_components_hasDerivWithinAt_laplacian_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) {n : ℕ}
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (x : M) (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) J t)
    (basis : Module.Basis (Fin n) ℝ (V x))
    (horth : ∀ i j, (S.family.metric t).inner x (ι t x (basis i)) (ι t x (basis j)) =
      if i = j then 1 else 0) (a b c : Fin n) :
    HasDerivWithinAt (fun s => hamiltonPAt (S.base.metric s) x
      (fun q => ι s x (![basis a, basis b, basis c] q)))
      (rawBundleConnLap (S.family.metric t)
        (CovariantDerivative.multilinear
          (CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map
            (LeviCivita (S.family.metric t))) 3)
        (fun y => (hamiltonPField (S.family.metric t) y).compContinuousLinearMap
          (fun _ => (ι t y).toContinuousLinearMap)) x (![basis a, basis b, basis c]) +
        hamiltonPEvolutionReactionComponent
          (fun i j k l => S.base.rm04 t x
            (vec4 (ι t x (basis i)) (ι t x (basis j)) (ι t x (basis k)) (ι t x (basis l))))
          (fun i j => metricRicci (S.family.metric t) x
            (vec2 (ι t x (basis i)) (ι t x (basis j))))
          (fun i j k l m => nablaRm04Field S t x
            (vec5 (ι t x (basis i)) (ι t x (basis j)) (ι t x (basis k))
              (ι t x (basis l)) (ι t x (basis m))))
          (fun i j k => metricNablaRic (S.family.metric t) x
            (vec3 (ι t x (basis i)) (ι t x (basis j)) (ι t x (basis k)))) a b c) J t := by
  have hd := hamiltonP_pullback_components_hasDerivWithinAt_of_ricci_ode S hS t x
    (fun s => ι s x) hode basis horth a b c
  have hslots (s : ℝ) : (fun q => ι s x (![basis a, basis b, basis c] q)) =
      vec3 (ι s x (basis a)) (ι s x (basis b)) (ι s x (basis c)) := by
    funext q
    fin_cases q <;> rfl
  have hlap := rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    (ι t) hι (S.family.metric t) (LeviCivita (S.family.metric t)) 3
    (T := fun y => hamiltonPField (S.family.metric t) y) (x := x)
    (((hamiltonPField (S.family.metric t)).contMDiff x).of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  rw [rawBundleConnLap_multilinear_eq_roughLap0SField] at hlap
  rw [hlap]
  convert hd using 1
  · funext s
    rw [hslots]
  · congr 1
    change roughLap0SField (S.family.metric t) (hamiltonPField (S.family.metric t)) x
      (fun q => ι t x (![basis a, basis b, basis c] q)) = _
    rw [hslots]

theorem hamiltonMOrigin_pullback_components_hasDerivWithinAt_laplacian_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular) {n : ℕ}
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι clock.time x).toContinuousLinearMap))
    (x : M) (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric clock.time) x (ι clock.time x v)) J clock.time)
    (basis : Module.Basis (Fin n) ℝ (V x))
    (horth : ∀ i j, (S.family.metric clock.time).inner x
      (ι clock.time x (basis i)) (ι clock.time x (basis j)) = if i = j then 1 else 0)
    (a b : Fin n) :
    HasDerivWithinAt (fun s => hamiltonMOriginField clock.origin s (S.base.metric s) x
      (fun q => ι s x (![basis a, basis b] q)))
      (rawBundleConnLap (S.family.metric clock.time)
        (CovariantDerivative.multilinear
          (CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι clock.time y).toLinearEquiv) hι.clm_bundle_map
            (LeviCivita (S.family.metric clock.time))) 2)
        (fun y => (hamiltonMOriginField clock.origin clock.time (S.family.metric clock.time) y).compContinuousLinearMap (fun _ => (ι clock.time y).toContinuousLinearMap)) x
          (![basis a, basis b]) +
        hamiltonMEvolutionReactionComponent clock
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (ι clock.time x (basis i)) (ι clock.time x (basis j))
              (ι clock.time x (basis k)) (ι clock.time x (basis l))))
          (fun i j => metricRicci (S.family.metric clock.time) x
            (vec2 (ι clock.time x (basis i)) (ι clock.time x (basis j))))
          (fun i j k => metricNablaRic (S.family.metric clock.time) x
            (vec3 (ι clock.time x (basis i)) (ι clock.time x (basis j)) (ι clock.time x (basis k))))
          (fun i j k l => hamiltonNablaPField (S.family.metric clock.time) x
            (vec4 (ι clock.time x (basis i)) (ι clock.time x (basis j))
              (ι clock.time x (basis k)) (ι clock.time x (basis l))))
          (fun i j => hamiltonDivPAt (S.family.metric clock.time) x
            (vec2 (ι clock.time x (basis i)) (ι clock.time x (basis j)))) a b) J clock.time := by
  have hd := hamiltonMOrigin_pullback_components_hasDerivWithinAt_of_ricci_ode S hS clock ht x
    (fun s => ι s x) hode basis horth a b
  have hslots (s : ℝ) : (fun q => ι s x (![basis a, basis b] q)) =
      vec2 (ι s x (basis a)) (ι s x (basis b)) := by
    funext q
    fin_cases q <;> rfl
  have hlap := rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    (ι clock.time) hι (S.family.metric clock.time) (LeviCivita (S.family.metric clock.time)) 2
    (T := fun y => hamiltonMOriginField clock.origin clock.time (S.family.metric clock.time) y)
    (x := x)
    (((hamiltonMOriginField clock.origin clock.time (S.family.metric clock.time)).contMDiff x).of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  rw [rawBundleConnLap_multilinear_eq_roughLap0SField] at hlap
  rw [hlap]
  convert hd using 1
  · funext s
    rw [hslots]
  · congr 1
    change roughLap0SField (S.family.metric clock.time)
      (hamiltonMOriginField clock.origin clock.time (S.family.metric clock.time)) x
      (fun q => ι clock.time x (![basis a, basis b] q)) = _
    rw [hslots]

end DifferentialGeometry.PDE.RicciFlow
