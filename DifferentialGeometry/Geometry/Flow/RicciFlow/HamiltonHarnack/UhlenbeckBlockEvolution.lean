import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MatrixHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.UhlenbeckTestJets
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricPullback
import DifferentialGeometry.Analysis.Calculus.MultilinearPullback
import DifferentialGeometry.Analysis.Calculus.Multilinear
import DifferentialGeometry.Analysis.Calculus.FiniteDimension
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TriangularJets
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackTensor
import DifferentialGeometry.Geometry.Connection.Laplacian.CovariantTensor
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor0S_hasDerivAt_of_pullback_of_endomorphism
    {k : ℕ} {x : M} {t : ℝ} (A : ℝ → Tensor0SSpace k I x)
    (B : Tensor0SSpace k I x) (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : ℝ → TangentSpace I x ≃L[ℝ] TangentSpace I x)
    (hφ : ∀ v, HasDerivAt (fun s => φ s v) (L (φ t v)) t)
    (hA : ∀ v : Fin k → TangentSpace I x, HasDerivAt (fun s => A s (fun q => φ s (v q)))
      (B (fun q => φ t (v q))) t) :
    ∀ v, HasDerivAt (fun s => A s v)
      ((B - covariantEndomorphismAction0S (A t) L) v) t := by
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin k => TangentSpace I x) ℝ) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => TangentSpace I x) ℝ) :=
    ContinuousMultilinearMap.normedSpace
  let : TopologicalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => TangentSpace I x) ℝ) :=
    ContinuousMultilinearMap.instTopologicalSpace
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) k x
  have hφd : DifferentiableAt ℝ (fun s => (φ s).toContinuousLinearMap) t :=
    differentiableAt_clm_apply.mpr (fun v => (hφ v).differentiableAt)
  have hT : HasDerivAt (fun s => (e (A s)).compContinuousLinearMap
      (fun _ => (φ s).toContinuousLinearMap))
      ((e B).compContinuousLinearMap (fun _ => (φ t).toContinuousLinearMap)) t := by
    apply ContinuousMultilinearMap.hasDerivAt_of_basis_eval (coordinateFrameAtToBasis (I := I) x)
    intro m
    exact hA (fun q => coordinateFrameAtToBasis (I := I) x (m q))
  have hAd := ContinuousMultilinearMap.differentiableAt_of_compContinuousLinearMap
    (f := fun s => e (A s)) (A := fun s => (φ s).toContinuousLinearMap)
    (φ t) rfl hφd hT.differentiableAt
  have hEq (v : Fin k → TangentSpace I x) :=
    (hAd.hasDerivAt.continuousMultilinearMap_apply (fun q => hφ (v q))).unique (hA v)
  have hder : deriv (fun s => e (A s)) t = e (B - covariantEndomorphismAction0S (A t) L) := by
    ext v
    have h := hEq (fun q => (φ t).symm (v q))
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    change (deriv (fun s => e (A s)) t) v = _
    change (deriv (fun s => e (A s)) t) v =
      (B - covariantEndomorphismAction0S (A t) L) v
    rw [Tensor0SSpace.sub_apply, covariantEndomorphismAction0S_apply]
    exact eq_sub_of_add_eq h
  intro v
  have hd := (hAd.hasDerivAt.congr_deriv hder).continuousMultilinearMap_apply
    (fun q => hasDerivAt_const t (v q))
  have hz : (∑ i, (e (A t)) (Function.update v i 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact (e (A t)).map_coord_zero i (Function.update_self i 0 v)
  rw [hz, add_zero] at hd
  convert hd using 1 <;> rfl


private theorem tensor0S_hasDerivAt_laplacian_of_pullback
    [I.Boundaryless] [T2Space M] {k : ℕ} {t : ℝ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) k)
    (B : ∀ y, Tensor0SSpace k I y)
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ t y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (x : M) (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v) (L (φ t x v)) t)
    (hA : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE k (φ s x).toLinearEquiv (A s x) v)
      (rawBundleConnLap g
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear k)
        (fun y => tensor0SPullbackCLE k (φ t y).toLinearEquiv (A t y)) x v +
        tensor0SPullbackCLE k (φ t x).toLinearEquiv (B x) v) t) :
    ∀ v, HasDerivAt (fun s => A s x v)
      ((roughLap0SField g (A t) x + B x - covariantEndomorphismAction0S (A t x) L) v) t := by
  apply tensor0S_hasDerivAt_of_pullback_of_endomorphism
    (fun s => A s x) (roughLap0SField g (A t) x + B x) L (fun s => φ s x) hode
  intro v
  have hlap := rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    (φ t) hφ g (LeviCivita g) k ((A t).contMDiff x |>.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  have hbase := rawBundleConnLap_multilinear_eq_roughLap0SField g (A t) x
  rw [hbase] at hlap
  have hlap' : rawBundleConnLap g
      ((CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear k)
      (fun y => tensor0SPullbackCLE k (φ t y).toLinearEquiv (A t y)) x =
      tensor0SPullbackCLE k (φ t x).toLinearEquiv (roughLap0SField g (A t) x) := hlap
  have h := hA v
  rw [hlap'] at h
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
  convert h using 1
  · rfl
  rw [Tensor0SSpace.add_apply]
  rfl

open DifferentialGeometry.Geometry.Curvature

private theorem hamilton_test_jets_of_pullback
    [I.Boundaryless] [T2Space M] {t : ℝ}
    (gSource : RiemannianMetric (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) (x : M) (τ : ℝ)
    (Ric : Tensor0SSpace 2 I x)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ t y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (hiso : ∀ X Y, g.inner x (φ t x X) (φ t x Y) = gSource.inner x X Y)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt g Ric).toContinuousLinearMap (φ t x v)) t)
    (hDW : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ t y).toLinearEquiv (W t y))
        x (φ t x X) (fun _ => Y) = 0)
    (hDU : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ t y).toLinearEquiv (U t y))
        x (φ t x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ t x).toLinearEquiv Ric ![X, Y] *
          tensor0SPullbackCLE 1 (φ t x).toLinearEquiv (W t x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ t x).toLinearEquiv Ric ![X, Z] *
          tensor0SPullbackCLE 1 (φ t x).toLinearEquiv (W t x) (fun _ => Y)) +
      (1 / (4 * τ) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ t x).toLinearEquiv (W t x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ t x).toLinearEquiv (W t x) (fun _ => Y)))
    (hUt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap g
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ t y).toLinearEquiv (U t y)) x v) t)
    (hWt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap g
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ t y).toLinearEquiv (W t y)) x v +
      (1 / τ : ℝ) * tensor0SPullbackCLE 1 (φ t x).toLinearEquiv (W t x) v) t) :
    totalNabla0SFun 1 (LeviCivita g) (W t) x = 0 ∧
    (∀ X Y Z, totalNabla0SFun 2 (LeviCivita g) (U t) x ![X, Y, Z] =
      (1 / 2 : ℝ) * (Ric ![X, Y] * W t x (fun _ => Z) - Ric ![X, Z] * W t x (fun _ => Y)) +
      (1 / (4 * τ) : ℝ) * (g.inner x X Y * W t x (fun _ => Z) -
        g.inner x X Z * W t x (fun _ => Y))) ∧
    (∀ v, HasDerivAt (fun s => U s x v)
      ((roughLap0SField g (U t) x -
        covariantEndomorphismAction0S (U t x) (ricciEndAt g Ric).toContinuousLinearMap) v) t) ∧
    (∀ v, HasDerivAt (fun s => W s x v)
      ((roughLap0SField g (W t) x + (1 / τ : ℝ) • W t x -
        covariantEndomorphismAction0S (W t x) (ricciEndAt g Ric).toContinuousLinearMap) v) t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply tensor0SSpace_ext
    intro v
    have h := hDW ((φ t x).symm (v 0)) ((φ t x).symm (v 1))
    rw [multilinear_pullback_eq_totalNabla0SFun (φ t) hφ] at h
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
    have hv : (fun q => (φ t x).toLinearEquiv
        ((Fin.cons ((φ t x).symm (v 0)) (fun _ : Fin 1 => (φ t x).symm (v 1)) : Fin 2 → TangentSpace I x) q)) = v := by
      funext q
      fin_cases q <;> simp
    rw [hv] at h
    exact h
  · intro X Y Z
    have h := hDU ((φ t x).symm X) ((φ t x).symm Y) ((φ t x).symm Z)
    rw [multilinear_pullback_eq_totalNabla0SFun (φ t) hφ] at h
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
    have hv2 (A B : TangentSpace I x) :
        (fun q => (φ t x).toLinearEquiv (![(φ t x).symm A, (φ t x).symm B] q)) = ![A, B] := by
      funext q
      fin_cases q <;> simp
    have hv3 : (fun q => (φ t x).toLinearEquiv
        ((Fin.cons ((φ t x).symm X) (vec2 ((φ t x).symm Y) ((φ t x).symm Z)) : Fin 3 → TangentSpace I x) q)) =
        ![X, Y, Z] := by
      funext q
      fin_cases q <;> exact (φ t x).apply_symm_apply _
    have hv1 (A : TangentSpace I x) :
        (fun _ : Fin 1 => (φ t x).toLinearEquiv ((φ t x).symm A)) = (fun _ => A) := by
      funext q
      exact (φ t x).apply_symm_apply A
    rw [hv3] at h
    simpa only [hv2, hv1, ← hiso, ContinuousLinearEquiv.apply_symm_apply] using h
  · intro v
    have h := tensor0S_hasDerivAt_laplacian_of_pullback g U (fun _ => 0) φ hφ x
      (ricciEndAt g Ric).toContinuousLinearMap hode
      (fun w => by simpa only [map_zero, Tensor0SSpace.zero_apply, add_zero] using hUt w) v
    simpa only [add_zero] using h
  · exact tensor0S_hasDerivAt_laplacian_of_pullback g W (fun y => (1 / τ : ℝ) • W t y)
      φ hφ x (ricciEndAt g Ric).toContinuousLinearMap hode
      (fun v => by simpa only [map_smul, Tensor0SSpace.smul_apply, smul_eq_mul] using hWt v)


private theorem hamilton_harnack_block_evolution_of_pulled_test_jets
    [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : RiemannianMetric (TangentSpace I : M → Type _))
    (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (horth : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (hskew : ∀ X Y : TangentSpace I x,
      U clock.time x ![X, Y] = -U clock.time x ![Y, X])
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (hiso : ∀ X Y, (S.family.metric clock.time).inner x (φ clock.time x X) (φ clock.time x Y) = gSource.inner x X Y)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt (S.family.metric clock.time) (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap (φ clock.time x v)) clock.time)
    (hDW : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y))
        x (φ clock.time x X) (fun _ => Y) = 0)
    (hDU : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y))
        x (φ clock.time x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Y] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Z] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)) +
      (1 / (4 * clock.elapsed) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)))
    (hUt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y)) x v) clock.time)
    (hWt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y)) x v +
      (1 / clock.elapsed : ℝ) * tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) v) clock.time) :
    let q := fun r y =>
      inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U r y).product (U r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y))
    HasDerivAt (fun r : Real => q r x)
        (deriv (fun r : Real => q r x) clock.time) clock.time ∧
      deriv (fun r : Real => q r x) clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis d)) (φ clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis c))))
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a b => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis a))) +
          hamiltonBlockSigmaSquare
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis d)) (φ clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis c))))
            (fun a b => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis a))) := by
  obtain ⟨hDW', hDU', hUt', hWt'⟩ := hamilton_test_jets_of_pullback gSource
    (S.family.metric clock.time) x clock.elapsed (metricRicci (S.family.metric clock.time) x)
    U W φ hφ hiso hode hDW hDU hUt hWt
  let B := basis.map (φ clock.time x).toLinearEquiv
  have hB : ∀ i j, (S.base.metric clock.time).inner x (B i) (B j) = if i = j then 1 else 0 :=
    fun i j => (hiso (basis i) (basis j)).trans (horth i j)
  exact hamilton_harnack_block_exact_evolution_of_tensor_test_jet S hS clock ht x B hB
    U W hskew hDW' hDU' hUt' hWt'

private theorem hamilton_block_tensor_contraction_pullback {x y : M}
    (gSource gTarget : SmoothMetricGen I M)
    (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (K : Tensor0SSpace 4 I y) (P : Tensor0SSpace 3 I y) (Mbar : Tensor0SSpace 2 I y)
    (U : Tensor0SSpace 2 I y) (W : Tensor0SSpace 1 I y) :
    inner0S gSource x 4 (tensor0SPullbackCLE 4 e K)
        ((tensor0SPullbackCLE 2 e U).product (tensor0SPullbackCLE 2 e U)) +
      2 * inner0S gSource x 3 (tensor0SPullbackCLE 3 e P)
        ((tensor0SPullbackCLE 2 e U).product (tensor0SPullbackCLE 1 e W)) +
      inner0S gSource x 2 (tensor0SPullbackCLE 2 e Mbar)
        ((tensor0SPullbackCLE 1 e W).product (tensor0SPullbackCLE 1 e W)) =
    inner0S gTarget y 4 K (U.product U) + 2 * inner0S gTarget y 3 P (U.product W) +
      inner0S gTarget y 2 Mbar (W.product W) := by
  rw [← Tensor0SBundle.tensor0SPullbackCLE_product,
    ← Tensor0SBundle.tensor0SPullbackCLE_product,
    ← Tensor0SBundle.tensor0SPullbackCLE_product]
  rw [Tensor0SBundle.inner0S_tensor0SPullbackCLE gSource gTarget x y 4 e hiso,
    Tensor0SBundle.inner0S_tensor0SPullbackCLE gSource gTarget x y 3 e hiso,
    Tensor0SBundle.inner0S_tensor0SPullbackCLE gSource gTarget x y 2 e hiso]


theorem hamilton_harnack_block_evolution_pullback
    [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : J ∈ nhds clock.time)
    (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (horth : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (hskew : ∀ X Y : TangentSpace I x,
      U clock.time x ![X, Y] = -U clock.time x ![Y, X])
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (hiso : ∀ r ∈ J, ∀ y X Y, (S.family.metric r).inner y (φ r y X) (φ r y Y) = gSource.inner y X Y)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt (S.family.metric clock.time) (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap (φ clock.time x v)) clock.time)
    (hDW : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y))
        x (φ clock.time x X) (fun _ => Y) = 0)
    (hDU : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y))
        x (φ clock.time x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Y] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Z] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)) +
      (1 / (4 * clock.elapsed) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)))
    (hUt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y)) x v) clock.time)
    (hWt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y)) x v +
      (1 / clock.elapsed : ℝ) * tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) v) clock.time) :
    let q := fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (φ r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (φ r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)))
    HasDerivAt (fun r : Real => q r x)
        (deriv (fun r : Real => q r x) clock.time) clock.time ∧
      deriv (fun r : Real => q r x) clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis d)) (φ clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis c))))
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a b => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis a))) +
          hamiltonBlockSigmaSquare
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis d)) (φ clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b)) (φ clock.time x (basis c))))
            (fun a b => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis a)) (φ clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis a))) := by
  dsimp only
  have htJ : clock.time ∈ J := mem_of_mem_nhds hJ
  obtain ⟨hqd, hqheat⟩ := hamilton_harnack_block_evolution_of_pulled_test_jets
    S hS clock ht gSource.toRiemannianMetric x basis horth U W hskew φ hφ
      (hiso clock.time htJ x) hode hDW hDU hUt hWt
  let qOriginal := fun r y =>
    inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U r y).product (U r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y))
  let qFixed := fun r y =>
    inner0S gSource y 4
          (tensor0SPullbackCLE 4 (φ r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (φ r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)))
  have heq (r : ℝ) (hr : r ∈ J) (y : M) : qFixed r y = qOriginal r y :=
    hamilton_block_tensor_contraction_pullback gSource (S.base.metric r) (φ r y).toLinearEquiv
      (hiso r hr y) _ _ _ _ _
  have hspace : qFixed clock.time = qOriginal clock.time := funext (heq clock.time htJ)
  have htime : (fun r => qFixed r x) =ᶠ[nhds clock.time] (fun r => qOriginal r x) := by
    filter_upwards [hJ] with r hr
    exact heq r hr x
  have hqdFixed := hqd.congr_of_eventuallyEq htime
  refine ⟨hqdFixed.congr_deriv hqdFixed.deriv.symm, ?_⟩
  change deriv (fun r => qFixed r x) clock.time -
    laplacianAt (flowG S) clock.time (qFixed clock.time) x = _
  rw [hqdFixed.deriv, hspace]
  exact hqheat

theorem exists_uhlenbeck_isometry_with_hamilton_block_evolution [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    {J : Set ℝ} {s : ℝ} (hJ : J.OrdConnected) (hs : s ∈ J)
    (hJD : J ⊆ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    (ι₀ : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric s).inner x (ι₀ x v) (ι₀ x w) =
      gSource.inner x v w) :
    ∃ ι : ℝ → ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι s x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = gSource.inner x v w) ∧
      ∀ (clock : HarnackClock) (_ : clock.time ∈ J) (x : M)
        (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
        (W₀ : StrongDual ℝ (TangentSpace I x)),
        ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
          (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
          (hι : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
            (fun y => (⟨y, (ι clock.time y).toContinuousLinearMap⟩ :
              TotalSpace (E →L[ℝ] E)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))),
          let g := S.family.metric clock.time
          let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι clock.time y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)
          let fixedU := fun r y => tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)
          let fixedW := fun r y => tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)
          let fixedRic := tensor0SPullbackCLE 2 (ι clock.time x).toLinearEquiv (metricRicci g x)
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
            (J ×ˢ Set.univ) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
            (J ×ˢ Set.univ) ∧
          (∀ r y X Y, fixedU r y ![X, Y] = -fixedU r y ![Y, X]) ∧
          fixedU clock.time x = U₀.toTensor0S ∧
          (∀ X, fixedW clock.time x (fun _ => X) = W₀ X) ∧
          (∀ X Y,
            cov.multilinear 1 (fixedW clock.time) x (ι clock.time x X) (fun _ => Y) = 0) ∧
          (∀ X Y Z,
            cov.multilinear 2 (fixedU clock.time) x (ι clock.time x X) (vec2 Y Z) =
              (1 / 2 : ℝ) * (fixedRic ![X, Y] * W₀ Z - fixedRic ![X, Z] * W₀ Y) +
              (1 / (4 * clock.elapsed) : ℝ) *
                (gSource.inner x X Y * W₀ Z - gSource.inner x X Z * W₀ Y)) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
            (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
            (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
              (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) ∧
          (J ∈ nhds clock.time →
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
              (clock.time, x) ∧
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
              (clock.time, x) ∧
            (∀ v, HasDerivAt (fun r => fixedU r x v)
              (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) clock.time) ∧
            (∀ v, HasDerivAt (fun r => fixedW r x v)
              (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
                (1 / clock.elapsed : ℝ) * fixedW clock.time x v) clock.time) ∧
            (∀ v, deriv (fun r => fixedU r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v = 0) ∧
            ∀ v, deriv (fun r => fixedW r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v =
                  (1 / clock.elapsed : ℝ) * fixedW clock.time x v) ∧
          (J ∈ nhds clock.time → ∀ (n : ℕ)
            (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
            (_ : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0),
    let q := fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (ι r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (ι r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)))
    HasDerivAt (fun r : Real => q r x)
        (deriv (fun r : Real => q r x) clock.time) clock.time ∧
      deriv (fun r : Real => q r x) clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b)) (ι clock.time x (basis d)) (ι clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b)) (ι clock.time x (basis c))))
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b))))
            (fun a b => U clock.time x
              (vec2 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => ι clock.time x (basis a))) +
          hamiltonBlockSigmaSquare
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b)) (ι clock.time x (basis d)) (ι clock.time x (basis c))))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b)) (ι clock.time x (basis c))))
            (fun a b => U clock.time x
              (vec2 (I := I) (ι clock.time x (basis a)) (ι clock.time x (basis b))))
            (fun a => W clock.time x (fun _ : Fin 1 => ι clock.time x (basis a)))) := by
  obtain ⟨ι, hinit, hjoint, hinv, hode, hiso, hjets⟩ :=
    exists_uhlenbeck_isometry_with_hamilton_test_jets S hS hJ hs hJD
      gSource.toRiemannianMetric ι₀ hι₀ h₀
  refine ⟨ι, hinit, hjoint, hinv, hode, hiso, ?_⟩
  intro clock ht x U₀ W₀
  obtain ⟨U, W, hι, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal⟩ :=
    hjets clock ht x U₀ W₀
  refine ⟨U, W, hι, ?_⟩
  dsimp only
  refine ⟨hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal, ?_⟩
  intro hnhds n basis horth
  have hRicEnd :
      (ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap =
        ricciSharp (S.family.metric clock.time) x := by
    ext v
    apply ricciSharpVec_unique (S.family.metric clock.time) x v
    intro w
    rw [LinearMap.coe_toContinuousLinearMap', ricciEnd_inner]
    exact metricRicciAt_apply_eq_ricciTensor (S.family.metric clock.time) x v w
  have hRicODE : ∀ v, HasDerivAt (fun r => ι r x v)
      ((ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap
          (ι clock.time x v)) clock.time := by
    intro v
    simpa only [hRicEnd] using (hode x v clock.time ht).hasDerivAt hnhds
  have horigSkew (X Y : TangentSpace I x) :
      U clock.time x ![X, Y] = -U clock.time x ![Y, X] := by
    have h := hskew clock.time x ((ι clock.time x).symm X) ((ι clock.time x).symm Y)
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
    have hv (A B : TangentSpace I x) :
        (fun q => (ι clock.time x).toLinearEquiv
          (![(ι clock.time x).symm A, (ι clock.time x).symm B] q)) = ![A, B] := by
      funext q
      fin_cases q <;> exact (ι clock.time x).apply_symm_apply _
    simpa only [hv] using h
  apply hamilton_harnack_block_evolution_pullback S hS clock (hJD ht) gSource hnhds
    x basis horth U W horigSkew ι hι hiso hRicODE hDW
  · intro X Y Z
    simp only [hW]
    convert hDU X Y Z using 1
    rfl
  · intro v
    exact (hUt v).hasDerivAt hnhds
  · intro v
    exact (hWt v).hasDerivAt hnhds

theorem exists_uhlenbeck_isometry_with_hamilton_block_heat_nonneg [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    {J : Set ℝ} {s : ℝ} (hJ : J.OrdConnected) (hs : s ∈ J)
    (hJD : J ⊆ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    (ι₀ : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric s).inner x (ι₀ x v) (ι₀ x w) =
      gSource.inner x v w) :
    ∃ ι : ℝ → ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι s x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = gSource.inner x v w) ∧
      ∀ (clock : HarnackClock) (_ : clock.time ∈ J) (x : M)
        (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
        (W₀ : StrongDual ℝ (TangentSpace I x)),
        ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
          (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
          (hι : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
            (fun y => (⟨y, (ι clock.time y).toContinuousLinearMap⟩ :
              TotalSpace (E →L[ℝ] E)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))),
          let g := S.family.metric clock.time
          let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι clock.time y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)
          let fixedU := fun r y => tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)
          let fixedW := fun r y => tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)
          let fixedRic := tensor0SPullbackCLE 2 (ι clock.time x).toLinearEquiv (metricRicci g x)
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
            (J ×ˢ Set.univ) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
            (J ×ˢ Set.univ) ∧
          (∀ r y X Y, fixedU r y ![X, Y] = -fixedU r y ![Y, X]) ∧
          fixedU clock.time x = U₀.toTensor0S ∧
          (∀ X, fixedW clock.time x (fun _ => X) = W₀ X) ∧
          (∀ X Y,
            cov.multilinear 1 (fixedW clock.time) x (ι clock.time x X) (fun _ => Y) = 0) ∧
          (∀ X Y Z,
            cov.multilinear 2 (fixedU clock.time) x (ι clock.time x X) (vec2 Y Z) =
              (1 / 2 : ℝ) * (fixedRic ![X, Y] * W₀ Z - fixedRic ![X, Z] * W₀ Y) +
              (1 / (4 * clock.elapsed) : ℝ) *
                (gSource.inner x X Y * W₀ Z - gSource.inner x X Z * W₀ Y)) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
            (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
            (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
              (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) ∧
          (J ∈ nhds clock.time →
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
              (clock.time, x) ∧
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
              (clock.time, x) ∧
            (∀ v, HasDerivAt (fun r => fixedU r x v)
              (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) clock.time) ∧
            (∀ v, HasDerivAt (fun r => fixedW r x v)
              (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
                (1 / clock.elapsed : ℝ) * fixedW clock.time x v) clock.time) ∧
            (∀ v, deriv (fun r => fixedU r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v = 0) ∧
            ∀ v, deriv (fun r => fixedW r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v =
                  (1 / clock.elapsed : ℝ) * fixedW clock.time x v) ∧
          (J ∈ nhds clock.time → ∀
            (_ : ∀ (U : HamiltonHarnackTwoForm (TangentSpace I x))
              (W : Tensor0SSpace 1 I x),
              0 ≤ hamiltonHarnackQuadraticAt (I := I) S clock x U W),
              let q := fun r y =>
                inner0S gSource y 4
                    (tensor0SPullbackCLE 4 (ι r y).toLinearEquiv
                      (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
                    ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
                      (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))) +
                  2 * inner0S gSource y 3
                    (tensor0SPullbackCLE 3 (ι r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
                    ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
                      (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
                  inner0S gSource y 2
                    (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv
                      (hamiltonMOriginField clock.origin r (S.base.metric r) y))
                    ((tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)).product
                      (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)))
              HasDerivAt (fun r : Real => q r x)
                  (deriv (fun r : Real => q r x) clock.time) clock.time ∧
                0 ≤ deriv (fun r : Real => q r x) clock.time -
                  laplacianAt (I := I) (flowG (I := I) S) clock.time (q clock.time) x) := by
  obtain ⟨ι, hinit, hjoint, hinv, hode, hiso, hjets⟩ :=
    exists_uhlenbeck_isometry_with_hamilton_block_evolution
      S hS hJ hs hJD gSource ι₀ hι₀ h₀
  refine ⟨ι, hinit, hjoint, hinv, hode, hiso, ?_⟩
  intro clock ht x U₀ W₀
  obtain ⟨U, W, hι, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt,
      hlocal, hevo⟩ := hjets clock ht x U₀ W₀
  refine ⟨U, W, hι, ?_⟩
  dsimp only
  refine ⟨hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal, ?_⟩
  intro hnhds hnonneg
  classical
  obtain ⟨basis, horth⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gSource x
  let n := Module.finrank ℝ (TangentSpace I x)
  obtain ⟨hqd, hqheat⟩ := hevo hnhds n basis horth
  refine ⟨hqd, ?_⟩
  rw [hqheat]
  let B := basis.map (ι clock.time x).toLinearEquiv
  have hB : ∀ i j, (S.base.metric clock.time).inner x (B i) (B j) =
      if i = j then 1 else 0 :=
    fun i j => (hiso clock.time ht x (basis i) (basis j)).trans (horth i j)
  have hM : hamiltonMOriginField clock.origin clock.time (S.base.metric clock.time) x =
      hamiltonMAt clock (S.base.metric clock.time) x := by
    rw [hamiltonMOriginField_apply]
    exact (hamiltonMAt_eq_hamiltonDivPAt_add S hS clock (hJD ht) x).symm
  have hUc (a b : Fin n) :
      U clock.time x (vec2 (B a) (B b)) = -U clock.time x (vec2 (B b) (B a)) := by
    have h := hskew clock.time x (basis a) (basis b)
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
    have hv (a b : Fin n) :
        (fun q => (ι clock.time x).toLinearEquiv (![basis a, basis b] q)) =
          vec2 (B a) (B b) := by
      funext q
      fin_cases q <;> rfl
    simpa only [hv] using h
  have hreaction := hamiltonBlockJ_add_sigmaSquare_nonneg_of_harnack_nonneg S clock (hJD ht) x
    B hB hnonneg (fun a b => U clock.time x (vec2 (B a) (B b)))
      (fun a => W clock.time x (fun _ : Fin 1 => B a)) hUc
  have hv2 (X Y : TangentSpace I x) : vec2 X Y = ![X, Y] := by
    funext q
    fin_cases q <;> rfl
  have hv3 (X Y Z : TangentSpace I x) : vec3 X Y Z = ![X, Y, Z] := by
    funext q
    fin_cases q <;> rfl
  have hBapply (a : Fin n) : B a = ι clock.time x (basis a) := rfl
  simpa only [hM, hamiltonPField_apply, tensor04StandardAt_apply, hBapply,
    hv2, hv3] using hreaction


private theorem hamilton_perturbed_harnack_block_evolution_within_of_pulled_test_jets
    [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : RiemannianMetric (TangentSpace I : M → Type _))
    (x : M) {T : Set Real} (hT : UniqueDiffWithinAt Real T clock.time) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (horth : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (hskew : ∀ X Y : TangentSpace I x,
      U clock.time x ![X, Y] = -U clock.time x ![Y, X])
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (hiso : ∀ X Y, (S.family.metric clock.time).inner x (φ clock.time x X) (φ clock.time x Y) = gSource.inner x X Y)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt (S.family.metric clock.time) (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap (φ clock.time x v)) clock.time)
    (hDW : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y))
        x (φ clock.time x X) (fun _ => Y) = 0)
    (hDU : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y))
        x (φ clock.time x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Y] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Z] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)) +
      (1 / (4 * clock.elapsed) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)))
    (hUt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y)) x v) clock.time)
    (hWt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y)) x v +
      (1 / clock.elapsed : ℝ) * tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) v) clock.time)
    (phi : Real → M → Real) (psi : Real → Real) (phi' psi' : Real)
    (hphi : HasDerivWithinAt (fun r => phi r x) phi' T clock.time)
    (hpsi : HasDerivWithinAt psi psi' T clock.time)
    (hh : ContMDiffAt I 𝓘(Real, Real) 2 (phi clock.time) x) :
    let q := fun r y =>
      inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U r y).product (U r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y)) +
        (phi r y / (r - clock.origin)) *
          normSq0S (I := I) (S.base.metric r) y 1 (W r y) +
        psi r *
          normSq0S (I := I) (S.base.metric r) y 2 (U r y)
    HasDerivWithinAt (fun r : Real => q r x)
        (derivWithin (fun r : Real => q r x) T clock.time) T clock.time ∧
      derivWithin (fun r : Real => q r x) T clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis l)) (φ clock.time x (basis k))))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis k))))
            (fun i j => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i j => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) +
          hamiltonBlockSigmaSquare
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis l)) (φ clock.time x (basis k))))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis k))))
            (fun i j => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) +
          ((phi' -
                laplacianAt (I := I) (flowG (I := I) S) clock.time (phi clock.time) x) /
              clock.elapsed + phi clock.time x / clock.elapsed ^ 2) *
            (∑ i : Fin n,
              (W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) ^ 2) +
          psi' * (∑ i : Fin n, ∑ j : Fin n,
            (U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)))) ^ 2) -
          2 * psi clock.time *
            (∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (hamiltonTestJetDU clock
                (fun p q => metricRicci (I := I) (M := M)
                  (S.base.metric clock.time) x
                    (vec2 (I := I) (φ clock.time x (basis p)) (φ clock.time x (basis q))))
                (fun p q => if p = q then (1 : Real) else 0)
                (fun p => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis p)))
                e i j) ^ 2) := by
  obtain ⟨hDW', hDU', hUt', hWt'⟩ := hamilton_test_jets_of_pullback gSource
    (S.family.metric clock.time) x clock.elapsed (metricRicci (S.family.metric clock.time) x)
    U W φ hφ hiso hode hDW hDU hUt hWt
  let B := basis.map (φ clock.time x).toLinearEquiv
  have hB : ∀ i j, (S.base.metric clock.time).inner x (B i) (B j) = if i = j then 1 else 0 :=
    fun i j => (hiso (basis i) (basis j)).trans (horth i j)
  exact hamilton_perturbed_harnack_block_exact_evolution_of_phi
    (I := I) S hS clock ht x B hB U W hskew hDW' hDU' hUt' hWt'
      hT phi psi phi' psi' hphi hpsi hh


theorem hamilton_perturbed_harnack_block_evolution_within_pullback
    [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : J ∈ nhds clock.time)
    (x : M) {T : Set Real} (hT : UniqueDiffWithinAt Real T clock.time) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (horth : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (hskew : ∀ X Y : TangentSpace I x,
      U clock.time x ![X, Y] = -U clock.time x ![Y, X])
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (hiso : ∀ r ∈ J, ∀ y X Y, (S.family.metric r).inner y (φ r y X) (φ r y Y) = gSource.inner y X Y)
    (hode : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt (S.family.metric clock.time) (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap (φ clock.time x v)) clock.time)
    (hDW : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y))
        x (φ clock.time x X) (fun _ => Y) = 0)
    (hDU : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y))
        x (φ clock.time x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Y] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Z] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)) +
      (1 / (4 * clock.elapsed) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)))
    (hUt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y)) x v) clock.time)
    (hWt : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y)) x v +
      (1 / clock.elapsed : ℝ) * tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) v) clock.time)
    (phi : Real → M → Real) (psi : Real → Real) (phi' psi' : Real)
    (hphi : HasDerivWithinAt (fun r => phi r x) phi' T clock.time)
    (hpsi : HasDerivWithinAt psi psi' T clock.time)
    (hh : ContMDiffAt I 𝓘(Real, Real) 2 (phi clock.time) x) :
    let q := fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (φ r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (φ r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        (phi r y / (r - clock.origin)) * normSq0S (I := I) gSource y 1
          (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)) +
        psi r * normSq0S (I := I) gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))
    HasDerivWithinAt (fun r : Real => q r x)
        (derivWithin (fun r : Real => q r x) T clock.time) T clock.time ∧
      derivWithin (fun r : Real => q r x) T clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis l)) (φ clock.time x (basis k))))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis k))))
            (fun i j => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i j => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) +
          hamiltonBlockSigmaSquare
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis l)) (φ clock.time x (basis k))))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)) (φ clock.time x (basis k))))
            (fun i j => U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j))))
            (fun i => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) +
          ((phi' -
                laplacianAt (I := I) (flowG (I := I) S) clock.time (phi clock.time) x) /
              clock.elapsed + phi clock.time x / clock.elapsed ^ 2) *
            (∑ i : Fin n,
              (W clock.time x (fun _ : Fin 1 => φ clock.time x (basis i))) ^ 2) +
          psi' * (∑ i : Fin n, ∑ j : Fin n,
            (U clock.time x
              (vec2 (I := I) (φ clock.time x (basis i)) (φ clock.time x (basis j)))) ^ 2) -
          2 * psi clock.time *
            (∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (hamiltonTestJetDU clock
                (fun p q => metricRicci (I := I) (M := M)
                  (S.base.metric clock.time) x
                    (vec2 (I := I) (φ clock.time x (basis p)) (φ clock.time x (basis q))))
                (fun p q => if p = q then (1 : Real) else 0)
                (fun p => W clock.time x (fun _ : Fin 1 => φ clock.time x (basis p)))
                e i j) ^ 2) := by
  dsimp only
  have htJ : clock.time ∈ J := mem_of_mem_nhds hJ
  obtain ⟨hqd, hqheat⟩ := hamilton_perturbed_harnack_block_evolution_within_of_pulled_test_jets
    S hS clock ht gSource.toRiemannianMetric x hT basis horth U W hskew φ hφ
      (hiso clock.time htJ x) hode hDW hDU hUt hWt
      phi psi phi' psi' hphi hpsi hh
  let qOriginal := fun r y =>
    inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U r y).product (U r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y)) +
        (phi r y / (r - clock.origin)) *
          normSq0S (I := I) (S.base.metric r) y 1 (W r y) +
        psi r * normSq0S (I := I) (S.base.metric r) y 2 (U r y)
  let qFixed := fun r y =>
    inner0S gSource y 4
          (tensor0SPullbackCLE 4 (φ r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (φ r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        (phi r y / (r - clock.origin)) * normSq0S (I := I) gSource y 1
          (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)) +
        psi r * normSq0S (I := I) gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))
  have heq (r : ℝ) (hr : r ∈ J) (y : M) : qFixed r y = qOriginal r y := by
    have hBase := hamilton_block_tensor_contraction_pullback gSource (S.base.metric r)
      (φ r y).toLinearEquiv (hiso r hr y)
      (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y)
      (hamiltonPField (S.base.metric r) y)
      (hamiltonMOriginField clock.origin r (S.base.metric r) y) (U r y) (W r y)
    have hWnorm := Tensor0SBundle.inner0S_tensor0SPullbackCLE
      gSource (S.base.metric r) y y 1 (φ r y).toLinearEquiv
      (hiso r hr y) (W r y) (W r y)
    have hUnorm := Tensor0SBundle.inner0S_tensor0SPullbackCLE
      gSource (S.base.metric r) y y 2 (φ r y).toLinearEquiv
      (hiso r hr y) (U r y) (U r y)
    dsimp only [qFixed, qOriginal, normSq0S]
    rw [hBase, hWnorm, hUnorm]
  have hspace : qFixed clock.time = qOriginal clock.time := funext (heq clock.time htJ)
  have htime : (fun r => qFixed r x) =ᶠ[nhds clock.time] (fun r => qOriginal r x) := by
    filter_upwards [hJ] with r hr
    exact heq r hr x
  have hqdFixed := hqd.congr_of_eventuallyEq
    (htime.filter_mono nhdsWithin_le_nhds) (heq clock.time htJ x)
  refine ⟨hqdFixed.congr_deriv (hqdFixed.derivWithin hT).symm, ?_⟩
  change derivWithin (fun r => qFixed r x) T clock.time -
    laplacianAt (flowG S) clock.time (qFixed clock.time) x = _
  rw [hqdFixed.derivWithin hT, hspace]
  exact hqheat

theorem exists_hamilton_perturbed_harnack_block_evolution_lower_bound_within_pullback
    [I.Boundaryless] [T2Space M] (K S0 : Real) :
    ∃ C : Real, 0 ≤ C ∧ ∀
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (_ : IsSolutionOn S) (clock : HarnackClock) (_ : clock.time ∈ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    {J : Set ℝ} (_ : J ∈ nhds clock.time)
    (x : M) {T : Set Real} (_ : UniqueDiffWithinAt Real T clock.time) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (_ : ∀ i j, gSource.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
    (_ : ∀ X Y : TangentSpace I x,
      U clock.time x ![X, Y] = -U clock.time x ![Y, X])
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (_ : ∀ r ∈ J, ∀ y X Y, (S.family.metric r).inner y (φ r y X) (φ r y Y) = gSource.inner y X Y)
    (_ : ∀ v, HasDerivAt (fun s => φ s x v)
      ((ricciEndAt (S.family.metric clock.time) (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap (φ clock.time x v)) clock.time)
    (_ : ∀ X Y,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y))
        x (φ clock.time x X) (fun _ => Y) = 0)
    (_ : ∀ X Y Z,
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y))
        x (φ clock.time x X) (vec2 Y Z) =
      (1 / 2 : ℝ) *
        (tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Y] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv (metricRicci (S.family.metric clock.time) x) ![X, Z] *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)) +
      (1 / (4 * clock.elapsed) : ℝ) *
        (gSource.inner x X Y *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Z) -
        gSource.inner x X Z *
          tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) (fun _ => Y)))
    (_ : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 2 (φ s x).toLinearEquiv (U s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 2)
        (fun y => tensor0SPullbackCLE 2 (φ clock.time y).toLinearEquiv (U clock.time y)) x v) clock.time)
    (_ : ∀ v, HasDerivAt
      (fun s => tensor0SPullbackCLE 1 (φ s x).toLinearEquiv (W s x) v)
      (rawBundleConnLap (S.family.metric clock.time)
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita (S.family.metric clock.time))).multilinear 1)
        (fun y => tensor0SPullbackCLE 1 (φ clock.time y).toLinearEquiv (W clock.time y)) x v +
      (1 / clock.elapsed : ℝ) * tensor0SPullbackCLE 1 (φ clock.time x).toLinearEquiv (W clock.time x) v) clock.time)
    (phi : Real → M → Real) (psi : Real → Real) (phi' psi' : Real)
    (_ : HasDerivWithinAt (fun r => phi r x) phi' T clock.time)
    (_ : HasDerivWithinAt psi psi' T clock.time)
    (_ : ContMDiffAt I 𝓘(Real, Real) 2 (phi clock.time) x)
    (_ : ∀ k : Nat, k ≤ 2 →
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x ≤ K)
    (_ : clock.elapsed ≤ S0)
    (_ : 0 ≤ phi clock.time x)
    (_ : 0 ≤ psi clock.time) (_ : psi clock.time ≤ 1),
    let q := fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (φ r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (φ r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y))) +
        (phi r y / (r - clock.origin)) * normSq0S (I := I) gSource y 1
          (tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)) +
        psi r * normSq0S (I := I) gSource y 2
          (tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y))
    let B := basis.map (φ clock.time x).toLinearEquiv
    let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
      S.base.rm04 clock.time x
        (vec4 (I := I) (B a) (B b) (B d) (B c))
    let P : Fin n → Fin n → Fin n → Real := fun a b c =>
      hamiltonPField (I := I) (S.base.metric clock.time) x
        (vec3 (I := I) (B a) (B b) (B c))
    let Mbar : Fin n → Fin n → Real := fun a b =>
      hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x (vec2 (I := I) (B a) (B b))
    let Uc : Fin n → Fin n → Real := fun a b =>
      U clock.time x (vec2 (I := I) (B a) (B b))
    let Wc : Fin n → Real := fun a => W clock.time x (fun _ => B a)
    let Lphi := phi' - laplacianAt (I := I) (flowG (I := I) S)
      clock.time (phi clock.time) x
    HasDerivWithinAt (fun r : Real => q r x)
        (derivWithin (fun r : Real => q r x) T clock.time) T clock.time ∧
      hamiltonBlockJ (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P
          (hamiltonPerturbedMBlock clock Mbar (phi clock.time x)) Uc Wc +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P Uc Wc +
        (Lphi / clock.elapsed + phi clock.time x / clock.elapsed ^ 2 -
            C * psi clock.time / clock.elapsed ^ 2 -
            C * phi clock.time x / clock.elapsed) * (∑ a, (Wc a) ^ 2) +
        (psi' - C * psi clock.time) * (∑ a, ∑ b, (Uc a b) ^ 2) ≤
      derivWithin (fun r : Real => q r x) T clock.time -
        laplacianAt (I := I) (flowG (I := I) S) clock.time (q clock.time) x := by
  obtain ⟨C, hC, hbound⟩ := exists_hamiltonPerturbedBlock_reaction_lower_bound
    (I := I) (M := M) K S0
  refine ⟨C, hC, ?_⟩
  intro D S hS clock ht gSource J hJ x T hT n basis horth U W hskew
    φ hφ hiso hode hDW hDU hUt hWt phi psi phi' psi' hphi hpsi hh
    hderiv helapsed hphiNonneg hpsiNonneg hpsiOne
  obtain ⟨hqd, hqe⟩ := hamilton_perturbed_harnack_block_evolution_within_pullback
    (I := I) S hS clock ht gSource hJ x hT basis horth U W hskew
    φ hφ hiso hode hDW hDU hUt hWt phi psi phi' psi' hphi hpsi hh
  refine ⟨hqd, ?_⟩
  dsimp only at hqe ⊢
  rw [hqe]
  let B := basis.map (φ clock.time x).toLinearEquiv
  have hB : ∀ i j, (S.base.metric clock.time).inner x (B i) (B j) =
      if i = j then 1 else 0 :=
    fun i j => (hiso clock.time (mem_of_mem_nhds hJ) x (basis i) (basis j)).trans
      (horth i j)
  exact hbound S hS clock ht x B hB (phi clock.time x)
    (phi' - laplacianAt (I := I) (flowG S) clock.time (phi clock.time) x)
    (psi clock.time) psi'
    (fun a b => U clock.time x (vec2 (I := I) (B a) (B b)))
    (fun a => W clock.time x (fun _ => B a))
    hderiv helapsed hphiNonneg hpsiNonneg hpsiOne
    (fun a b => by
      have hv (X Y : TangentSpace I x) : vec2 (I := I) X Y = ![X, Y] := by
        funext k
        fin_cases k <;> rfl
      simpa only [hv] using hskew (B a) (B b))

theorem exists_uhlenbeck_isometry_with_perturbed_hamilton_block_evolution_lower_bound
    [I.Boundaryless] [T2Space M] (K S0 : Real) :
    ∃ C : Real, 0 ≤ C ∧ ∀
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (_ : IsSolutionOn S)
    {J : Set ℝ} {s : ℝ} (_ : J.OrdConnected) (_ : s ∈ J)
    (_ : J ⊆ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    (ι₀ : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x)
    (_ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))))
    (_ : ∀ x v w, (S.family.metric s).inner x (ι₀ x v) (ι₀ x w) =
      gSource.inner x v w),
    ∃ ι : ℝ → ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι s x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = gSource.inner x v w) ∧
      ∀ (clock : HarnackClock) (_ : clock.time ∈ J) (x : M)
        (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
        (W₀ : StrongDual ℝ (TangentSpace I x)),
        ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
          (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
          (hι : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
            (fun y => (⟨y, (ι clock.time y).toContinuousLinearMap⟩ :
              TotalSpace (E →L[ℝ] E)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))),
          let g := S.family.metric clock.time
          let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι clock.time y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)
          let fixedU := fun r y => tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)
          let fixedW := fun r y => tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)
          let fixedRic := tensor0SPullbackCLE 2 (ι clock.time x).toLinearEquiv (metricRicci g x)
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
            (J ×ˢ Set.univ) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
            (J ×ˢ Set.univ) ∧
          (∀ r y X Y, fixedU r y ![X, Y] = -fixedU r y ![Y, X]) ∧
          fixedU clock.time x = U₀.toTensor0S ∧
          (∀ X, fixedW clock.time x (fun _ => X) = W₀ X) ∧
          (∀ X Y,
            cov.multilinear 1 (fixedW clock.time) x (ι clock.time x X) (fun _ => Y) = 0) ∧
          (∀ X Y Z,
            cov.multilinear 2 (fixedU clock.time) x (ι clock.time x X) (vec2 Y Z) =
              (1 / 2 : ℝ) * (fixedRic ![X, Y] * W₀ Z - fixedRic ![X, Z] * W₀ Y) +
              (1 / (4 * clock.elapsed) : ℝ) *
                (gSource.inner x X Y * W₀ Z - gSource.inner x X Z * W₀ Y)) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
            (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
            (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
              (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) ∧
          (J ∈ nhds clock.time →
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
              (clock.time, x) ∧
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
              (clock.time, x) ∧
            (∀ v, HasDerivAt (fun r => fixedU r x v)
              (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) clock.time) ∧
            (∀ v, HasDerivAt (fun r => fixedW r x v)
              (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
                (1 / clock.elapsed : ℝ) * fixedW clock.time x v) clock.time) ∧
            (∀ v, deriv (fun r => fixedU r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v = 0) ∧
            ∀ v, deriv (fun r => fixedW r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v =
                  (1 / clock.elapsed : ℝ) * fixedW clock.time x v) ∧
          (J ∈ nhds clock.time → ∀
            {T : Set Real} (_ : UniqueDiffWithinAt Real T clock.time) {n : Nat}
            (basis : Module.Basis (Fin n) Real (TangentSpace I x))
            (_ : ∀ i j, gSource.inner x (basis i) (basis j) =
              if i = j then 1 else 0)
    (phi : Real → M → Real) (psi : Real → Real) (phi' psi' : Real)
    (_ : HasDerivWithinAt (fun r => phi r x) phi' T clock.time)
    (_ : HasDerivWithinAt psi psi' T clock.time)
    (_ : ContMDiffAt I 𝓘(Real, Real) 2 (phi clock.time) x)
    (_ : ∀ k : Nat, k ≤ 2 →
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x ≤ K)
    (_ : clock.elapsed ≤ S0)
    (_ : 0 ≤ phi clock.time x)
    (_ : 0 ≤ psi clock.time) (_ : psi clock.time ≤ 1),
    let q := fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (ι r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (ι r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
        (phi r y / (r - clock.origin)) * normSq0S (I := I) gSource y 1
          (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)) +
        psi r * normSq0S (I := I) gSource y 2
          (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))
    let B := basis.map (ι clock.time x).toLinearEquiv
    let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
      S.base.rm04 clock.time x
        (vec4 (I := I) (B a) (B b) (B d) (B c))
    let P : Fin n → Fin n → Fin n → Real := fun a b c =>
      hamiltonPField (I := I) (S.base.metric clock.time) x
        (vec3 (I := I) (B a) (B b) (B c))
    let Mbar : Fin n → Fin n → Real := fun a b =>
      hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x (vec2 (I := I) (B a) (B b))
    let Uc : Fin n → Fin n → Real := fun a b =>
      U clock.time x (vec2 (I := I) (B a) (B b))
    let Wc : Fin n → Real := fun a => W clock.time x (fun _ => B a)
    let Lphi := phi' - laplacianAt (I := I) (flowG (I := I) S)
      clock.time (phi clock.time) x
    HasDerivWithinAt (fun r : Real => q r x)
        (derivWithin (fun r : Real => q r x) T clock.time) T clock.time ∧
      hamiltonBlockJ (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P
          (hamiltonPerturbedMBlock clock Mbar (phi clock.time x)) Uc Wc +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P Uc Wc +
        (Lphi / clock.elapsed + phi clock.time x / clock.elapsed ^ 2 -
            C * psi clock.time / clock.elapsed ^ 2 -
            C * phi clock.time x / clock.elapsed) * (∑ a, (Wc a) ^ 2) +
        (psi' - C * psi clock.time) * (∑ a, ∑ b, (Uc a b) ^ 2) ≤
      derivWithin (fun r : Real => q r x) T clock.time -
        laplacianAt (I := I) (flowG (I := I) S) clock.time (q clock.time) x) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_hamilton_perturbed_harnack_block_evolution_lower_bound_within_pullback
      (I := I) (M := M) K S0
  refine ⟨C, hC, ?_⟩
  intro D S hS J s hJ hs hJD gSource ι₀ hι₀ h₀
  obtain ⟨ι, hinit, hjoint, hinv, hode, hiso, hjets⟩ :=
    exists_uhlenbeck_isometry_with_hamilton_test_jets S hS hJ hs hJD
      gSource.toRiemannianMetric ι₀ hι₀ h₀
  refine ⟨ι, hinit, hjoint, hinv, hode, hiso, ?_⟩
  intro clock ht x U₀ W₀
  obtain ⟨U, W, hι, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal⟩ :=
    hjets clock ht x U₀ W₀
  refine ⟨U, W, hι, ?_⟩
  dsimp only
  refine ⟨hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal, ?_⟩
  intro hnhds T hT n basis horth phi psi phi' psi' hphi hpsi hh
    hderiv helapsed hphiNonneg hpsiNonneg hpsiOne
  have hRicEnd :
      (ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap =
        ricciSharp (S.family.metric clock.time) x := by
    ext v
    apply ricciSharpVec_unique (S.family.metric clock.time) x v
    intro w
    rw [LinearMap.coe_toContinuousLinearMap', ricciEnd_inner]
    exact metricRicciAt_apply_eq_ricciTensor (S.family.metric clock.time) x v w
  have hRicODE : ∀ v, HasDerivAt (fun r => ι r x v)
      ((ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap
          (ι clock.time x v)) clock.time := by
    intro v
    simpa only [hRicEnd] using (hode x v clock.time ht).hasDerivAt hnhds
  have horigSkew (X Y : TangentSpace I x) :
      U clock.time x ![X, Y] = -U clock.time x ![Y, X] := by
    have h := hskew clock.time x ((ι clock.time x).symm X) ((ι clock.time x).symm Y)
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply] at h
    have hv (A B : TangentSpace I x) :
        (fun q => (ι clock.time x).toLinearEquiv
          (![(ι clock.time x).symm A, (ι clock.time x).symm B] q)) = ![A, B] := by
      funext q
      fin_cases q <;> exact (ι clock.time x).apply_symm_apply _
    simpa only [hv] using h
  apply hbound S hS clock (hJD ht) gSource hnhds x hT basis horth U W
    horigSkew ι hι hiso hRicODE hDW
  · intro X Y Z
    simp only [hW]
    convert hDU X Y Z using 1
    rfl
  · intro v
    exact (hUt v).hasDerivAt hnhds
  · intro v
    exact (hWt v).hasDerivAt hnhds
  · exact hphi
  · exact hpsi
  · exact hh
  · exact hderiv
  · exact helapsed
  · exact hphiNonneg
  · exact hpsiNonneg
  · exact hpsiOne

theorem exists_uhlenbeck_isometry_with_perturbed_hamilton_block_upper_support
    [I.Boundaryless] [T2Space M] (K S0 : Real) :
    ∃ C : Real, 0 ≤ C ∧ ∀
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (_ : IsSolutionOn S)
    {J : Set ℝ} {s : ℝ} (_ : J.OrdConnected) (_ : s ∈ J)
    (_ : J ⊆ D.regular)
    (gSource : SmoothRiemannianMetric I M)
    (ι₀ : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x)
    (_ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))))
    (_ : ∀ x v w, (S.family.metric s).inner x (ι₀ x v) (ι₀ x w) =
      gSource.inner x v w),
    ∃ ι : ℝ → ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι s x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = gSource.inner x v w) ∧
      ∀ (clock : HarnackClock) (_ : clock.time ∈ J) (x : M)
        (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
        (W₀ : StrongDual ℝ (TangentSpace I x)),
        ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
          (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
          (hι : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
            (fun y => (⟨y, (ι clock.time y).toContinuousLinearMap⟩ :
              TotalSpace (E →L[ℝ] E)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))),
          let g := S.family.metric clock.time
          let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι clock.time y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)
          let fixedU := fun r y => tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)
          let fixedW := fun r y => tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)
          let fixedRic := tensor0SPullbackCLE 2 (ι clock.time x).toLinearEquiv (metricRicci g x)
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
            (J ×ˢ Set.univ) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
            (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
              TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
            (J ×ˢ Set.univ) ∧
          (∀ r y X Y, fixedU r y ![X, Y] = -fixedU r y ![Y, X]) ∧
          fixedU clock.time x = U₀.toTensor0S ∧
          (∀ X, fixedW clock.time x (fun _ => X) = W₀ X) ∧
          (∀ X Y,
            cov.multilinear 1 (fixedW clock.time) x (ι clock.time x X) (fun _ => Y) = 0) ∧
          (∀ X Y Z,
            cov.multilinear 2 (fixedU clock.time) x (ι clock.time x X) (vec2 Y Z) =
              (1 / 2 : ℝ) * (fixedRic ![X, Y] * W₀ Z - fixedRic ![X, Z] * W₀ Y) +
              (1 / (4 * clock.elapsed) : ℝ) *
                (gSource.inner x X Y * W₀ Z - gSource.inner x X Z * W₀ Y)) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
            (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
          (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
            (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
              (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) ∧
          (J ∈ nhds clock.time →
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)))
              (clock.time, x) ∧
            ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
              (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ :
                TotalSpace (Tensor0SModel 1 ℝ E) (fun y : M => Tensor0SSpace 1 I y)))
              (clock.time, x) ∧
            (∀ v, HasDerivAt (fun r => fixedU r x v)
              (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) clock.time) ∧
            (∀ v, HasDerivAt (fun r => fixedW r x v)
              (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
                (1 / clock.elapsed : ℝ) * fixedW clock.time x v) clock.time) ∧
            (∀ v, deriv (fun r => fixedU r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v = 0) ∧
            ∀ v, deriv (fun r => fixedW r x v) clock.time -
                rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v =
                  (1 / clock.elapsed : ℝ) * fixedW clock.time x v) ∧
          (J ∈ nhds clock.time → ∀
            (stop : Real) (_ : clock.time ≤ stop) {n : Nat}
            (basis : Module.Basis (Fin n) Real (TangentSpace I x))
            (_ : ∀ i j, gSource.inner x (basis i) (basis j) =
              if i = j then 1 else 0)
    (phi phiBar : Real → M → Real) (psi : Real → Real) (phi' psi' : Real)
    (_ : HasDerivWithinAt (fun r => phiBar r x) phi' (Set.Ioc clock.origin stop) clock.time)
    (_ : HasDerivWithinAt psi psi' (Set.Ioc clock.origin stop) clock.time)
    (_ : ContMDiffAt I 𝓘(Real, Real) 2 (phiBar clock.time) x)
    (_ : ∀ k : Nat, k ≤ 2 →
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x ≤ K)
    (_ : clock.elapsed ≤ S0)
    (_ : 0 ≤ phi clock.time x)
    (_ : 0 ≤ psi clock.time) (_ : psi clock.time ≤ 1)
    (_ : phi clock.time x = phiBar clock.time x)
    (_ : ∀ᶠ z in 𝓝[(Set.Ioc clock.origin stop ×ˢ (Set.univ : Set M))]
      (clock.time, x), phi z.1 z.2 ≤ phiBar z.1 z.2),
    let q := fun f : Real → M → Real => fun r y =>
      inner0S gSource y 4
          (tensor0SPullbackCLE 4 (ι r y).toLinearEquiv
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))) +
        2 * inner0S gSource y 3
          (tensor0SPullbackCLE 3 (ι r y).toLinearEquiv (hamiltonPField (S.base.metric r) y))
          ((tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
        inner0S gSource y 2
          (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv
            (hamiltonMOriginField clock.origin r (S.base.metric r) y))
          ((tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)).product
            (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y))) +
        (f r y / (r - clock.origin)) * normSq0S (I := I) gSource y 1
          (tensor0SPullbackCLE 1 (ι r y).toLinearEquiv (W r y)) +
        psi r * normSq0S (I := I) gSource y 2
          (tensor0SPullbackCLE 2 (ι r y).toLinearEquiv (U r y))
    let B := basis.map (ι clock.time x).toLinearEquiv
    let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
      S.base.rm04 clock.time x
        (vec4 (I := I) (B a) (B b) (B d) (B c))
    let P : Fin n → Fin n → Fin n → Real := fun a b c =>
      hamiltonPField (I := I) (S.base.metric clock.time) x
        (vec3 (I := I) (B a) (B b) (B c))
    let Mbar : Fin n → Fin n → Real := fun a b =>
      hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x (vec2 (I := I) (B a) (B b))
    let Uc : Fin n → Fin n → Real := fun a b =>
      U clock.time x (vec2 (I := I) (B a) (B b))
    let Wc : Fin n → Real := fun a => W clock.time x (fun _ => B a)
    let Lphi := phi' - laplacianAt (I := I) (flowG (I := I) S)
      clock.time (phiBar clock.time) x
    q phi clock.time x = q phiBar clock.time x ∧
    (∀ᶠ z in 𝓝[(Set.Ioc clock.origin stop ×ˢ (Set.univ : Set M))]
      (clock.time, x), q phi z.1 z.2 ≤ q phiBar z.1 z.2) ∧
    HasDerivWithinAt (fun r : Real => q phiBar r x)
        (derivWithin (fun r : Real => q phiBar r x) (Set.Ioc clock.origin stop) clock.time) (Set.Ioc clock.origin stop) clock.time ∧
      hamiltonBlockJ (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P
          (hamiltonPerturbedMBlock clock Mbar (phi clock.time x)) Uc Wc +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock R (psi clock.time)) P Uc Wc +
        (Lphi / clock.elapsed + phi clock.time x / clock.elapsed ^ 2 -
            C * psi clock.time / clock.elapsed ^ 2 -
            C * phi clock.time x / clock.elapsed) * (∑ a, (Wc a) ^ 2) +
        (psi' - C * psi clock.time) * (∑ a, ∑ b, (Uc a b) ^ 2) ≤
      derivWithin (fun r : Real => q phiBar r x) (Set.Ioc clock.origin stop) clock.time -
        laplacianAt (I := I) (flowG (I := I) S) clock.time (q phiBar clock.time) x) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uhlenbeck_isometry_with_perturbed_hamilton_block_evolution_lower_bound
      (I := I) (M := M) K S0
  refine ⟨C, hC, ?_⟩
  intro D S hS J s hJ hs hJD gSource ι₀ hι₀ h₀
  obtain ⟨ι, hinit, hjoint, hinv, hode, hiso, hjets⟩ :=
    hproducer S hS hJ hs hJD gSource ι₀ hι₀ h₀
  refine ⟨ι, hinit, hjoint, hinv, hode, hiso, ?_⟩
  intro clock ht x U₀ W₀
  obtain ⟨U, W, hι, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt,
      hlocal, hlower⟩ := hjets clock ht x U₀ W₀
  refine ⟨U, W, hι, ?_⟩
  dsimp only
  refine ⟨hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, hlocal, ?_⟩
  intro hnhds stop htstop n basis horth phi phiBar psi phi' psi' hphi hpsi hh
    hderiv helapsed hphiNonneg hpsiNonneg hpsiOne hcontact hupper
  have hphiBarNonneg : 0 ≤ phiBar clock.time x := by
    rw [← hcontact]
    exact hphiNonneg
  have hoper := hlower hnhds
    (uniqueDiffOn_Ioc clock.origin stop clock.time ⟨clock.origin_lt_time, htstop⟩)
    basis horth phiBar psi phi' psi' hphi hpsi hh hderiv helapsed
    hphiBarNonneg hpsiNonneg hpsiOne
  dsimp only at hoper ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hcontact]
  · filter_upwards [hupper, self_mem_nhdsWithin] with z hz hzT
    have hden : 0 ≤ z.1 - clock.origin := sub_nonneg.mpr hzT.1.1.le
    have hscaled :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hz hden)
        (normSq0S_nonneg gSource z.2 1
          (tensor0SPullbackCLE 1 (ι z.1 z.2).toLinearEquiv (W z.1 z.2)))
    linarith only [hscaled]
  · simpa only [hcontact] using hoper

end DifferentialGeometry.PDE.RicciFlow
