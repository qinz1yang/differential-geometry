import DifferentialGeometry.Tensor.Multilinear.BundleComp
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TestJets
import DifferentialGeometry.Analysis.Calculus.Multilinear
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackTensor
import DifferentialGeometry.Geometry.Connection.Laplacian.CovariantTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem tensor0S_pullback_hasDerivWithinAt_of_endomorphism
    {k : ℕ} {x : M} {t : ℝ} (A : ℝ → Tensor0SSpace k I x)
    (B : Tensor0SSpace k I x) (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hA : ∀ v, HasDerivAt (fun s => A s v)
      ((B - covariantEndomorphismAction0S (A t) L) v) t)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F →L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v) (L (ι t v)) J t)
    (v : Fin k → F) :
    HasDerivWithinAt (fun s => A s (fun q => ι s (v q)))
      (B (fun q => ι t (v q))) J t := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) k x
  have hT : HasDerivAt (fun s => e (A s)) (e (B - covariantEndomorphismAction0S (A t) L)) t := by
    apply ContinuousMultilinearMap.hasDerivAt_of_basis_eval (coordinateFrameAtToBasis (I := I) x)
    intro m
    exact hA (fun q => coordinateFrameAtToBasis (I := I) x (m q))
  have hd := hT.hasDerivWithinAt.continuousMultilinearMap_apply (fun q => hι (v q))
  apply hd.congr_deriv
  change (B - covariantEndomorphismAction0S (A t) L) (fun q => ι t (v q)) +
    ∑ q, A t (Function.update (fun j => ι t (v j)) q (L (ι t (v q)))) = _
  rw [Tensor0SSpace.sub_apply, covariantEndomorphismAction0S_apply]
  exact sub_add_cancel _ _

private theorem tensor0S_pullback_hasDerivWithinAt_laplacian
    [I.Boundaryless] {k : ℕ} {t : ℝ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) k)
    (B : ∀ y, Tensor0SSpace k I y)
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ t y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    (x : M) (L : TangentSpace I x →L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hode : ∀ v, HasDerivWithinAt (fun s => φ s x v) (L (φ t x v)) J t)
    (hA : ∀ v, HasDerivAt (fun s => A s x v)
      ((roughLap0SField g (A t) x + B x - covariantEndomorphismAction0S (A t x) L) v) t)
    (v : Fin k → TangentSpace I x) :
    HasDerivWithinAt (fun s => tensor0SPullbackCLE k (φ s x).toLinearEquiv (A s x) v)
      (rawBundleConnLap g
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ t y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)).multilinear k)
        (fun y => tensor0SPullbackCLE k (φ t y).toLinearEquiv (A t y)) x v +
        tensor0SPullbackCLE k (φ t x).toLinearEquiv (B x) v) J t := by
  have hd := tensor0S_pullback_hasDerivWithinAt_of_endomorphism
    (fun s => A s x) (roughLap0SField g (A t) x + B x) L hA
    (fun s => (φ s x).toContinuousLinearMap) hode v
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
  rw [hlap']
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  convert hd using 1
  · rfl
  · change roughLap0SField g (A t) x (fun q => φ t x (v q)) +
      B x (fun q => φ t x (v q)) = _
    rw [Tensor0SSpace.add_apply]
    rfl

theorem hamilton_test_jet_realization_pullback
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (x : M) (clock : HarnackClock)
    (Ric : Tensor0SSpace 2 I x)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual ℝ (TangentSpace I x))
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))))
    {J : Set ℝ}
    (hode : ∀ v, HasDerivWithinAt (fun s => φ s x v)
      ((ricciEndAt g Ric).toContinuousLinearMap (φ clock.time x v)) J clock.time) :
    ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
      (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1),
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, U p.2 p.1⟩ : TotalSpace (Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SSpace 2 I y))) ∧
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, W p.2 p.1⟩ : TotalSpace (Tensor0SModel 1 ℝ E)
          (fun y : M => Tensor0SSpace 1 I y))) ∧
      (∀ r y X Y, U r y ![X, Y] = -U r y ![Y, X]) ∧
      U clock.time x = U₀.toTensor0S ∧
      (∀ X, W clock.time x (fun _ => X) = W₀ X) ∧
      let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)
      let fixedU := fun r y => tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)
      let fixedW := fun r y => tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)
      (∀ X Y, cov.multilinear 1 (fixedW clock.time) x (φ clock.time x X) (fun _ => Y) = 0) ∧
      (∀ X Y Z, cov.multilinear 2 (fixedU clock.time) x (φ clock.time x X) (vec2 Y Z) =
        (1 / 2 : ℝ) * (Ric ![φ clock.time x X, φ clock.time x Y] * W₀ (φ clock.time x Z) -
          Ric ![φ clock.time x X, φ clock.time x Z] * W₀ (φ clock.time x Y)) +
        (1 / (4 * clock.elapsed) : ℝ) *
          (g.inner x (φ clock.time x X) (φ clock.time x Y) * W₀ (φ clock.time x Z) -
            g.inner x (φ clock.time x X) (φ clock.time x Z) * W₀ (φ clock.time x Y))) ∧
      (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
        (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
      (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
        (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
          (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) := by
  obtain ⟨Ualt, U, W, hUalt, hUjoint, hWjoint, hU, hW, hDW, hDU, hUt, hWt⟩ :=
    hamilton_test_jet_realization (LeviCivita g) (metricCov_smooth g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible g) x clock Ric U₀ W₀
  have hUvalue : U clock.time x = U₀.toTensor0S := by
    rw [← hUalt, hU]
  have hskew (r : ℝ) (y : M) (X Y : TangentSpace I y) :
      U r y ![X, Y] = -U r y ![Y, X] := by
    rw [← hUalt]
    have hswap := (Ualt r y).map_swap (v := ![Y, X]) (i := (0 : Fin 2))
      (j := (1 : Fin 2)) (by decide)
    have hv : ![Y, X] ∘ (Equiv.swap (0 : Fin 2) 1) = ![X, Y] := by
      funext q
      fin_cases q <;> simp
    rw [hv] at hswap
    exact hswap
  refine ⟨U, W, hUjoint, hWjoint, hskew, hUvalue, hW, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    rw [multilinear_pullback_eq_totalNabla0SFun (φ clock.time) hφ]
    rw [hDW]
    simp
  · intro X Y Z
    rw [multilinear_pullback_eq_totalNabla0SFun (φ clock.time) hφ]
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
    have hv : (fun q : Fin 3 => (φ clock.time x).toLinearEquiv
        ((Fin.cons X (vec2 Y Z) : Fin 3 → TangentSpace I x) q)) =
        ![φ clock.time x X, φ clock.time x Y, φ clock.time x Z] := by
      funext q
      fin_cases q <;> rfl
    rw [hv]
    exact hDU _ _ _
  · intro v
    have htU : ∀ w, HasDerivAt (fun r => U r x w)
        ((roughLap0SField g (U clock.time) x + 0 -
          covariantEndomorphismAction0S (U clock.time x) (ricciEndAt g Ric).toContinuousLinearMap) w)
        clock.time := by
      intro w
      convert hUt w using 1
      rw [add_zero]
      rfl
    have hd := tensor0S_pullback_hasDerivWithinAt_laplacian g U (fun _ => 0)
      φ hφ x (ricciEndAt g Ric).toContinuousLinearMap hode htU v
    simpa only [map_zero, Tensor0SSpace.zero_apply, add_zero] using hd
  · intro v
    have htW : ∀ w, HasDerivAt (fun r => W r x w)
        ((roughLap0SField g (W clock.time) x + (1 / clock.elapsed : ℝ) • W clock.time x -
          covariantEndomorphismAction0S (W clock.time x) (ricciEndAt g Ric).toContinuousLinearMap) w)
        clock.time := hWt
    have hd := tensor0S_pullback_hasDerivWithinAt_laplacian g W
      (fun y => (1 / clock.elapsed : ℝ) • W clock.time y)
      φ hφ x (ricciEndAt g Ric).toContinuousLinearMap hode htW v
    simpa only [map_smul, Tensor0SSpace.smul_apply, smul_eq_mul] using hd

omit [T2Space M] in
private theorem tensor0S_pullback_joint_contMDiffOn
    {k : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) k)
    (hA : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun p : M × ℝ => (⟨p.1, A p.2 p.1⟩ : TotalSpace (Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SSpace k I y))))
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y) {J : Set ℝ}
    (hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, (φ p.1 p.2).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))
      (J ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun p : ℝ × M => (⟨p.2, tensor0SPullbackCLE k (φ p.1 p.2).toLinearEquiv (A p.1 p.2)⟩ :
        TotalSpace (Tensor0SModel k ℝ E) (fun y : M => Tensor0SSpace k I y))) (J ×ˢ Set.univ) := by
  have hA' := hA.comp (contMDiff_snd.prodMk contMDiff_fst)
  have h := hA'.contMDiffOn.multilinear_bundle_comp (fun _ => hφ)
  exact h

theorem exists_hamilton_test_jets_in_fixed_bundle
    [I.Boundaryless] (gSource : RiemannianMetric (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) (x : M) (clock : HarnackClock)
    (Ric : Tensor0SSpace 2 I x)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x)) (W₀ : StrongDual ℝ (TangentSpace I x))
    (φ : ℝ → ∀ y, TangentSpace I y ≃L[ℝ] TangentSpace I y)
    {J : Set ℝ} (ht : clock.time ∈ J)
    (hφjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, (φ p.1 p.2).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))
      (J ×ˢ Set.univ))
    (hiso : ∀ X Y, g.inner x (φ clock.time x X) (φ clock.time x Y) = gSource.inner x X Y)
    (hode : ∀ v, HasDerivWithinAt (fun s => φ s x v)
      ((ricciEndAt g Ric).toContinuousLinearMap (φ clock.time x v)) J clock.time) :
    ∃ (U : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
      (W : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 1)
      (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y)))),
      let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ clock.time y).toLinearEquiv) hφ.clm_bundle_map (LeviCivita g)
      let fixedU := fun r y => tensor0SPullbackCLE 2 (φ r y).toLinearEquiv (U r y)
      let fixedW := fun r y => tensor0SPullbackCLE 1 (φ r y).toLinearEquiv (W r y)
      let fixedRic := tensor0SPullbackCLE 2 (φ clock.time x).toLinearEquiv Ric
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : ℝ × M => (⟨p.2, fixedU p.1 p.2⟩ : TotalSpace (Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SSpace 2 I y))) (J ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
        (fun p : ℝ × M => (⟨p.2, fixedW p.1 p.2⟩ : TotalSpace (Tensor0SModel 1 ℝ E)
          (fun y : M => Tensor0SSpace 1 I y))) (J ×ˢ Set.univ) ∧
      (∀ r y X Y, fixedU r y ![X, Y] = -fixedU r y ![Y, X]) ∧
      fixedU clock.time x = U₀.toTensor0S ∧
      (∀ X, fixedW clock.time x (fun _ => X) = W₀ X) ∧
      (∀ X Y, cov.multilinear 1 (fixedW clock.time) x (φ clock.time x X) (fun _ => Y) = 0) ∧
      (∀ X Y Z, cov.multilinear 2 (fixedU clock.time) x (φ clock.time x X) (vec2 Y Z) =
        (1 / 2 : ℝ) * (fixedRic ![X, Y] * W₀ Z - fixedRic ![X, Z] * W₀ Y) +
        (1 / (4 * clock.elapsed) : ℝ) *
          (gSource.inner x X Y * W₀ Z - gSource.inner x X Z * W₀ Y)) ∧
      (∀ v, HasDerivWithinAt (fun r => fixedU r x v)
        (rawBundleConnLap g (cov.multilinear 2) (fixedU clock.time) x v) J clock.time) ∧
      (∀ v, HasDerivWithinAt (fun r => fixedW r x v)
        (rawBundleConnLap g (cov.multilinear 1) (fixedW clock.time) x v +
          (1 / clock.elapsed : ℝ) * fixedW clock.time x v) J clock.time) := by
  have hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => (⟨y, (φ clock.time y).toContinuousLinearMap⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) :=
    (hφjoint.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨ht, Set.mem_univ y⟩)).of_le (by simp)
  let e := φ clock.time x
  let Ut := U₀.compContinuousLinearMap e.symm.toContinuousLinearMap
  let Wt := W₀.comp e.symm.toContinuousLinearMap
  obtain ⟨U, W, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt⟩ :=
    hamilton_test_jet_realization_pullback g x clock Ric Ut Wt φ hφ hode
  refine ⟨U, W, hφ, ?_⟩
  dsimp only
  refine ⟨tensor0S_pullback_joint_contMDiffOn U hUjoint φ hφjoint,
    tensor0S_pullback_joint_contMDiffOn W hWjoint φ hφjoint, ?_, ?_, ?_, hDW, ?_, hUt, hWt⟩
  · intro r y X Y
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
    have hv (A B : TangentSpace I y) : (fun q => (φ r y).toLinearEquiv (![A, B] q)) =
        ![φ r y A, φ r y B] := by
      funext q
      fin_cases q <;> rfl
    simp only [hv]
    exact hskew r y _ _
  · rw [hU]
    apply tensor0SSpace_ext
    intro v
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply, Ut,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext q
    exact e.symm_apply_apply (v q)
  · intro X
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
    rw [hW]
    exact congrArg W₀ (e.symm_apply_apply X)
  · intro X Y Z
    rw [hDU]
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
    have hv (A B : TangentSpace I x) : (fun q => (φ clock.time x).toLinearEquiv (![A, B] q)) =
        ![φ clock.time x A, φ clock.time x B] := by
      funext q
      fin_cases q <;> rfl
    simp only [hv, Wt, e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, hiso]


theorem exists_uhlenbeck_isometry_with_hamilton_test_jets [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    {J : Set ℝ} {s : ℝ} (hJ : J.OrdConnected) (hs : s ∈ J)
    (hJD : J ⊆ D.regular)
    (gSource : RiemannianMetric (TangentSpace I : M → Type _))
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
                  (1 / clock.elapsed : ℝ) * fixedW clock.time x v) := by
  obtain ⟨ι, hinit, hjoint, hinv, hode, hiso⟩ :=
    exists_uhlenbeck_isometry_on_interval S hS hJ hs hJD
      gSource ι₀ hι₀ h₀
  refine ⟨ι, hinit, hjoint, hinv, hode, hiso, ?_⟩
  intro clock ht x U₀ W₀
  have hRicEnd :
      (ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap =
        ricciSharp (S.family.metric clock.time) x := by
    ext v
    apply ricciSharpVec_unique (S.family.metric clock.time) x v
    intro w
    rw [LinearMap.coe_toContinuousLinearMap', ricciEnd_inner]
    exact metricRicciAt_apply_eq_ricciTensor (S.family.metric clock.time) x v w
  have hRicODE : ∀ v, HasDerivWithinAt (fun r => ι r x v)
      ((ricciEndAt (S.family.metric clock.time)
        (metricRicci (S.family.metric clock.time) x)).toContinuousLinearMap
          (ι clock.time x v)) J clock.time := by
    intro v
    simpa only [hRicEnd] using hode x v clock.time ht
  obtain ⟨U, W, hι, hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt⟩ :=
    exists_hamilton_test_jets_in_fixed_bundle
      gSource (S.family.metric clock.time) x clock
      (metricRicci (S.family.metric clock.time) x) U₀ W₀ ι ht hjoint
      (hiso clock.time ht x) hRicODE
  refine ⟨U, W, hι, ?_⟩
  dsimp only
  refine ⟨hUjoint, hWjoint, hskew, hU, hW, hDW, hDU, hUt, hWt, ?_⟩
  intro hJnhds
  refine ⟨(hUjoint (clock.time, x) ⟨ht, Set.mem_univ x⟩).contMDiffAt
      (prod_mem_nhds hJnhds Filter.univ_mem),
    (hWjoint (clock.time, x) ⟨ht, Set.mem_univ x⟩).contMDiffAt
      (prod_mem_nhds hJnhds Filter.univ_mem),
    fun v => (hUt v).hasDerivAt hJnhds,
    fun v => (hWt v).hasDerivAt hJnhds, ?_, ?_⟩
  · intro v
    rw [((hUt v).hasDerivAt hJnhds).deriv]
    exact sub_self _
  · intro v
    rw [((hWt v).hasDerivAt hJnhds).deriv]
    exact add_sub_cancel_left _ _

end DifferentialGeometry.PDE.RicciFlow
