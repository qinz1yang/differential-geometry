import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.PIdentities
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import DifferentialGeometry.Geometry.Curvature.RicciPullbackDerivative

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem hamiltonPAt_tensor0SPullbackCLE_eq_multilinear
    (g : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M) (X Y Z : TangentSpace I x) :
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov g)
    let fixedRic := fun y => tensor0SPullbackCLE 2 (φ y).toLinearEquiv (metricRicci g y)
    tensor0SPullbackCLE 3 (φ x).toLinearEquiv (hamiltonPAt g x) (vec3 X Y Z) =
      D.multilinear 2 fixedRic x (φ x X) (vec2 Y Z) -
        D.multilinear 2 fixedRic x (φ x Y) (vec2 X Z) := by
  dsimp only
  rw [multilinear_pullback_metricRicci_eq_metricNablaRic g φ hφ,
    multilinear_pullback_metricRicci_eq_metricNablaRic g φ hφ]
  change tensor0SPullbackCLE 3 (φ x).toLinearEquiv
      (hamiltonP (metricNablaRic g x)) (vec3 X Y Z) = _
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  rw [show (fun i => (φ x).toLinearEquiv (vec3 X Y Z i)) =
      vec3 (φ x X) (φ x Y) (φ x Z) by
        funext i
        fin_cases i <;> rfl]
  rw [hamiltonP_apply]
  congr 1 <;> apply congrArg (metricNablaRic g x) <;>
    funext i <;> fin_cases i <;> rfl

theorem hamiltonPAt_tensor0SPullbackCLE_skew
    (g : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (X Y Z : TangentSpace I x) :
    tensor0SPullbackCLE 3 e (hamiltonPAt g y) (vec3 X Y Z) =
      -tensor0SPullbackCLE 3 e (hamiltonPAt g y) (vec3 Y X Z) := by
  change tensor0SPullbackCLE 3 e (hamiltonP (metricNablaRic g y)) (vec3 X Y Z) = _
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  rw [show (fun i => e (vec3 X Y Z i)) = vec3 (e X) (e Y) (e Z) by
        funext i
        fin_cases i <;> rfl,
    show (fun i => e (vec3 Y X Z i)) = vec3 (e Y) (e X) (e Z) by
        funext i
        fin_cases i <;> rfl]
  exact hamiltonP_skew _ (e X) (e Y) (e Z)

theorem hamiltonPAt_tensor0SPullbackCLE_cyclic
    (g : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (X Y Z : TangentSpace I x) :
    tensor0SPullbackCLE 3 e (hamiltonPAt g y) (vec3 X Y Z) +
        tensor0SPullbackCLE 3 e (hamiltonPAt g y) (vec3 Y Z X) +
      tensor0SPullbackCLE 3 e (hamiltonPAt g y) (vec3 Z X Y) = 0 := by
  have he (A B C : TangentSpace I x) :
      (fun i => e (vec3 A B C i)) = vec3 (e A) (e B) (e C) := by
    funext i
    fin_cases i <;> rfl
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he]
  exact hamiltonPAt_cyclic g y (e X) (e Y) (e Z)

theorem hamiltonPAt_tensor0SPullbackCLE_traces
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource gTarget : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (X : TangentSpace I x) :
    let fixedP := tensor0SPullbackCLE 3 e (hamiltonPAt gTarget y)
    (∑ i : Idx, ∑ j : Idx, gInv i j * fixedP (vec3 (basis i) X (basis j))) =
        -(1 / 2 : Real) *
          differential1FormFun (I := I) (fun z => metricScalarAt gTarget z) y
            (fun _ : Fin 1 => e X) ∧
      (∑ i : Idx, ∑ j : Idx, gInv i j * fixedP (vec3 X (basis i) (basis j))) =
        (1 / 2 : Real) *
          differential1FormFun (I := I) (fun z => metricScalarAt gTarget z) y
            (fun _ : Fin 1 => e X) := by
  have hinv' : MetricInverseInBasis (I := I) gTarget y (basis.map e) gInv := by
    intro i j
    simpa only [Module.Basis.map_apply, hiso] using hinv i j
  have he (A B C : TangentSpace I x) :
      (fun i => e (vec3 A B C i)) = vec3 (e A) (e B) (e C) := by
    funext i
    fin_cases i <;> rfl
  constructor
  · simpa only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he,
      Module.Basis.map_apply] using
      hamiltonPAt_first_trace gTarget (basis.map e) gInv hinv' (e X)
  · simpa only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he,
      Module.Basis.map_apply] using
      hamiltonPAt_second_trace gTarget (basis.map e) gInv hinv' (e X)

theorem multilinear_pullback_metricRm04_divergence_eq_hamiltonPAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource gTarget : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M)
    (hiso : ∀ u v, gTarget.inner x (φ x u) (φ x v) = gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B Z : TangentSpace I x) :
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov gTarget)
    let fixedRm := fun y => tensor0SPullbackCLE 4 (φ y).toLinearEquiv (metricRm04 gTarget y)
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * D.multilinear 4 fixedRm x (φ x (basis i)) (vec4 (basis j) Z A B)) =
      tensor0SPullbackCLE 3 (φ x).toLinearEquiv
        (hamiltonPAt gTarget x) (vec3 B A Z) := by
  have hinv' : MetricInverseInBasis (I := I) gTarget x
      (basis.map (φ x).toLinearEquiv) gInv := by
    intro i j
    change (∑ k, gInv i k * gTarget.inner x (φ x (basis k)) (φ x (basis j)) = _) ∧
      (∑ k, gTarget.inner x (φ x (basis i)) (φ x (basis k)) * gInv k j = _)
    simpa only [hiso] using hinv i j
  have he (A B C : TangentSpace I x) :
      (fun i => (φ x).toLinearEquiv (vec3 A B C i)) =
        vec3 (φ x A) (φ x B) (φ x C) := by
    funext i
    fin_cases i <;> rfl
  have hv (A B C D F : TangentSpace I x) :
      (fun i : Fin 5 => (φ x).toLinearEquiv ((Fin.cons A (vec4 (I := I) B C D F) : Fin 5 → TangentSpace I x) i)) =
        vec5 (φ x A) (φ x B) (φ x C) (φ x D) (φ x F) := by
    funext i
    fin_cases i <;> rfl
  dsimp only
  simp_rw [multilinear_pullback_eq_totalNabla0SFun φ hφ]
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he, hv]
  exact metric_curvature_divergence_eq_hamiltonPAt gTarget
    (basis.map (φ x).toLinearEquiv) gInv hinv' (φ x A) (φ x B) (φ x Z)

theorem exists_uhlenbeck_hamiltonP_on_interval
    [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {J : Set Real} {s : Real} (hJ : J.OrdConnected) (hs : s ∈ J)
    (hJD : J ⊆ D.regular)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource : SmoothRiemannianMetric I M)
    (ι₀ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric s).inner x (ι₀ x v) (ι₀ x w) =
      gSource.inner x v w) :
    ∃ (ι : Real → ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
      (hι : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun x => (⟨x, (ι t x).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))),
      (∀ x, ι s x = ι₀ x) ∧
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = gSource.inner x v w) ∧
      ∀ (t : Real) (ht : t ∈ J),
        let φ := ι t
        let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ y).toLinearEquiv)
          ((hι t ht).of_le (by norm_num)).clm_bundle_map
          (metricCov (S.family.metric t))
        let fixedRic := fun x => tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (metricRicci (S.family.metric t) x)
        let fixedNablaRic := fun x => tensor0SPullbackCLE 3 (φ x).toLinearEquiv
          (metricNablaRic (S.family.metric t) x)
        let fixedP := fun x => tensor0SPullbackCLE 3 (φ x).toLinearEquiv
          (hamiltonPAt (S.family.metric t) x)
        let fixedRm := fun x => tensor0SPullbackCLE 4 (φ x).toLinearEquiv
          (metricRm04 (S.family.metric t) x)
        (∀ (x : M) (X : TangentSpace I x) (tail : Fin 2 → TangentSpace I x),
          cov.multilinear 2 fixedRic x (φ x X) tail =
            fixedNablaRic x (Fin.cons X tail)) ∧
        (∀ (x : M) (X Y Z : TangentSpace I x),
          fixedP x (vec3 X Y Z) =
            cov.multilinear 2 fixedRic x (φ x X) (vec2 Y Z) -
              cov.multilinear 2 fixedRic x (φ x Y) (vec2 X Z)) ∧
        (∀ (x : M) (X Y Z : TangentSpace I x),
          fixedP x (vec3 X Y Z) = -fixedP x (vec3 Y X Z)) ∧
        (∀ (x : M) (X Y Z : TangentSpace I x),
          fixedP x (vec3 X Y Z) + fixedP x (vec3 Y Z X) +
            fixedP x (vec3 Z X Y) = 0) ∧
        ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x))
          (gInv : Idx → Idx → Real),
          MetricInverseInBasis (I := I) gSource x basis gInv →
          (∀ X : TangentSpace I x,
            (∑ i, ∑ j, gInv i j * fixedP x (vec3 (basis i) X (basis j))) =
                -(1 / 2 : Real) *
                  differential1FormFun (I := I) (fun z => metricScalarAt (S.family.metric t) z) x
                    (fun _ : Fin 1 => φ x X) ∧
              (∑ i, ∑ j, gInv i j * fixedP x (vec3 X (basis i) (basis j))) =
                (1 / 2 : Real) *
                  differential1FormFun (I := I) (fun z => metricScalarAt (S.family.metric t) z) x
                    (fun _ : Fin 1 => φ x X)) ∧
          ∀ A B Z : TangentSpace I x,
            (∑ i, ∑ j, gInv i j * cov.multilinear 4 fixedRm x
              (φ x (basis i)) (vec4 (basis j) Z A B)) = fixedP x (vec3 B A Z) := by
  obtain ⟨ι, hinit, hjoint, hinv, hderiv, hiso⟩ :=
    exists_uhlenbeck_isometry_on_interval S hS hJ hs hJD
      gSource.toRiemannianMetric ι₀ hι₀ h₀
  have hι : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x => (⟨x, (ι t x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))) := by
    intro t ht
    exact hjoint.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun x => ⟨ht, Set.mem_univ x⟩)
  refine ⟨ι, hι, hinit, hjoint, hinv, hderiv, hiso, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x X tail
    exact multilinear_pullback_metricRicci_eq_metricNablaRic (S.family.metric t)
      (ι t) ((hι t ht).of_le (by norm_num)) x X tail
  · intro x X Y Z
    exact hamiltonPAt_tensor0SPullbackCLE_eq_multilinear (S.family.metric t)
      (ι t) ((hι t ht).of_le (by norm_num)) x X Y Z
  · intro x X Y Z
    exact hamiltonPAt_tensor0SPullbackCLE_skew (S.family.metric t)
      (ι t x).toLinearEquiv X Y Z
  · intro x X Y Z
    exact hamiltonPAt_tensor0SPullbackCLE_cyclic (S.family.metric t)
      (ι t x).toLinearEquiv X Y Z
  · intro x basis gInv hmetric
    refine ⟨?_, ?_⟩
    · intro X
      exact hamiltonPAt_tensor0SPullbackCLE_traces gSource (S.family.metric t)
        (ι t x).toLinearEquiv (hiso t ht x) basis gInv hmetric X
    · intro A B Z
      exact multilinear_pullback_metricRm04_divergence_eq_hamiltonPAt
        gSource (S.family.metric t) (ι t) ((hι t ht).of_le (by norm_num)) x
        (hiso t ht x) basis gInv hmetric A B Z

end DifferentialGeometry.PDE.RicciFlow
