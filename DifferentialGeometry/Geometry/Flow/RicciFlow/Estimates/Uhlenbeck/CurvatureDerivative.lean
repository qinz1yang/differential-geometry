import DifferentialGeometry.Analysis.Calculus.Multilinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Tensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem riemann_pullback_hasDerivWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t v)) J t)
    (v : Fin 4 → F) :
    HasDerivWithinAt (fun s => S.base.rm04 s x (fun q => ι s (v q)))
      ((deriv (fun s => S.base.rm04 s x) t) (fun q => ι t (v q)) +
        ∑ q : Fin 4, S.base.rm04 t x
          (fun p => ι t (Function.update v q
            ((ι t).symm (ricciSharp (I := I) (S.family.metric t) x (ι t (v q)))) p))) J t := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
  have hRm := (riemann_differentiableAt_of_solution S hS t x).hasDerivAt.hasDerivWithinAt
    (s := J)
  have hCml := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hRm
  have h := hCml.continuousMultilinearMap_apply (fun q : Fin 4 => hι (v q))
  refine h.congr_deriv ?_
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  change S.base.rm04 (t : ℝ) x _ = S.base.rm04 (t : ℝ) x _
  congr 1
  funext p
  by_cases hp : p = q
  · subst p
    simp
  · simp [hp]

theorem riemann_pullback_four_slots_hasDerivWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t v)) J t)
    (a b c d : F) :
    HasDerivWithinAt
      (fun s => S.base.rm04 s x (vec4 (ι s a) (ι s b) (ι s c) (ι s d)))
      ((deriv (fun s => S.base.rm04 s x) t)
          (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) +
        S.base.rm04 t x (vec4
          (ricciSharp (I := I) (S.family.metric t) x (ι t a)) (ι t b) (ι t c) (ι t d)) +
        S.base.rm04 t x (vec4 (ι t a)
          (ricciSharp (I := I) (S.family.metric t) x (ι t b)) (ι t c) (ι t d)) +
        S.base.rm04 t x (vec4 (ι t a) (ι t b)
          (ricciSharp (I := I) (S.family.metric t) x (ι t c)) (ι t d)) +
        S.base.rm04 t x (vec4 (ι t a) (ι t b) (ι t c)
          (ricciSharp (I := I) (S.family.metric t) x (ι t d)))) J t := by
  have h := riemann_pullback_hasDerivWithinAt S hS t x ι hι ![a, b, c, d]
  have hslots (s : ℝ) : (fun q => ι s (![a, b, c, d] q)) =
      vec4 (ι s a) (ι s b) (ι s c) (ι s d) := by
    funext q
    fin_cases q <;> rfl
  have hupdate (q : Fin 4) :
      (fun p => ι t (Function.update ![a, b, c, d] q
        ((ι t).symm (ricciSharp (I := I) (S.family.metric t) x
          (ι t (![a, b, c, d] q)))) p)) =
      Function.update (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) q
        (ricciSharp (I := I) (S.family.metric t) x (ι t (![a, b, c, d] q))) := by
    funext p
    by_cases hp : p = q
    · subst p
      simp
    · simp only [Function.update_of_ne hp]
      exact congrFun (hslots t) p
  simp only [hslots, hupdate, Fin.sum_univ_four] at h
  have h0 (u : TangentSpace I x) :
      Function.update (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) (0 : Fin 4) u =
      vec4 u (ι t b) (ι t c) (ι t d) := by
    funext q
    fin_cases q <;> rfl
  have h1 (u : TangentSpace I x) :
      Function.update (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) (1 : Fin 4) u =
      vec4 (ι t a) u (ι t c) (ι t d) := by
    funext q
    fin_cases q <;> rfl
  have h2 (u : TangentSpace I x) :
      Function.update (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) (2 : Fin 4) u =
      vec4 (ι t a) (ι t b) u (ι t d) := by
    funext q
    fin_cases q <;> rfl
  have h3 (u : TangentSpace I x) :
      Function.update (vec4 (ι t a) (ι t b) (ι t c) (ι t d)) (3 : Fin 4) u =
      vec4 (ι t a) (ι t b) (ι t c) u := by
    funext q
    fin_cases q <;> rfl
  rw [h0, h1, h2, h3] at h
  have hv0 : (![a, b, c, d] : Fin 4 → F) 0 = a := by rfl
  have hv1 : (![a, b, c, d] : Fin 4 → F) 1 = b := by rfl
  have hv2 : (![a, b, c, d] : Fin 4 → F) 2 = c := by rfl
  have hv3 : (![a, b, c, d] : Fin 4 → F) 3 = d := by rfl
  simpa only [hv0, hv1, hv2, hv3, add_assoc] using h

theorem riemann_pullback_components_hasDerivWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t v)) J t)
    (h : F →L[ℝ] F →L[ℝ] ℝ)
    (hmetric : ∀ v w, (S.family.metric t).inner x (ι t v) (ι t w) = h v w)
    (b : Module.Basis Idx ℝ F) (hInv : Idx → Idx → ℝ)
    (hinv : ∀ i j,
      (∑ k, hInv i k * h (b k) (b j)) = (if i = j then 1 else 0) ∧
      (∑ k, h (b i) (b k) * hInv k j) = (if i = j then 1 else 0))
    (m : Fin 4 → Idx) :
    HasDerivWithinAt (fun s => S.base.rm04 s x (fun q => ι s (b (m q))))
      ((deriv (fun s => S.base.rm04 s x) t) (fun q => ι t (b (m q))) +
        ∑ q : Fin 4, ∑ e,
          (∑ f, hInv e f * ricciTensor (I := I) (S.family.metric t) x
            (ι t (b (m q))) (ι t (b f))) *
          S.base.rm04 t x (fun p => ι t (b (Function.update m q e p)))) J t := by
  have htensor := riemann_pullback_hasDerivWithinAt S hS t x ι hι (fun q => b (m q))
  refine htensor.congr_deriv ?_
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [ricciSharp_conjugate_apply_eq_sum (S.family.metric t) x (ι t) h hmetric b hInv hinv]
  let R : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x (S.base.rm04 t x)).compContinuousLinearMap
      (fun _ => (ι t).toContinuousLinearMap)
  change R (Function.update (fun q => b (m q)) q _) = _
  have hsum := R.toMultilinearMap.map_update_sum Finset.univ q
    (fun e => (∑ f, hInv e f * ricciTensor (I := I) (S.family.metric t) x
      (ι t (b (m q))) (ι t (b f))) • b e) (fun q => b (m q))
  refine hsum.trans ?_
  apply Finset.sum_congr rfl
  intro e _
  rw [R.toMultilinearMap.map_update_smul, smul_eq_mul]
  have harg : Function.update (fun q => b (m q)) q (b e) =
      fun p => b (Function.update m q e p) := by
    funext p
    by_cases hp : p = q
    · subst p
      simp
    · simp [hp]
  rw [harg]
  rfl

end DifferentialGeometry.PDE.RicciFlow
