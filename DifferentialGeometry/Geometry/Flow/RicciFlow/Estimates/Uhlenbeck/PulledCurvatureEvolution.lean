import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureDerivative
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackTensor
import DifferentialGeometry.Geometry.Connection.Laplacian.CovariantTensor

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

theorem riemann_pullback_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t v)) J t)
    (v : Fin 4 → F) :
    HasDerivWithinAt (fun s => S.base.rm04 s x (fun q => ι s (v q)))
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x (fun q => ι t (v q)) -
        2 * curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x
          (fun q => ι t (v q))) J t := by
  have h := riemann_pullback_four_slots_hasDerivWithinAt S hS t x ι hι
    (v 0) (v 1) (v 2) (v 3)
  have hv (s : ℝ) : vec4 (ι s (v 0)) (ι s (v 1)) (ι s (v 2)) (ι s (v 3)) =
      fun q => ι s (v q) := by
    funext q
    fin_cases q <;> rfl
  rw [show deriv (fun s => S.base.rm04 s x) (t : ℝ) =
      roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
        ricciDrift04 (S.family.metric t) x from
      (riemann_tensor_hasDerivAt_of_solution S hS t x).deriv] at h
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
    ricciDrift04_apply] at h
  simp only [SolutionFamily.rm04, metricRm04_apply, SolutionOn.family_metric] at h ⊢
  simp only [hv] at h
  exact h.congr_deriv (by ring)

theorem riemann_pullback_components_hasDerivWithinAt_of_ricci_ode
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
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x
          (fun q => ι t (b (m q))) +
        2 * ((-bComp hInv (fun a b' c d => S.base.rm04 t x
              (vec4 (ι t (b a)) (ι t (b b')) (ι t (b c)) (ι t (b d))))
              (m 0) (m 1) (m 2) (m 3)) -
          (-bComp hInv (fun a b' c d => S.base.rm04 t x
              (vec4 (ι t (b a)) (ι t (b b')) (ι t (b c)) (ι t (b d))))
              (m 0) (m 1) (m 3) (m 2)) +
          (-bComp hInv (fun a b' c d => S.base.rm04 t x
              (vec4 (ι t (b a)) (ι t (b b')) (ι t (b c)) (ι t (b d))))
              (m 0) (m 2) (m 1) (m 3)) -
          (-bComp hInv (fun a b' c d => S.base.rm04 t x
              (vec4 (ι t (b a)) (ι t (b b')) (ι t (b c)) (ι t (b d))))
              (m 0) (m 3) (m 1) (m 2)))) J t := by
  have hderiv := riemann_pullback_hasDerivWithinAt_of_ricci_ode S hS t x ι hι
    (fun q => b (m q))
  rw [curvatureQuadraticCombination_apply_isometry_basis (S.family.metric t) x
    (ι t) h hmetric b hInv hinv] at hderiv
  exact hderiv.congr_deriv (by ring)

theorem riemann_pullback_tensor_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : ℝ → F ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ∀ v, HasDerivWithinAt (fun s => ι s v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t v)) J t) :
    HasDerivWithinAt
      (fun s => (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x (S.base.rm04 s x)).compContinuousLinearMap
        (fun _ => (ι s).toContinuousLinearMap))
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
        (roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
          (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x)).compContinuousLinearMap
        (fun _ => (ι t).toContinuousLinearMap)) J t := by
  let b := (coordBasisAt (I := I) x).map (ι t).symm.toLinearEquiv
  apply ContinuousMultilinearMap.hasDerivWithinAt_of_basis_eval b
  intro m
  have hd := riemann_pullback_hasDerivWithinAt_of_ricci_ode S hS t x ι hι
    (fun q => b (m q))
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using hd

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

private theorem rawBundleConnLap_pullback_riemann
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (x : M) :
    rawBundleConnLap (S.family.metric t)
      (CovariantDerivative.multilinear
        (CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map (LeviCivita (S.family.metric t))) 4)
      (fun y => (S.base.rm04 t y).compContinuousLinearMap
        (fun _ => (ι y).toContinuousLinearMap)) x =
      (rawBundleConnLap (S.family.metric t)
        (CovariantDerivative.multilinear (LeviCivita (S.family.metric t)) 4)
        (fun y => S.base.rm04 t y) x).compContinuousLinearMap
          (fun _ => (ι x).toContinuousLinearMap) := by
  apply rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    ι hι (S.family.metric t) (LeviCivita (S.family.metric t)) 4
  exact ((S.base.rm04 t).contMDiff x).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

theorem riemann_pullback_tensor_hasDerivWithinAt_laplacian_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (x : M) (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    HasDerivWithinAt
      (fun s => (S.base.rm04 s x).compContinuousLinearMap
        (fun _ => (ι s x).toContinuousLinearMap))
      (rawBundleConnLap (S.family.metric t)
        (CovariantDerivative.multilinear
          (CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map
            (LeviCivita (S.family.metric t))) 4)
        (fun y => (S.base.rm04 t y).compContinuousLinearMap
          (fun _ => (ι t y).toContinuousLinearMap)) x -
        (2 : ℝ) • (curvatureQuadraticCombination (S.family.metric t)
          (S.base.rm04 t) x).compContinuousLinearMap
            (fun _ => (ι t x).toContinuousLinearMap)) J t := by
  have hd := riemann_pullback_tensor_hasDerivWithinAt_of_ricci_ode S hS t x
    (fun s => ι s x) hode
  apply hd.congr_deriv
  rw [rawBundleConnLap_pullback_riemann S t (ι t) hι x,
    rawBundleConnLap_multilinear_eq_roughLap0SField]
  rfl

theorem riemann_pullback_components_hasDerivWithinAt_laplacian_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (x : M) (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t)
    (h : V x →L[ℝ] V x →L[ℝ] ℝ)
    (hmetric : ∀ v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = h v w)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (V x)) (hInv : Fin d → Fin d → ℝ)
    (hinv : ∀ i j,
      (∑ k, hInv i k * h (b k) (b j)) = (if i = j then 1 else 0) ∧
      (∑ k, h (b i) (b k) * hInv k j) = (if i = j then 1 else 0))
    (m : Fin 4 → Fin d) :
    let R := fun a b' c d' => S.base.rm04 t x
      (vec4 (ι t x (b a)) (ι t x (b b')) (ι t x (b c)) (ι t x (b d')))
    HasDerivWithinAt (fun s => S.base.rm04 s x (fun q => ι s x (b (m q))))
      ((rawBundleConnLap (S.family.metric t)
          (CovariantDerivative.multilinear
            (CovariantDerivative.pullbackFiberwiseLinearEquiv
              (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map
              (LeviCivita (S.family.metric t))) 4)
          (fun y => (S.base.rm04 t y).compContinuousLinearMap
            (fun _ => (ι t y).toContinuousLinearMap)) x) (fun q => b (m q)) +
        2 * ((-bComp hInv R (m 0) (m 1) (m 2) (m 3)) -
          (-bComp hInv R (m 0) (m 1) (m 3) (m 2)) +
          (-bComp hInv R (m 0) (m 2) (m 1) (m 3)) -
          (-bComp hInv R (m 0) (m 3) (m 1) (m 2)))) J t := by
  have hd := riemann_pullback_components_hasDerivWithinAt_of_ricci_ode S hS t x
    (fun s => ι s x) hode h hmetric b hInv hinv m
  apply hd.congr_deriv
  rw [rawBundleConnLap_pullback_riemann S t (ι t) hι x,
    rawBundleConnLap_multilinear_eq_roughLap0SField]
  rfl

theorem exists_uhlenbeck_isometry_with_pulled_curvature_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hJD : J ⊆ D.regular)
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = h.inner x v w) ∧
      ∀ t ∈ J, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
        (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
        ∀ x,
          HasDerivWithinAt
            (fun s => (S.base.rm04 s x).compContinuousLinearMap
              (fun _ => (ι s x).toContinuousLinearMap))
            (rawBundleConnLap (S.family.metric t)
              (CovariantDerivative.multilinear
                (CovariantDerivative.pullbackFiberwiseLinearEquiv
                  (fun y => (ι t y).toLinearEquiv) hιt.clm_bundle_map
                  (LeviCivita (S.family.metric t))) 4)
              (fun y => (S.base.rm04 t y).compContinuousLinearMap
                (fun _ => (ι t y).toContinuousLinearMap)) x -
              (2 : ℝ) • (curvatureQuadraticCombination (S.family.metric t)
                (S.base.rm04 t) x).compContinuousLinearMap
                  (fun _ => (ι t x).toContinuousLinearMap)) J t ∧
          ∀ (d : ℕ) (b : Module.Basis (Fin d) ℝ (V x)),
            let hInv := basisInvMetric (S.family.metric t₀) x
              (b.map (ι₀ x).toLinearEquiv)
            (∀ i j,
              (∑ k, hInv i k * h.inner x (b k) (b j)) = (if i = j then 1 else 0) ∧
              (∑ k, h.inner x (b i) (b k) * hInv k j) = (if i = j then 1 else 0)) ∧
            ∀ m : Fin 4 → Fin d,
              let R := fun a b' c d' => S.base.rm04 t x
                (vec4 (ι t x (b a)) (ι t x (b b')) (ι t x (b c)) (ι t x (b d')))
              HasDerivWithinAt
                (fun s => S.base.rm04 s x (fun q => ι s x (b (m q))))
                ((rawBundleConnLap (S.family.metric t)
                    (CovariantDerivative.multilinear
                      (CovariantDerivative.pullbackFiberwiseLinearEquiv
                        (fun y => (ι t y).toLinearEquiv) hιt.clm_bundle_map
                        (LeviCivita (S.family.metric t))) 4)
                    (fun y => (S.base.rm04 t y).compContinuousLinearMap
                      (fun _ => (ι t y).toContinuousLinearMap)) x) (fun q => b (m q)) +
                  2 * ((-bComp hInv R (m 0) (m 1) (m 2) (m 3)) -
                    (-bComp hInv R (m 0) (m 1) (m 3) (m 2)) +
                    (-bComp hInv R (m 0) (m 2) (m 1) (m 3)) -
                    (-bComp hInv R (m 0) (m 3) (m 1) (m 2)))) J t := by
  obtain ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval S hS hJ ht₀ hJD h ι₀ hι₀ h₀
  refine ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric, ?_⟩
  intro t ht
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hιt := (hsmooth.comp_contMDiff hpair (fun x => ⟨ht, Set.mem_univ x⟩)).of_le
    (show (1 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  refine ⟨hιt, ?_⟩
  intro x
  refine ⟨riemann_pullback_tensor_hasDerivWithinAt_laplacian_of_ricci_ode S hS
    ⟨t, hJD ht⟩ ι hιt x (fun v => hderiv x v t ht), ?_⟩
  intro d b
  let hInv := basisInvMetric (S.family.metric t₀) x (b.map (ι₀ x).toLinearEquiv)
  have hinv : ∀ i j,
      (∑ k, hInv i k * h.inner x (b k) (b j)) = (if i = j then 1 else 0) ∧
      (∑ k, h.inner x (b i) (b k) * hInv k j) = (if i = j then 1 else 0) := by
    intro i j
    have hz := basisInvMetric_isInverse (I := I) (S.family.metric t₀) x
      (b.map (ι₀ x).toLinearEquiv) i j
    change (∑ k, hInv i k * (S.family.metric t₀).inner x
        (ι₀ x (b k)) (ι₀ x (b j))) = _ ∧
      (∑ k, (S.family.metric t₀).inner x (ι₀ x (b i)) (ι₀ x (b k)) * hInv k j) = _ at hz
    simpa only [h₀] using hz
  refine ⟨hinv, ?_⟩
  intro m
  exact riemann_pullback_components_hasDerivWithinAt_laplacian_of_ricci_ode S hS
    ⟨t, hJD ht⟩ ι hιt x (fun v => hderiv x v t ht)
    (h.inner x) (hmetric t ht x) b hInv hinv m

end DifferentialGeometry.PDE.RicciFlow
