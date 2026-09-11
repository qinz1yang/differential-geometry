import DifferentialGeometry.Geometry.Connection.ConnectionForm
import DifferentialGeometry.Tensor.Multilinear.BundleComp
import DifferentialGeometry.Geometry.Connection.TensorNabla.Multilinear

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem multilinear_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F₂ V₂ x} {x : M}
    (hT : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₂ V₂))) x)
    (X : TangentSpace I x) :
    multilinear
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
      (fun y => (T y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap)) x X =
      (multilinear cov k T x X).compContinuousLinearMap
        (fun _ => (φ x).toContinuousLinearMap) := by
  classical
  let D := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov
  let U := fun y => (T y).compContinuousLinearMap (fun _ : Fin k => (φ y).toContinuousLinearMap)
  have hφx := (hφ x).mdifferentiableAt (by norm_num)
  have hU := hT.multilinear_bundle_comp (fun _ : Fin k => hφx)
  apply Bundle.continuousMultilinearMap.ext
  intro v
  choose Y hY using fun i : Fin k =>
    ContMDiffSection.exists_eq_at (I := I) (F := F₁) (V := V₁) (n := (⊤ : ℕ∞)) x (v i)
  let Z : Fin k → ∀ y, V₂ y := fun i y => φ y (Y i y)
  have hZ : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F₂))
      (fun y => (⟨y, Z i y⟩ : TotalSpace F₂ V₂)) x :=
    fun i => hφx.clm_bundle_apply (Y i).mdifferentiableAt
  have hd := multilinear_apply D k (fun i y => Y i y) hU
    (fun i => (Y i).mdifferentiableAt) X
  have hc := multilinear_apply cov k Z hT hZ X
  have hscalar : (fun y => U y (fun i => Y i y)) =
      (fun y => T y (fun i => Z i y)) := rfl
  have hsum : (∑ i, U x (Function.update (fun j => Y j x) i (D (fun y => Y i y) x X))) =
      ∑ i, T x (Function.update (fun j => Z j x) i (cov (Z i) x X)) := by
    apply Finset.sum_congr rfl
    intro i hi
    change T x (fun j => φ x (Function.update (fun j => Y j x) i
      (D (fun y => Y i y) x X) j)) = _
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      exact map_pullbackFiberwiseLinearEquiv_apply (fun y => (φ y).toLinearEquiv)
        hφ.clm_bundle_map cov (fun y => Y i y) x X
    · simp only [Function.update_of_ne hj]
      rfl
  have hv : (fun i => Y i x) = v := funext hY
  change multilinear D k U x X v =
    multilinear cov k T x X (fun i => φ x (v i))
  rw [← hv, hd, hscalar, hsum]
  exact hc.symm

theorem multilinear_secondCovDeriv_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F₂ V₂ x} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)) 2
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₂ V₂))) x)
    {Y : ∀ y, TangentSpace I y}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (X : TangentSpace I x) :
    let D := multilinear
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let U := fun y => (T y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap)
    D (fun y => D U y (Y y)) x X - D U x (base Y x X) =
      (multilinear cov k (fun y => multilinear cov k T y (Y y)) x X -
        multilinear cov k T x (base Y x X)).compContinuousLinearMap
          (fun _ => (φ x).toContinuousLinearMap) := by
  let D := multilinear
    (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
  let U := fun y => (T y).compContinuousLinearMap (fun _ : Fin k => (φ y).toContinuousLinearMap)
  let W := fun y => multilinear cov k T y (Y y)
  have hTc := (inferInstance : ContMDiffCovariantDerivative (multilinear cov k) ∞).contMDiffAt
    (m := 1) hT (by norm_num)
  have hW := (hTc.mdifferentiableAt (by norm_num)).clm_bundle_apply hY
  have hφx := (hφ x).mdifferentiableAt (by norm_num)
  have hPW := hW.multilinear_bundle_comp (fun _ : Fin k => hφx)
  have hTnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ))
      (fun z => (⟨z, T z⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₂ V₂))) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hT.of_le (by norm_num))).mono (fun _ hy => hy.mdifferentiableAt (by simp))
  have heq : ∀ᶠ y in 𝓝 x, D U y (Y y) =
      (W y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap) := by
    filter_upwards [hTnear] with y hy
    exact multilinear_pullbackFiberwiseLinearEquiv φ hφ cov k hy (Y y)
  have hleft : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₁) ℝ))
      (fun y => (⟨y, D U y (Y y)⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₁) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₁ V₁))) x := by
    apply hPW.congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg (fun v => (⟨y, v⟩ : TotalSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₁) ℝ)
      (Bundle.continuousMultilinearMap ℝ k F₁ V₁))) hy
  have houter := D.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hleft hPW Filter.univ_mem heq
  change D (fun y => D U y (Y y)) x X - D U x (base Y x X) = _
  rw [houter, multilinear_pullbackFiberwiseLinearEquiv φ hφ cov k hW X,
    multilinear_pullbackFiberwiseLinearEquiv φ hφ cov k
      (hT.mdifferentiableAt (by norm_num)) (base Y x X)]
  rfl

end CovariantDerivative
