import DifferentialGeometry.Geometry.Metric.BundleHom
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Topology.VectorBundle.FiniteDimensional

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {FU FV : Type*}
  [NormedAddCommGroup FU] [NormedSpace ℝ FU] [FiniteDimensional ℝ FU]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV] [FiniteDimensional ℝ FV]
  {U V : M → Type*}
  [TopologicalSpace (TotalSpace FU U)]
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [FiberBundle FU U] [VectorBundle ℝ FU U] [ContMDiffVectorBundle ∞ FU U I]
  [IsContMDiffRiemannianBundle I 1 FU U]
  [TopologicalSpace (TotalSpace FV V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle FV V] [VectorBundle ℝ FV V] [ContMDiffVectorBundle 1 FV V I]
  [IsContMDiffRiemannianBundle I 1 FV V]

theorem mvfderiv_hilbertSchmidtInner
    (covU : CovariantDerivative I FU U) (hcovU : covU.IsMetricCompatible)
    (covV : CovariantDerivative I FV V) (hcovV : covV.IsMetricCompatible)
    {A C : ∀ y, U y →L[ℝ] V y} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, FU →L[ℝ] FV))
      (fun y => (⟨y, A y⟩ : TotalSpace (FU →L[ℝ] FV) (fun y => U y →L[ℝ] V y))) x)
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, FU →L[ℝ] FV))
      (fun y => (⟨y, C y⟩ : TotalSpace (FU →L[ℝ] FV) (fun y => U y →L[ℝ] V y))) x)
    (v : TangentSpace I x) :
    let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y => VectorBundle.finiteDimensional ℝ FU U y
    mvfderiv I (fun y => ContinuousLinearMap.hilbertSchmidtInner (A y) (C y)) x v =
      ContinuousLinearMap.hilbertSchmidtInner
        (homBundleCovariantDerivativeGen I M FU U FV V covU covV A x v) (C x) +
      ContinuousLinearMap.hilbertSchmidtInner (A x)
        (homBundleCovariantDerivativeGen I M FU U FV V covU covV C x v) := by
  classical
  dsimp only
  let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y => VectorBundle.finiteDimensional ℝ FU U y
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  rw [← hX]
  let b := stdOrthonormalBasis ℝ (U x)
  obtain ⟨S, hS, hxS, e, he, heON, hex⟩ :=
    exists_contMDiff_orthonormal_sections (I := I) (F := FU) (m := 1) x b b.orthonormal
  have hediff (i) : MDifferentiableAt I (I.prod 𝓘(ℝ, FU)) (T% (e i)) x :=
    ((he i).contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
  have hAdiff (i) : MDifferentiableAt I (I.prod 𝓘(ℝ, FV))
      (T% (fun y => A y (e i y))) x := hA.clm_bundle_apply (hediff i)
  have hCdiff (i) : MDifferentiableAt I (I.prod 𝓘(ℝ, FV))
      (T% (fun y => C y (e i y))) x := hC.clm_bundle_apply (hediff i)
  have hsum (y : M) (hy : y ∈ S) :
      ContinuousLinearMap.hilbertSchmidtInner (A y) (C y) =
        ∑ i, inner ℝ (A y (e i y)) (C y (e i y)) := by
    have hdim : Fintype.card (Fin (Module.finrank ℝ (U x))) = Module.finrank ℝ (U y) := by
      rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ FU U x,
        VectorBundle.finrank_eq ℝ FU U y]
    let bY := OrthonormalBasis.mk (heON y hy)
      ((heON y hy).linearIndependent.span_eq_top_of_card_eq_finrank' hdim).ge
    simpa only [bY, OrthonormalBasis.coe_mk] using
      ContinuousLinearMap.hilbertSchmidtInner_eq_sum bY (A y) (C y)
  have hderivsum : mvfderiv I
      (fun y => ContinuousLinearMap.hilbertSchmidtInner (A y) (C y)) x (X x) =
        ∑ i, mvfderiv I (fun y => inner ℝ (A y (e i y)) (C y (e i y))) x (X x) := by
    have hgerm : (fun y => ContinuousLinearMap.hilbertSchmidtInner (A y) (C y)) =ᶠ[𝓝 x]
        (fun y => ∑ i, inner ℝ (A y (e i y)) (C y (e i y))) :=
      eventually_of_mem (hS.mem_nhds hxS) hsum
    change mfderiv I 𝓘(ℝ, ℝ) _ x (X x) = _
    rw [hgerm.mfderiv_eq]
    exact mvfderiv_finset_sum_at' Finset.univ _ (X x)
      (fun i _ => (hAdiff i).inner_bundle (hCdiff i))
  let K : U x →L[ℝ] U x :=
    (b.toBasis.constr ℝ (fun i => covU (e i) x (X x))).toContinuousLinearMap
  have hK (i) : K (b i) = covU (e i) x (X x) := by
    exact b.toBasis.constr_basis (S := ℝ) (fun i => covU (e i) x (X x)) i
  have hskew (i j) :
      inner ℝ (K (b i)) (b j) + inner ℝ (b i) (K (b j)) = 0 := by
    have hgerm : (fun y => inner ℝ (e i y) (e j y)) =ᶠ[𝓝 x]
        (fun _ => inner ℝ (b i) (b j)) := by
      filter_upwards [hS.mem_nhds hxS] with y hy
      rw [orthonormal_iff_ite.mp (heON y hy), orthonormal_iff_ite.mp b.orthonormal]
    have hz : mvfderiv I (fun y => inner ℝ (e i y) (e j y)) x (X x) = 0 := by
      change mfderiv I 𝓘(ℝ, ℝ) _ x (X x) = 0
      rw [hgerm.mfderiv_eq]
      exact congrArg (fun L => L (X x)) (mvfderiv_const (I := I) (inner ℝ (b i) (b j)))
    rw [hcovU.mvfderiv_inner_eq (fun y => X y) (hediff i) (hediff j)] at hz
    simpa only [hK, hex] using hz
  have hadj : K.adjoint = -K := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply InnerProductSpace.ext_inner_right_basis b.toBasis
    intro j
    change inner ℝ (K.adjoint (b i)) (b j) = inner ℝ (-(K (b i))) (b j)
    rw [K.adjoint_inner_left, inner_neg_left]
    linear_combination hskew i j
  let DA := homBundleCovariantDerivativeGen I M FU U FV V covU covV A x (X x)
  let DC := homBundleCovariantDerivativeGen I M FU U FV V covU covV C x (X x)
  have hDA (i) : covV (fun y => A y (e i y)) x (X x) =
      DA (b i) + A x (K (b i)) := by
    have h := homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M FU U FV V covU covV A hA X.mdifferentiableAt (hediff i)
    rw [hex i] at h
    rw [hK]
    exact eq_add_of_sub_eq h.symm
  have hDC (i) : covV (fun y => C y (e i y)) x (X x) =
      DC (b i) + C x (K (b i)) := by
    have h := homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M FU U FV V covU covV C hC X.mdifferentiableAt (hediff i)
    rw [hex i] at h
    rw [hK]
    exact eq_add_of_sub_eq h.symm
  rw [hderivsum]
  simp_rw [hcovV.mvfderiv_inner_eq (fun y => X y) (hAdiff _) (hCdiff _),
    hDA, hDC, hex, inner_add_left, inner_add_right]
  change (∑ i, ((inner ℝ (DA (b i)) (C x (b i)) +
      inner ℝ (A x (K (b i))) (C x (b i))) +
      (inner ℝ (A x (b i)) (DC (b i)) +
      inner ℝ (A x (b i)) (C x (K (b i)))))) = _
  simp only [Finset.sum_add_distrib]
  have hzero := ContinuousLinearMap.hilbertSchmidtInner_comp_add_eq_zero (A x) (C x) K hadj
  simp only [ContinuousLinearMap.hilbertSchmidtInner_eq_sum b,
    ContinuousLinearMap.comp_apply] at hzero ⊢
  linear_combination hzero


theorem homBundleCovariantDerivativeGen_isMetricCompatible
    (covU : CovariantDerivative I FU U) (hcovU : covU.IsMetricCompatible)
    (covV : CovariantDerivative I FV V) (hcovV : covV.IsMetricCompatible) :
    let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y => VectorBundle.finiteDimensional ℝ FU U y
    letI : RiemannianBundle (fun y => U y →L[ℝ] V y) :=
      ⟨(homContMDiffRiemannianMetric (IB := I) (n := 1) (FU := FU) (FV := FV) U V).toRiemannianMetric⟩
    let homNorm : ∀ y, NormedAddCommGroup (U y →L[ℝ] V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y => U y →L[ℝ] V y) y
    let _ : ∀ y, SeminormedAddCommGroup (U y →L[ℝ] V y) :=
      fun y => (homNorm y).toSeminormedAddCommGroup
    let _ : ∀ y, InnerProductSpace ℝ (U y →L[ℝ] V y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := fun y => U y →L[ℝ] V y) y
    CovariantDerivative.IsMetricCompatible (I := I) (F := FU →L[ℝ] FV)
      (V := fun y => U y →L[ℝ] V y)
      (homBundleCovariantDerivativeGen I M FU U FV V covU covV) := by
  let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y => VectorBundle.finiteDimensional ℝ FU U y
  let g := homContMDiffRiemannianMetric (IB := I) (n := 1) (FU := FU) (FV := FV) U V
  let _ : RiemannianBundle (fun y => U y →L[ℝ] V y) := ⟨g.toRiemannianMetric⟩
  let homNorm : ∀ y, NormedAddCommGroup (U y →L[ℝ] V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun y => U y →L[ℝ] V y) y
  let _ : ∀ y, SeminormedAddCommGroup (U y →L[ℝ] V y) :=
    fun y => (homNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (U y →L[ℝ] V y) := fun y =>
    Bundle.instInnerProductSpaceReal (E := fun y => U y →L[ℝ] V y) y
  apply (CovariantDerivative.isMetricCompatible_iff _).mpr
  intro x X A C _ hA hC
  have hinner (y : M) (a c : U y →L[ℝ] V y) :
      inner ℝ a c = ContinuousLinearMap.hilbertSchmidtInner a c := by
    change ContinuousLinearMap.hilbertSchmidtInnerSL a c = _
    exact ContinuousLinearMap.hilbertSchmidtInnerSL_apply a c
  simp only [hinner]
  exact mvfderiv_hilbertSchmidtInner covU hcovU covV hcovV hA hC (X x)

end DifferentialGeometry.HomConnectionGen
