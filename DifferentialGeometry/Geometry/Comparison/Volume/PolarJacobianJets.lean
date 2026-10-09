import DifferentialGeometry.Geometry.Comparison.Volume.PolarTwoJet
import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.Derivative
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold Matrix
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

theorem matrixCurve_det_sqrt_jets_at_identity
    {n : ℕ}
    (G B : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, ContDiff ℝ ∞ (fun t ↦ G t i j))
    (hGB : ∀ t i j, HasDerivAt (fun s ↦ G s i j) (B t i j) t)
    (hBC : ∀ i j, HasDerivAt (fun t ↦ B t i j) (C i j) 0)
    (hG0 : G 0 = 1) (hB0 : B 0 = 0) :
    iteratedDeriv 1 (fun t ↦ (G t).det) 0 = 0 ∧
      iteratedDeriv 2 (fun t ↦ (G t).det) 0 = Matrix.trace C ∧
      iteratedDeriv 1 (fun t ↦ Real.sqrt (G t).det) 0 = 0 ∧
      iteratedDeriv 2 (fun t ↦ Real.sqrt (G t).det) 0 =
        (1 / 2 : ℝ) * Matrix.trace C := by
  classical
  have hdet (t : ℝ) : HasDerivAt (fun s ↦ (G s).det)
      (Matrix.trace ((G t).adjugate * B t)) t :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_det_eq_trace_adjugate_mul
      G (B t) t (hGB t)
  have hdet_deriv : deriv (fun t ↦ (G t).det) =
      fun t ↦ Matrix.trace ((G t).adjugate * B t) := by
    funext t
    exact (hdet t).deriv
  have hadj : ∀ i j, DifferentiableAt ℝ (fun t ↦ (G t).adjugate i j) 0 := by
    intro i j
    exact (DifferentialGeometry.Analysis.contDiff_adjugate_of_entries G hG i j).differentiable
      (by simp) 0
  have htrace : HasDerivAt
      (fun t ↦ Matrix.trace ((G t).adjugate * B t))
      (Matrix.trace C) 0 := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply]
    have houter : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
        (fun t ↦ ∑ j, (G t).adjugate i j * B t j i) (C i i) 0 := by
      intro i hi
      have hinner : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
          (fun t ↦ (G t).adjugate i j * B t j i)
          ((1 : Matrix (Fin n) (Fin n) ℝ) i j * C j i) 0 := by
        intro j hj
        have hmul := (hadj i j).hasDerivAt.mul (hBC j i)
        change HasDerivAt (fun t ↦ (G t).adjugate i j * B t j i) _ 0 at hmul
        rw [hG0, hB0] at hmul
        simpa only [Matrix.adjugate_one, Matrix.zero_apply, mul_zero,
          zero_add] using hmul
      have hsum := HasDerivAt.fun_sum hinner
      simpa [Matrix.one_apply] using hsum
    exact HasDerivAt.fun_sum houter
  have hdetTwo : iteratedDeriv 2 (fun t ↦ (G t).det) 0 =
      Matrix.trace C := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
      hdet_deriv]
    exact htrace.deriv
  have hdetOneDeriv : deriv (fun t ↦ (G t).det) 0 = 0 := by
    rw [hdet_deriv]
    change Matrix.trace ((G 0).adjugate * B 0) = 0
    rw [hG0, hB0]
    simp
  have hdetOne : iteratedDeriv 1 (fun t ↦ (G t).det) 0 = 0 := by
    rw [iteratedDeriv_one]
    exact hdetOneDeriv
  have hdetZero : (G 0).det = 1 := by
    rw [hG0, Matrix.det_one]
  have hpos : 0 < (G 0).det := by
    rw [hdetZero]
    norm_num
  have hsqrtOneHas :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      G (B 0) 0 (hGB 0) hpos
  have hsqrtOne : iteratedDeriv 1
      (fun t ↦ Real.sqrt (G t).det) 0 = 0 := by
    rw [iteratedDeriv_one]
    have : HasDerivAt (fun t ↦ Real.sqrt (G t).det) 0 0 := by
      rw [hB0] at hsqrtOneHas
      simpa only [Matrix.mul_zero, Matrix.trace_zero, mul_zero, zero_mul]
        using hsqrtOneHas
    exact this.deriv
  have hdetCont : ContDiff ℝ ∞ (fun t ↦ (G t).det) :=
    DifferentialGeometry.Analysis.contDiff_det_of_entries G hG
  have hsqrt : ContDiffAt ℝ 2 Real.sqrt ((G 0).det) := by
    rw [hdetZero]
    exact Real.contDiffAt_sqrt one_ne_zero
  have hcomp := iteratedDeriv_comp_two (g := Real.sqrt)
    (f := fun t ↦ (G t).det) (x := (0 : ℝ)) hsqrt
    (hdetCont.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
  change iteratedDeriv 2 (Real.sqrt ∘ fun t ↦ (G t).det) 0 = _ at hcomp
  rw [hdetZero, hdetOneDeriv, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add, hdetTwo] at hcomp
  have hsqrtDeriv : deriv Real.sqrt 1 = (1 / 2 : ℝ) := by
    simpa using (Real.hasDerivAt_sqrt one_ne_zero).deriv
  rw [hsqrtDeriv] at hcomp
  have hsqrtTwo : iteratedDeriv 2
      (fun t ↦ Real.sqrt (G t).det) 0 = (1 / 2 : ℝ) * Matrix.trace C := by
    change iteratedDeriv 2 (Real.sqrt ∘ fun t ↦ (G t).det) 0 = _
    exact hcomp
  exact ⟨hdetOne, hdetTwo, hsqrtOne, hsqrtTwo⟩

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_first_jet_swap_last
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b c : E) :
    iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        (fun _ ↦ a) b c =
      iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        (fun _ ↦ a) c b := by
  have hfun : (fun z : E ↦ intrinsicFrameMetric (I := I) g hEnorm p z b c) =
      (fun z : E ↦ intrinsicFrameMetric (I := I) g hEnorm p z c b) := by
    funext z
    exact g.symm _ _ _
  have h := congrArg (fun f : E → ℝ ↦
      iteratedFDeriv ℝ 1 f 0 (fun _ ↦ a)) hfun
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hmetric_b := hmetric.clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ b))
  have hmetric_c := hmetric.clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ c))
  have hb :
      iteratedFDeriv ℝ 1 (fun z : E ↦
          intrinsicFrameMetric (I := I) g hEnorm p z b c) 0 (fun _ ↦ a) =
        iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          (fun _ ↦ a) b c := by
    rw [iteratedFDeriv_clm_apply_const_apply hmetric_b (by simp),
      iteratedFDeriv_clm_apply_const_apply hmetric (by simp)]
  have hc :
      iteratedFDeriv ℝ 1 (fun z : E ↦
          intrinsicFrameMetric (I := I) g hEnorm p z c b) 0 (fun _ ↦ a) =
        iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          (fun _ ↦ a) c b := by
    rw [iteratedFDeriv_clm_apply_const_apply hmetric_c (by simp),
      iteratedFDeriv_clm_apply_const_apply hmetric (by simp)]
  exact hb.symm.trans (h.trans hc)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_first_jet_diag_first
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a c : E) :
    iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        (fun _ ↦ a) a c = 0 := by
  have hline : (fun t : ℝ ↦
      intrinsicFrameMetric (I := I) g hEnorm p (t • a) a c) =
      (fun _ : ℝ ↦ Inner.inner ℝ a c) := by
    funext t
    by_cases ht : t = 0
    · subst t
      rw [zero_smul]
      change intrinsicFrameMetric (I := I) g (fun x v ↦ hEnorm x v) p 0 a c =
        Inner.inner ℝ a c
      have hz := intrinsicFrameMetric_zero (I := I) g
        (fun x v ↦ hEnorm x v) p
      calc
        intrinsicFrameMetric (I := I) g (fun x v ↦ hEnorm x v) p 0 a c =
            (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) a c :=
          congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ ↦ A a c) hz
        _ = Inner.inner ℝ a c := rfl
    · have hrad := intrinsicFrameMetric_radial (I := I) g hEnorm p (t • a) c
      have hmul : t * intrinsicFrameMetric (I := I) g hEnorm p (t • a) a c =
          t * Inner.inner ℝ a c := by
        simpa only [map_smul, _root_.smul_apply, smul_eq_mul,
          real_inner_smul_left] using hrad
      exact (mul_left_cancel₀ ht hmul)
  have h := congrArg (fun f : ℝ → ℝ ↦
      iteratedFDeriv ℝ 1 f 0 (fun _ ↦ (1 : ℝ))) hline
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hmetric_a := hmetric.clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ a))
  have hbridge :
      iteratedFDeriv ℝ 1 (fun z : E ↦
          intrinsicFrameMetric (I := I) g hEnorm p z a c) 0 (fun _ ↦ a) =
        iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          (fun _ ↦ a) a c := by
    rw [iteratedFDeriv_clm_apply_const_apply hmetric_a (by simp),
      iteratedFDeriv_clm_apply_const_apply hmetric (by simp)]
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ a
  have hscalar :
      iteratedFDeriv ℝ 1 (fun t : ℝ ↦
          intrinsicFrameMetric (I := I) g hEnorm p (t • a) a c) 0
          (fun _ ↦ (1 : ℝ)) =
        iteratedFDeriv ℝ 1 (fun z : E ↦
          intrinsicFrameMetric (I := I) g hEnorm p z a c) 0 (fun _ ↦ a) := by
    have hscalarCont : ContDiff ℝ ∞ (fun z : E ↦
        intrinsicFrameMetric (I := I) g hEnorm p z a c) :=
      (hmetric.clm_apply
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ a))).clm_apply
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ c))
    have hcomp := L.iteratedFDeriv_comp_right hscalarCont 0
      (i := 1) (by simp)
    have happ := congrArg (fun A ↦ A (fun _ ↦ (1 : ℝ))) hcomp
    have hL :
        (fun z : E ↦ intrinsicFrameMetric (I := I) g hEnorm p z a c) ∘ L =
          (fun t : ℝ ↦ intrinsicFrameMetric (I := I) g hEnorm p (t • a) a c) := by
      funext t
      simp only [Function.comp_apply, L,
        ContinuousLinearMap.toSpanSingleton_apply]
    rw [hL] at happ
    simpa only [L, ContinuousLinearMap.toSpanSingleton_apply, zero_smul,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, one_smul]
      using happ
  rw [← hbridge, ← hscalar]
  rw [iteratedFDeriv_const_of_ne (by norm_num)
    (Inner.inner ℝ a c)] at h
  simpa using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_first_jet_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b c : E) :
    iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        (fun _ ↦ a) b c = 0 := by
  let hNorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v ↦ hEnorm x v
  change iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0
    (fun _ ↦ a) b c = 0
  let T : E → E → E → ℝ := fun x y z ↦
    iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0
      (fun _ ↦ x) y z
  have hanti : ∀ x y z : E, T x y z + T y x z = 0 := by
    intro x y z
    have hdiag := intrinsicFrameMetric_first_jet_diag_first
      (I := I) g hNorm p (x + y) z
    change T (x + y) (x + y) z = 0 at hdiag
    have htuple : (fun _ : Fin 1 ↦ x + y) =
        (fun _ : Fin 1 ↦ x) + (fun _ : Fin 1 ↦ y) := by
      funext i
      rfl
    dsimp only [T] at hdiag ⊢
    rw [htuple] at hdiag
    have hmap :
        iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0
            ((fun _ : Fin 1 ↦ x) + (fun _ : Fin 1 ↦ y)) =
          iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0
              (fun _ : Fin 1 ↦ x) +
            iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0
              (fun _ : Fin 1 ↦ y) := by
      let F := iteratedFDeriv ℝ 1
        (intrinsicFrameMetric (I := I) g hNorm p) 0
      have hmap' := F.map_update_add (fun _ : Fin 1 ↦ (0 : E)) (0 : Fin 1) x y
      have hconst (z : E) : Function.update (fun _ : Fin 1 ↦ (0 : E)) 0 z =
          (fun _ : Fin 1 ↦ z) := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simp
      rw [hconst (x + y), hconst x, hconst y] at hmap'
      exact hmap'
    rw [hmap] at hdiag
    simp only [_root_.add_apply] at hdiag
    have hxmap :=
      ((iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0)
        (fun _ : Fin 1 ↦ x)).map_add x y
    have hymap :=
      ((iteratedFDeriv ℝ 1 (intrinsicFrameMetric (I := I) g hNorm p) 0)
        (fun _ : Fin 1 ↦ y)).map_add x y
    rw [hxmap, hymap] at hdiag
    simp only [_root_.add_apply] at hdiag
    rw [intrinsicFrameMetric_first_jet_diag_first (I := I) g hNorm p x z,
      intrinsicFrameMetric_first_jet_diag_first (I := I) g hNorm p y z] at hdiag
    linarith
  have hsab : T a b c = T a c b :=
    intrinsicFrameMetric_first_jet_swap_last (I := I) g hNorm p a b c
  have hsca : T c a b = T c b a :=
    intrinsicFrameMetric_first_jet_swap_last (I := I) g hNorm p c a b
  have hsba : T b a c = T b c a :=
    intrinsicFrameMetric_first_jet_swap_last (I := I) g hNorm p b a c
  have hac := hanti a c b
  have hcb := hanti c b a
  have hba := hanti b a c
  change T a b c = 0
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_radial_first_jet_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E) (i j : Fin (Module.finrank ℝ E)) :
    iteratedDeriv 1 (fun t : ℝ ↦
      intrinsicFrameGram (I := I) g hEnorm p (t • u) i j) 0 = 0 := by
  let ei : E := (stdOrthonormalBasis ℝ E) i
  let ej : E := (stdOrthonormalBasis ℝ E) j
  let F : E → ℝ := fun z ↦ intrinsicFrameMetric (I := I) g hEnorm p z ei ej
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hF : ContDiff ℝ ∞ F :=
    (hmetric.clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ ei))).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ ej))
  have hambient : iteratedFDeriv ℝ 1 F 0 (fun _ ↦ u) = 0 := by
    dsimp only [F]
    rw [iteratedFDeriv_clm_apply_const_apply
        (hmetric.clm_apply
          (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ ei))) (by simp),
      iteratedFDeriv_clm_apply_const_apply hmetric (by simp)]
    exact intrinsicFrameMetric_first_jet_zero (I := I) g hEnorm p u ei ej
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ u
  have hcomp := L.iteratedFDeriv_comp_right hF 0 (i := 1) (by simp)
  have happ := congrArg (fun A ↦ A (fun _ ↦ (1 : ℝ))) hcomp
  have hFL : F ∘ L = (fun t : ℝ ↦
      intrinsicFrameGram (I := I) g hEnorm p (t • u) i j) := by
    funext t
    simp only [Function.comp_apply, F, L,
      ContinuousLinearMap.toSpanSingleton_apply, intrinsicFrameGram, ei, ej]
  rw [hFL] at happ
  have hrhs :
      ((iteratedFDeriv ℝ 1 F (L 0)).compContinuousLinearMap
          (fun _ ↦ L)) (fun _ ↦ (1 : ℝ)) =
        iteratedFDeriv ℝ 1 F 0 (fun _ ↦ u) := by
    simp only [L, map_zero,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [iteratedDeriv_eq_iteratedFDeriv]
  exact happ.trans (hrhs.trans hambient)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunch3_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1) = p := by
  simp only [intrinsicLaunch3, zero_smul, add_zero]
  calc
    intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p) 1 =
        intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p) 0 := by
      simpa using intrinsicGeodesic_smul (I := I) g hEnorm p
        (0 : TangentSpace I p) 0
    _ = p := intrinsicGeodesic_zero (I := I) g hEnorm p 0

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJ_pole_one
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1) : E) = b := by
  let c : E := (normalFrame (I := I) g p).symm
    (show TangentSpace I p from b)
  have hc : (normalFrame (I := I) g p c : E) = b := by
    exact congrArg (fun v : TangentSpace I p ↦ (v : E))
      ((normalFrame (I := I) g p).apply_symm_apply
        (show TangentSpace I p from b))
  have hJ := congrArg (fun v ↦ (v : E))
    (intrinsicLaunchJ_zero (I := I) g hEnorm p 0 a b 1)
  have hframe := congrArg (fun v ↦ (v : E))
    (intrinsicFrame_deriv (I := I) g (fun x v ↦ hEnorm x v) p 0 c)
  have hframe0 := congrArg (fun D ↦ (D c : E))
    (intrinsicFrame_deriv_zero (I := I) g (fun x v ↦ hEnorm x v) p)
  rw [map_zero, hc] at hframe
  change (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1) : E) = b
  exact hJ.trans (hframe.symm.trans (hframe0.trans hc))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicMetricJet_two_zero_of_launch_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u b : E)
    (hone : (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 1 (0, 1) : E) = 0)
    (htwo : (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 2 (0, 1) : E) =
      -(1 / 3 : ℝ) •
        (riemannOp (LeviCivita (I := I) g) p
          (show TangentSpace I p from b)
          (show TangentSpace I p from u)
          (show TangentSpace I p from u) : E)) :
    intrinsicMetricJet (I := I) g hEnorm p 0 u b 2 0 =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (LeviCivita (I := I) g) p
          (show TangentSpace I p from b)
          (show TangentSpace I p from u)
          (show TangentSpace I p from u))
        (show TangentSpace I p from b) := by
  unfold intrinsicMetricJet
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.reduceSub,
    Nat.choose_self, Nat.choose_one_right, Nat.cast_ofNat,
    intrinsicLaunchJet_zero]
  rw [intrinsicLaunch3_pole (I := I) g hEnorm p u b]
  rw [intrinsicLaunchJ_pole_one (I := I) g hEnorm p u b]
  change 0 + g.inner p (show TangentSpace I p from b)
        (show TangentSpace I p from
          (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 2 (0, 1) : E)) +
      2 * g.inner p
        (show TangentSpace I p from
          (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 1 (0, 1) : E))
        (show TangentSpace I p from
          (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 1 (0, 1) : E)) +
      g.inner p
        (show TangentSpace I p from
          (intrinsicLaunchJet (I := I) g hEnorm p 0 u b 2 (0, 1) : E))
        (show TangentSpace I p from b) =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (LeviCivita (I := I) g) p
          (show TangentSpace I p from b)
          (show TangentSpace I p from u)
          (show TangentSpace I p from u))
        (show TangentSpace I p from b)
  rw [hone, htwo]
  let R : TangentSpace I p :=
    riemannOp (LeviCivita (I := I) g) p
      (show TangentSpace I p from b)
      (show TangentSpace I p from u)
      (show TangentSpace I p from u)
  change 0 + g.inner p (show TangentSpace I p from b) (-(1 / 3 : ℝ) • R) +
      2 * g.inner p (0 : TangentSpace I p) 0 +
      g.inner p (-(1 / 3 : ℝ) • R)
        (show TangentSpace I p from b) =
    -(2 / 3 : ℝ) * g.inner p R (show TangentSpace I p from b)
  have hinnerZero : g.inner p (0 : TangentSpace I p) 0 = 0 := by
    rw [map_zero]
  rw [hinnerZero]
  simp only [map_smul, smul_eq_mul, zero_add, mul_zero, add_zero]
  rw [g.symm p b]
  have hsmul : ((-(1 / 3 : ℝ) • (g.inner p) R)
      (show TangentSpace I p from b)) =
      -(1 / 3 : ℝ) * g.inner p R (show TangentSpace I p from b) := rfl
  rw [hsmul]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_radial_second_diag_of_launch_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E) (i : Fin (Module.finrank ℝ E))
    (hone : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0)
    (htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (LeviCivita (I := I) g) p
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) : E)) :
    iteratedDeriv 2 (fun t : ℝ ↦
      intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) 0 =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (LeviCivita (I := I) g) p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
          (normalFrame (I := I) g p u)
          (normalFrame (I := I) g p u))
        (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i)) := by
  let e : E := (stdOrthonormalBasis ℝ E) i
  let a : E := tangentSpaceModelContinuousLinearEquiv (I := I) p
    (normalFrame (I := I) g p u)
  let b : E := tangentSpaceModelContinuousLinearEquiv (I := I) p
    (normalFrame (I := I) g p e)
  let F : E → ℝ := fun z ↦ intrinsicFrameMetric (I := I) g hEnorm p z e e
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hF : ContDiff ℝ ∞ F :=
    (hmetric.clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ e))).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ e))
  have hambient :
      iteratedFDeriv ℝ 2 F 0 (fun _ ↦ u) =
        iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          (fun _ ↦ u) e e := by
    dsimp only [F]
    rw [iteratedFDeriv_clm_apply_const_apply
        (hmetric.clm_apply
          (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ e))) (by norm_cast),
      iteratedFDeriv_clm_apply_const_apply hmetric (by norm_cast)]
  have hmetricJet := intrinsicFrameMetric_diag_jet
    (I := I) g hEnorm p 0 u e 2
  simp only [map_zero] at hmetricJet
  change iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
      (fun _ ↦ u) e e =
    intrinsicMetricJet (I := I) g hEnorm p 0 a b 2 0 at hmetricJet
  have hexpand := intrinsicMetricJet_two_zero_of_launch_jets
    (I := I) g hEnorm p a b (hone a b) (htwo a b)
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ u
  have hcomp := L.iteratedFDeriv_comp_right hF 0 (i := 2) (by norm_cast)
  have happ := congrArg (fun A ↦ A (fun _ ↦ (1 : ℝ))) hcomp
  have hFL : F ∘ L = (fun t : ℝ ↦
      intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) := by
    funext t
    simp only [Function.comp_apply, F, L,
      ContinuousLinearMap.toSpanSingleton_apply, intrinsicFrameGram, e]
  rw [hFL] at happ
  have hrhs :
      ((iteratedFDeriv ℝ 2 F (L 0)).compContinuousLinearMap
          (fun _ ↦ L)) (fun _ ↦ (1 : ℝ)) =
        iteratedFDeriv ℝ 2 F 0 (fun _ ↦ u) := by
    simp only [L, map_zero,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [iteratedDeriv_eq_iteratedFDeriv]
  calc
    iteratedFDeriv ℝ 2
        (fun t : ℝ ↦ intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) 0
        (fun _ ↦ (1 : ℝ)) = iteratedFDeriv ℝ 2 F 0 (fun _ ↦ u) :=
      happ.trans hrhs
    _ = iteratedFDeriv ℝ 2
        (intrinsicFrameMetric (I := I) g hEnorm p) 0 (fun _ ↦ u) e e := hambient
    _ = intrinsicMetricJet (I := I) g hEnorm p 0 a b 2 0 := hmetricJet
    _ = -(2 / 3 : ℝ) * g.inner p
        (riemannOp (LeviCivita (I := I) g) p
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a))
        (show TangentSpace I p from b) := hexpand
    _ = -(2 / 3 : ℝ) * g.inner p
        (riemannOp (LeviCivita (I := I) g) p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
          (normalFrame (I := I) g p u)
          (normalFrame (I := I) g p u))
        (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i)) := by
      rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem normalFrame_curvature_trace_eq_ricci
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner p
          (riemannOp (LeviCivita (I := I) g) p
            (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
            (normalFrame (I := I) g p u)
            (normalFrame (I := I) g p u))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i)) =
      ricciTensor (I := I) g p
        (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) := by
  symm
  apply ricciTensor_eq_orthonormal_trace (I := I) g p
    (normalFrame (I := I) g p u) (normalFrame (I := I) g p u)
    (fun i ↦ normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
  intro i j
  rw [normalFrame_inner]
  exact (stdOrthonormalBasis ℝ E).inner_eq_ite i j

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_radial_second_trace_of_launch_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E)
    (hone : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0)
    (htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (LeviCivita (I := I) g) p
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) : E)) :
    ∑ i : Fin (Module.finrank ℝ E),
        iteratedDeriv 2 (fun t : ℝ ↦
          intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) 0 =
      -(2 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) := by
  rw [← normalFrame_curvature_trace_eq_ricci (I := I) g p u,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact intrinsicFrameGram_radial_second_diag_of_launch_jets
    (I := I) g hEnorm p u i hone htwo

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_radial_second_trace_of_launch_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E)
    (hone : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0)
    (htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (LeviCivita (I := I) g) p
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) : E)) :
    ∑ i : Fin (Module.finrank ℝ E),
        iteratedDeriv 2
          (fun t : ℝ ↦ intrinsicFrameMetric (I := I) g hEnorm p (t • u)
            ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) 0 =
      -(2 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) := by
  simpa only [intrinsicFrameGram] using
    intrinsicFrameGram_radial_second_trace_of_launch_jets
      (I := I) g hEnorm p u hone htwo

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_jets_of_launch_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E)
    (hone : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0)
    (htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (LeviCivita (I := I) g) p
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) : E)) :
    iteratedDeriv 1
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 = 0 ∧
      iteratedDeriv 2
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 =
        -(1 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p u)
          (normalFrame (I := I) g p u) := by
  classical
  let G : ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun t ↦
    intrinsicFrameGram (I := I) g hEnorm p (t • u)
  let B : ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun t i j ↦
    deriv (fun s ↦ G s i j) t
  let C : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun i j ↦
    iteratedDeriv 2 (fun t ↦ G t i j) 0
  have hG : ∀ i j, ContDiff ℝ ∞ (fun t ↦ G t i j) := by
    intro i j
    have hmetric := intrinsicFrameMetric_apply_contDiff (I := I) g hEnorm p
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)
    have hcomp := hmetric.comp
      (contDiff_id.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ u)))
    convert hcomp using 1; rfl
  have hGB : ∀ t i j, HasDerivAt (fun s ↦ G s i j) (B t i j) t := by
    intro t i j
    exact ((hG i j).differentiable (by simp) t).hasDerivAt
  have hBC : ∀ i j, HasDerivAt (fun t ↦ B t i j) (C i j) 0 := by
    intro i j
    have hd : Differentiable ℝ (iteratedDeriv 1 (fun t ↦ G t i j)) :=
      (hG i j).differentiable_iteratedDeriv 1 (by simp)
    rw [iteratedDeriv_one] at hd
    have h := (hd 0).hasDerivAt
    change HasDerivAt (deriv (fun t ↦ G t i j))
      (iteratedDeriv 2 (fun t ↦ G t i j) 0) 0
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
    exact h
  have hG0 : G 0 = 1 := by
    simpa only [G, zero_smul] using intrinsicFrameGram_zero (I := I) g hEnorm p
  have hB0 : B 0 = 0 := by
    ext i j
    change deriv (fun s ↦ G s i j) 0 = 0
    rw [← iteratedDeriv_one]
    simpa only [G] using
      intrinsicFrameGram_radial_first_jet_zero (I := I) g hEnorm p u i j
  have hmatrix := matrixCurve_det_sqrt_jets_at_identity
    G B C hG hGB hBC hG0 hB0
  have htrace : Matrix.trace C =
      -(2 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) := by
    change (∑ i, C i i) = _
    simpa only [C, G] using
      intrinsicFrameGram_radial_second_trace_of_launch_jets
        (I := I) g hEnorm p u hone htwo
  have hJfun :
      (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) =
        fun t ↦ Real.sqrt (G t).det := by
    funext t
    exact normalExpJacobian_eq_sqrt_det_intrFrameGram
      (I := I) g hEnorm p (t • u)
  constructor
  · rw [hJfun]
    exact hmatrix.2.2.1
  · rw [hJfun, hmatrix.2.2.2, htrace]
    ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_jets_of_intrLaunchJet_two_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u : E)
    (htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (LeviCivita (I := I) g) p
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) : E)) :
    iteratedDeriv 1
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 = 0 ∧
      iteratedDeriv 2
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 =
        -(1 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p u)
          (normalFrame (I := I) g p u) := by
  apply normalExpJacobian_radial_jets_of_launch_jets
    (I := I) g hEnorm p u (fun a b ↦ ?_) htwo
  exact congrArg (fun v ↦ (v : E))
    (intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
