import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SameManifoldWindowCompactness
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.LocalStabilityInputWitness
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem ricciTensor_eq_zero_of_tendsto_ricciTensor
    {hSeq : Nat -> SmoothRiemannianMetric I M} {hInf : SmoothRiemannianMetric I M}
    (hric : forall (k : Nat) (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (hSeq k) x v w = 0)
    (hconv : forall (x : M) (v w : TangentSpace I x),
      Tendsto (fun k : Nat => ricciTensor (I := I) (hSeq k) x v w) atTop
        (nhds (ricciTensor (I := I) hInf x v w))) :
    forall (x : M) (v w : TangentSpace I x), ricciTensor (I := I) hInf x v w = 0 := by
  intro x v w
  have hzero : Tendsto (fun k : Nat => ricciTensor (I := I) (hSeq k) x v w) atTop
      (nhds (0 : Real)) := by
    have hconst : (fun k : Nat => ricciTensor (I := I) (hSeq k) x v w) =
        fun _ : Nat => (0 : Real) := by
      funext k
      exact hric k x v w
    rw [hconst]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hconv x v w) hzero

omit [SigmaCompactSpace M] in
theorem nonempty_sameManifoldLimitEquationData_of_tendsto_ricciTensor
    {hSeq : Nat -> SmoothRiemannianMetric I M} {hInf : SmoothRiemannianMetric I M}
    (hric : forall (k : Nat) (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (hSeq k) x v w = 0)
    (hconv : forall (x : M) (v w : TangentSpace I x),
      Tendsto (fun k : Nat => ricciTensor (I := I) (hSeq k) x v w) atTop
        (nhds (ricciTensor (I := I) hInf x v w)))
    (D : RealTimeInterval) :
    Nonempty (SameManifoldLimitEquationData (I := I) (fun _ : Real => hInf) D) :=
  ⟨SameManifoldLimitEquationData.ofSolution (I := I) D
    (PDE.RicciFlow.SolutionOn.const hInf D)
    (PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero hInf
      (ricciTensor_eq_zero_of_tendsto_ricciTensor hric hconv) D)⟩

omit [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem hasDerivWithinAt_ricciTensor_limit_of_locally_uniform_deriv
    (D : RealTimeInterval)
    (g : Nat -> Real -> SmoothRiemannianMetric I M) (gInf : Real -> SmoothRiemannianMetric I M)
    {x : M} (X Y : TangentSpace I x) {t0 : Real} (ht0 : t0 ∈ D.regular)
    {dInf : Real}
    (hfun : forall s : Real, s ∈ D.regular -> Tendsto (fun k : Nat => (g k s).inner x X Y)
      atTop (nhds ((gInf s).inner x X Y)))
    (hdiff : forall k : Nat, DifferentiableOn Real
      (fun s : Real => (g k s).inner x X Y) D.regular)
    (hderiv : TendstoLocallyUniformlyOn
      (fun k : Nat => deriv (fun s : Real => (g k s).inner x X Y)) (fun _ : Real => dInf)
      atTop D.regular)
    (hric : Tendsto (fun k : Nat => ricciTensor (I := I) (g k t0) x X Y) atTop
      (nhds (ricciTensor (I := I) (gInf t0) x X Y)))
    (heq : forall k : Nat, HasDerivWithinAt (fun s : Real => (g k s).inner x X Y)
      ((-2 : Real) * ricciTensor (I := I) (g k t0) x X Y) D.carrier t0) :
    HasDerivWithinAt (fun s : Real => (gInf s).inner x X Y)
      ((-2 : Real) * ricciTensor (I := I) (gInf t0) x X Y) D.carrier t0 := by
  have hlim : HasDerivAt (fun s : Real => (gInf s).inner x X Y) dInf t0 :=
    hasDerivAt_of_tendsto_locally_uniformly_on' D.regular_isOpen hderiv
      (Eventually.of_forall hdiff) hfun ht0
  have hpt : Tendsto (fun k : Nat => deriv (fun s : Real => (g k s).inner x X Y) t0) atTop
      (nhds dInf) := hderiv.tendsto_at ht0
  have hpt' : Tendsto (fun k : Nat => (-2 : Real) * ricciTensor (I := I) (g k t0) x X Y)
      atTop (nhds ((-2 : Real) * ricciTensor (I := I) (gInf t0) x X Y)) :=
    hric.const_mul (-2)
  have hderiv_eq : (fun k : Nat => deriv (fun s : Real => (g k s).inner x X Y) t0) =
      fun k : Nat => (-2 : Real) * ricciTensor (I := I) (g k t0) x X Y := by
    funext k
    exact ((heq k).hasDerivAt (D.regular_mem_nhds ht0)).deriv
  have hdInf : dInf = (-2 : Real) * ricciTensor (I := I) (gInf t0) x X Y :=
    tendsto_nhds_unique (hderiv_eq ▸ hpt) hpt'
  rw [hdInf] at hlim
  exact hlim.hasDerivWithinAt

theorem nonempty_sameManifoldLimitEquationData_of_stationary_jet_convergence
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    (gRef : SmoothRiemannianMetric I M)
    (hSeq : Nat -> SmoothRiemannianMetric I M) (hInf : SmoothRiemannianMetric I M)
    (lam B : Real) (hlam : 0 < lam) (hB : 0 <= B)
    (hlowSeq : forall (k : Nat) (x : M) (ξ : TangentSpace I x),
      lam * gRef.inner x ξ ξ <= (hSeq k).inner x ξ ξ)
    (hlowInf : forall (x : M) (ξ : TangentSpace I x),
      lam * gRef.inner x ξ ξ <= hInf.inner x ξ ξ)
    (hbddSeq : forall (k : Nat) (x : M) (a : Nat), a <= 2 ->
      metricCovDerivNorm (I := I) a (hSeq k) gRef x <= B)
    (hbddInf : forall (x : M) (a : Nat), a <= 2 ->
      metricCovDerivNorm (I := I) a hInf gRef x <= B)
    (hconv : forall (x : M) (ε : Real), 0 < ε -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= 2 ->
        metricDerivNorm (I := I) a (hSeq k) hInf gRef x < ε)
    (hricFlat : forall (k : Nat) (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (hSeq k) x v w = 0)
    (D : RealTimeInterval) :
    Nonempty (SameManifoldLimitEquationData (I := I) (fun _ : Real => hInf) D) :=
  nonempty_sameManifoldLimitEquationData_of_tendsto_ricciTensor hricFlat
    (fun x v w => tendsto_ricciTensor_of_jetConvergence (I := I) gRef x hSeq hInf lam B
      hlam hB (fun k => hlowSeq k x) (hlowInf x) (fun k a ha => hbddSeq k x a ha)
      (hbddInf x) (hconv x) v w) D

omit [CompleteSpace E] [SigmaCompactSpace M] [IsManifold I 1 M] in
theorem hasDerivWithinAt_ricciTensor_limit_of_stationary_sequence
    (D : RealTimeInterval) {t0 : Real} (ht0 : t0 ∈ D.regular)
    (hSeq : Nat -> SmoothRiemannianMetric I M) (hInf : SmoothRiemannianMetric I M)
    {x : M} (X Y : TangentSpace I x)
    (hfun : Tendsto (fun k : Nat => (hSeq k).inner x X Y) atTop (nhds (hInf.inner x X Y)))
    (hricFlat : forall (k : Nat) (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (hSeq k) x v w = 0)
    (hric : Tendsto (fun k : Nat => ricciTensor (I := I) (hSeq k) x X Y) atTop
      (nhds (ricciTensor (I := I) hInf x X Y))) :
    HasDerivWithinAt (fun _ : Real => hInf.inner x X Y)
      ((-2 : Real) * ricciTensor (I := I) hInf x X Y) D.carrier t0 := by
  have hderiv : TendstoLocallyUniformlyOn (fun (_ : Nat) (_ : Real) => (0 : Real))
      (fun (_ : Real) => (0 : Real)) atTop D.regular :=
    have hconst : Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds (0 : Real)) :=
      tendsto_const_nhds
    (hconst.tendstoUniformlyOn_const D.regular).tendstoLocallyUniformlyOn
  refine hasDerivWithinAt_ricciTensor_limit_of_locally_uniform_deriv (I := I) D
    (fun (_ : Nat) (_ : Real) => hSeq _) (fun (_ : Real) => hInf) X Y ht0 (dInf := 0)
    (fun _ _ => hfun) (fun k => differentiableOn_const _) ?_ hric ?_
  · have hzero : (fun k : Nat => deriv (fun _ : Real => (hSeq k).inner x X Y)) =
        fun (_ : Nat) (_ : Real) => (0 : Real) := by
      funext k s
      exact (hasDerivAt_const s ((hSeq k).inner x X Y)).deriv
    rw [hzero]
    exact hderiv
  · intro k
    rw [hricFlat k x X Y, mul_zero]
    exact (hasDerivAt_const t0 ((hSeq k).inner x X Y)).hasDerivWithinAt

end General

section Line

noncomputable def scaleLineMetric (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) (t : Real) :
    SmoothRiemannianMetric 𝓘(Real, Real) Real :=
  DifferentialGeometry.scaleMetric (1 + t ^ 2) (by nlinarith [sq_nonneg t]) h

@[simp] theorem scaleLineMetric_inner
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) (t : Real)
    (x : Real) (v w : TangentSpace 𝓘(Real, Real) x) :
    (scaleLineMetric h t).inner x v w = (1 + t ^ 2) * h.inner x v w := by
  rw [scaleLineMetric, DifferentialGeometry.scaleMetric_inner]

theorem ricciTensor_scaleLineMetric_eq_zero
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) (t : Real)
    (x : Real) (v w : TangentSpace 𝓘(Real, Real) x) :
    ricciTensor (I := 𝓘(Real, Real)) (scaleLineMetric h t) x v w = 0 := by
  rw [scaleLineMetric, DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric]
  exact ricciTensor_line_eq_zero h x v w

theorem metricRicciAt_scaleLineMetric_eq_zero
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) (t : Real)
    (x : Real) (v w : TangentSpace 𝓘(Real, Real) x) :
    (DifferentialGeometry.Geometry.Curvature.metricRicciAt (scaleLineMetric h t) x)
      (vec2 v w) = 0 := by
  rw [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor]
  exact ricciTensor_scaleLineMetric_eq_zero h t x v w

theorem hasDerivAt_scaleLineMetric_inner
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
    (x : Real) (X Y : TangentSpace 𝓘(Real, Real) x) (t0 : Real) :
    HasDerivAt (fun s : Real => (scaleLineMetric h s).inner x X Y)
      (2 * t0 * h.inner x X Y) t0 := by
  have hsq : HasDerivAt (fun s : Real => s ^ 2) (2 * t0) t0 := by
    simpa using hasDerivAt_pow 2 t0
  have hfun : (fun s : Real => (scaleLineMetric h s).inner x X Y) =
      fun s : Real => (1 + s ^ 2) * h.inner x X Y := by
    funext s
    rw [scaleLineMetric_inner]
  rw [hfun]
  simpa using (hsq.const_add 1).mul_const (h.inner x X Y)

theorem scaleLineMetric_not_solution (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) :
    ¬ Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
      (fun t : Real => scaleLineMetric h t) (arcInterval 1)) := by
  rintro ⟨H⟩
  let x : Real := 0
  let X : TangentSpace 𝓘(Real, Real) x := 1
  have hT : (0 : Real) < 1 := by norm_num
  have ht0 : (-1 / 2 : Real) ∈ (arcInterval 1).regular := by
    rw [arcInterval_regular hT]
    exact ⟨by norm_num, by norm_num⟩
  have hcarrier : (arcInterval 1).carrier ∈ nhds (-1 / 2 : Real) :=
    (arcInterval 1).regular_mem_nhds ht0
  have ht0c : (-1 / 2 : Real) ∈ (arcInterval 1).carrier :=
    (arcInterval 1).regular_subset ht0
  have hX : X ≠ 0 := by
    change (1 : Real) ≠ 0
    exact one_ne_zero
  have hK : 0 < h.inner x X X := h.pos x X hX
  have hagree : H.solution.family.metric (-1 / 2) = scaleLineMetric h (-1 / 2) :=
    H.agrees (-1 / 2) ht0c
  have hric0 : H.solution.ricciAt (-1 / 2) x (vec2 X X) = 0 := by
    change (DifferentialGeometry.Geometry.Curvature.metricRicciAt
      (H.solution.family.metric (-1 / 2)) x) (vec2 X X) = 0
    rw [hagree]
    exact metricRicciAt_scaleLineMetric_eq_zero h (-1 / 2) x X X
  have heq := H.isSolution.equation ⟨-1 / 2, ht0⟩ x X X
  rw [PDE.RicciFlow.RicciAtFamily.toTensorField_apply, hric0, mul_zero] at heq
  have hcongr := heq.congr
    (fun y hy => by rw [H.agrees y hy])
    (by rw [hagree])
  have hderiv0 : HasDerivAt
      (fun s : Real => (scaleLineMetric h s).inner x X X) 0 (-1 / 2) :=
    hcongr.hasDerivAt hcarrier
  have hderiv1 := hasDerivAt_scaleLineMetric_inner h x X X (-1 / 2)
  have hzero : (2 : Real) * (-1 / 2) * h.inner x X X = 0 := by
    rw [<- hderiv0.deriv, hderiv1.deriv]
  linarith

noncomputable def ancientMetricSubsequence_const
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) :
    AncientMetricSubsequence (I := 𝓘(Real, Real)) (fun (_ : Nat) (_ : Real) => h) h where
  subseq := id
  strictMono := strictMono_id
  limit := fun _ : Real => h
  converges := by
    intro n K _ p ε hε
    exact ⟨0, fun k _ t _ => by rw [metricDerivNormSupOn_self]; exact hε⟩

noncomputable def ancientMetricSubsequence_scaleLineMetric
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) :
    AncientMetricSubsequence (I := 𝓘(Real, Real))
      (fun (_ : Nat) (t : Real) => scaleLineMetric h t) h where
  subseq := id
  strictMono := strictMono_id
  limit := fun t : Real => scaleLineMetric h t
  converges := by
    intro n K _ p ε hε
    exact ⟨0, fun k _ t _ => by rw [metricDerivNormSupOn_self]; exact hε⟩

theorem nonempty_sameManifoldLimitEquationData_line
    (h : SmoothRiemannianMetric 𝓘(Real, Real) Real) :
    Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
      (fun _ : Real => h) (arcInterval 1)) :=
  ⟨SameManifoldLimitEquationData.ofSolution (I := 𝓘(Real, Real)) (arcInterval 1)
    (PDE.RicciFlow.SolutionOn.const h (arcInterval 1))
    (PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero h
      (fun x v w => ricciTensor_line_eq_zero h x v w) (arcInterval 1))⟩

theorem scaleLineMetric_zero_inner (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
    (x : Real) (v w : TangentSpace 𝓘(Real, Real) x) :
    (scaleLineMetric h 0).inner x v w = h.inner x v w := by
  rw [scaleLineMetric_inner]
  ring

theorem exists_ancientMetricSubsequence_limit_equation_holds_and_fails :
    (exists (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
      (H : AncientMetricSubsequence (I := 𝓘(Real, Real))
        (fun (_ : Nat) (_ : Real) => h) h),
      Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
        H.limit (arcInterval 1))) ∧
    (exists (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
      (H : AncientMetricSubsequence (I := 𝓘(Real, Real))
        (fun (_ : Nat) (t : Real) => scaleLineMetric h t) h),
      ¬ Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
        H.limit (arcInterval 1))) := by
  constructor
  · refine ⟨euclideanMetric (E := Real),
      ancientMetricSubsequence_const (euclideanMetric (E := Real)), ?_⟩
    change Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
      (fun _ : Real => euclideanMetric (E := Real)) (arcInterval 1))
    exact nonempty_sameManifoldLimitEquationData_line (euclideanMetric (E := Real))
  · refine ⟨euclideanMetric (E := Real),
      ancientMetricSubsequence_scaleLineMetric (euclideanMetric (E := Real)), ?_⟩
    change ¬ Nonempty (SameManifoldLimitEquationData (I := 𝓘(Real, Real)) (M := Real)
      (fun t : Real => scaleLineMetric (euclideanMetric (E := Real)) t) (arcInterval 1))
    exact scaleLineMetric_not_solution (euclideanMetric (E := Real))

end Line

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
