import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.DifferentiatedContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureRicciContraction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Operator.WeightedLaplacianRicci
import DifferentialGeometry.Geometry.Operator.WeightedLaplacianTensorNorm
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Norm.Product
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private def rmGradSlots : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

omit [SigmaCompactSpace M] in
theorem gradientRicciSoliton_nablaHess_eq_neg_nablaRic
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    nablaHessSec (I := I) cov hcov f f.contMDiff = -nablaRic := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Hess := hessianSec (I := I) cov hcov f f.contMDiff
  let Ric := metricRicci (I := I) (M := M) g
  let nablaHess := nablaHessSec (I := I) cov hcov f f.contMDiff
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  have hmc : IsMetricCompatible (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hfield : Hess + Ric = (σ / 2) • metricTensorField (I := I) g := by
    apply ContMDiffSection.ext
    intro x
    ext slots
    have hslots : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]
    change Hess x (vec2 (I := I) (slots 0) (slots 1)) +
        Ric x (vec2 (I := I) (slots 0) (slots 1)) =
      (σ / 2) * metricTensorField (I := I) g x
        (vec2 (I := I) (slots 0) (slots 1))
    rw [metricTensorField_apply]
    change Hess x (vec2 (I := I) (slots 0) (slots 1)) +
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (slots 0) (slots 1)) =
      (σ / 2) * g.inner x (slots 0) (slots 1)
    rw [metricRicciAt_apply_eq_ricciTensor]
    rw [hessSec_inner_cov (I := I) cov hcov g hmc f f.contMDiff x]
    rw [show cov = LeviCivita (I := I) g by rfl]
    rw [show (fun y : M => gradientFun (I := I) g f y) =
        fun y : M => gradFun (I := I) g f y by
      funext y
      exact gradient_eq_gradFun (I := I) g f y]
    rw [← hessFun_eq_cov_local (I := I) g isOpen_univ
      f.contMDiff.contMDiffOn (mem_univ x)]
    simpa [add_comm] using h x (slots 0) (slots 1)
  have hHessReal : TotalNabla0SRealizes (I := I) 2 cov Hess nablaHess := by
    simpa [Hess, nablaHess, nablaHessSec] using
      (totalNabla0S_realizes (I := I) 2 cov Hess
        (totalNabla0S_regularity (I := I) 2 cov hcov Hess))
  have hRicReal : TotalNabla0SRealizes (I := I) 2 cov Ric nablaRic := by
    exact totalNabla0S_realizes (I := I) 2 cov Ric _
  have hMetricReal : TotalNabla0SRealizes (I := I) 2 cov
      (metricTensorField (I := I) g) 0 :=
    zero_realizes_metric (I := I) cov g hmc
  have hleft := hHessReal.add hRicReal
  have hright := hMetricReal.smul (σ / 2)
  rw [hfield] at hleft
  have heq := totalNabla0SRealizes_unique (I := I) hleft hright
  have hzero : nablaHess + nablaRic = 0 := by
    simpa only [smul_zero] using heq
  dsimp only
  change nablaHess = -nablaRic
  exact eq_neg_of_add_eq_zero_left hzero

omit [SigmaCompactSpace M] in
theorem gradientRicciSoliton_nablaRic_comm
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    (X Y Z : TangentSpace I x) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Rm13 := CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    nablaRic x (vec3 (I := I) X Y Z) -
        nablaRic x (vec3 (I := I) Y X Z) =
      Rm13 x (duSec (I := I) f f.contMDiff x) (vec3 (I := I) X Y Z) := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Rm13 := CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let nablaHess := nablaHessSec (I := I) cov hcov f f.contMDiff
  have hRm13 : rm13RealizesConnection (I := I) cov Rm13 :=
    rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov)
  have hNabla2 := nablaHess_realizes (I := I) cov hcov f f.contMDiff x
  have hcomm := oneFormThirdCovDerivCommAt_of_leviCivita
    (I := I) g Rm13 (duSec (I := I) f f.contMDiff)
      (hessianSec (I := I) cov hcov f f.contMDiff)
      (duSec (I := I) f f.contMDiff x) (nablaHess x)
      (by simpa [cov, LeviCivita] using hRm13) rfl hNabla2 X Y Z
  have hderiv := gradientRicciSoliton_nablaHess_eq_neg_nablaRic
    (I := I) (M := M) h
  have hpoint : nablaHess x = -nablaRic x := by
    simpa [cov, hcov, Ric, nablaRic, nablaHess] using
      congrArg (fun T => T x) hderiv
  rw [hpoint] at hcomm
  change nablaRic x (vec3 (I := I) X Y Z) -
      nablaRic x (vec3 (I := I) Y X Z) =
    Rm13 x (duSec (I := I) f f.contMDiff x) (vec3 (I := I) X Y Z)
  simp only [Tensor0SSpace.neg_apply] at hcomm
  linear_combination -hcomm

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_nablaRic_codazzi_field
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let swapped := Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1) nablaRic
    let Rm04 := metricRm04 (I := I) (M := M) g
    let rotatedRm := Tensor0SField.domDomCongr ∞ rmGradSlots Rm04
    let gradSection := gradG (I := I) g f
    nablaRic + (-1 : Real) • swapped =
      partialEval0SField (I := I) rotatedRm gradSection := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let swapped := Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1) nablaRic
  let Rm13 := CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 := metricRm04 (I := I) (M := M) g
  let rotatedRm := Tensor0SField.domDomCongr ∞ rmGradSlots Rm04
  let gradSection := gradG (I := I) g f
  apply ContMDiffSection.ext
  intro x
  ext slots
  have hslots : slots = vec3 (I := I) (slots 0) (slots 1) (slots 2) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]
  change (nablaRic x + (-1 : Real) • swapped x)
      (vec3 (I := I) (slots 0) (slots 1) (slots 2)) =
    partialEval0SField (I := I) rotatedRm gradSection x
      (vec3 (I := I) (slots 0) (slots 1) (slots 2))
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    partialEval0SField_apply, tensor0S_curry_apply_cons]
  dsimp only [swapped, rotatedRm]
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  simp only [smul_eq_mul, neg_mul, one_mul]
  have hswap :
      (fun q : Fin 3 => vec3 (I := I) (slots 0) (slots 1) (slots 2)
        ((Equiv.swap (0 : Fin 3) 1) q)) =
        vec3 (I := I) (slots 1) (slots 0) (slots 2) := by
    funext q
    fin_cases q <;> rfl
  rw [hswap]
  have hrotate :
      (fun q : Fin 4 =>
        (Fin.cons (gradSection x)
          (vec3 (I := I) (slots 0) (slots 1) (slots 2)) :
            Fin 4 → TangentSpace I x) (rmGradSlots q)) =
        vec4 (I := I) (slots 0) (slots 1) (slots 2) (gradSection x) := by
    funext q
    fin_cases q <;> rfl
  rw [hrotate]
  change nablaRic x (vec3 (I := I) (slots 0) (slots 1) (slots 2)) -
      nablaRic x (vec3 (I := I) (slots 1) (slots 0) (slots 2)) =
    Rm04 x (vec4 (I := I) (slots 0) (slots 1) (slots 2) (gradSection x))
  have hcomm := gradientRicciSoliton_nablaRic_comm
    (I := I) (M := M) h x (slots 0) (slots 1) (slots 2)
  have hRm13 : rm13RealizesConnection (I := I) cov Rm13 :=
    rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov)
  have hRm04 : rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04, metricRm04, cov, LeviCivita, metricCov] using
      (rm04Section_realizes (I := I) (M := M) g cov hcov)
  have hLower := rm04LowersRm13At_of_realizes
    (I := I) g cov Rm13 Rm04 hRm13 hRm04 x
  have hdu : duSec (I := I) f f.contMDiff x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradSection x)) := by
    change differential1FormFun (I := I) f x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradFun (I := I) g f x))
    exact differential1FormFun_eq_metric_dual_gradientFun (I := I) g f x
  rw [hdu] at hcomm
  have hlower := hLower (slots 0) (slots 1) (slots 2) (gradSection x)
  simpa [cov, hcov, Ric, nablaRic, Rm13, Rm04] using hcomm.trans hlower.symm

omit [SigmaCompactSpace M] in
omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_nabla2Ric_comm
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    (D X Y Z : TangentSpace I x) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let nabla2Ric := totalNabla0S (I := I) 3 cov nablaRic
      (totalNabla0S_regularity (I := I) 3 cov hcov nablaRic)
    let Rm04 := metricRm04 (I := I) (M := M) g
    let nablaRm04 := totalNabla0S (I := I) 4 cov Rm04
      (totalNabla0S_regularity (I := I) 4 cov hcov Rm04)
    let gradSection := gradG (I := I) g f
    nabla2Ric x (vec4 (I := I) D X Y Z) -
        nabla2Ric x (vec4 (I := I) D Y X Z) =
      nablaRm04 x (vec5 (I := I) D X Y Z (gradSection x)) +
        Rm04 x (vec4 (I := I) X Y Z (cov gradSection x D)) := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let nabla2Ric := totalNabla0S (I := I) 3 cov nablaRic
    (totalNabla0S_regularity (I := I) 3 cov hcov nablaRic)
  let swapped := Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1) nablaRic
  let Rm04 := metricRm04 (I := I) (M := M) g
  let nablaRm04 := totalNabla0S (I := I) 4 cov Rm04
    (totalNabla0S_regularity (I := I) 4 cov hcov Rm04)
  let rotatedRm := Tensor0SField.domDomCongr ∞ rmGradSlots Rm04
  let nablaRotatedRm := Tensor0SField.domDomCongr ∞
    (frontExtendEquiv rmGradSlots) nablaRm04
  let gradSection := gradG (I := I) g f
  obtain ⟨Dsec, hDsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x D
  have hNablaRic : TotalNabla0SRealizes (I := I) 3 cov nablaRic nabla2Ric :=
    totalNabla0S_realizes (I := I) 3 cov nablaRic _
  have hNablaRm : TotalNabla0SRealizes (I := I) 4 cov Rm04 nablaRm04 :=
    totalNabla0S_realizes (I := I) 4 cov Rm04 _
  have hNablaRotated : TotalNabla0SRealizes (I := I) 4 cov
      rotatedRm nablaRotatedRm := by
    simpa [rotatedRm, nablaRotatedRm] using
      (totalNabla0SRealizes_domDomCongr (I := I) cov rmGradSlots
        Rm04 nablaRm04 hNablaRm)
  have hfield := gradientRicciSoliton_nablaRic_codazzi_field
    (I := I) (M := M) h
  have hder := congrArg
    (fun A => nabla0SFun (I := I) 3 cov Dsec A x) hfield
  rw [nabla0SFun_add (I := I), nabla0SFun_smul (I := I)] at hder
  have hderEval := congrArg
    (fun A => A (vec3 (I := I) X Y Z)) hder
  have hleft :
      nabla0SFun (I := I) 3 cov Dsec nablaRic x (vec3 (I := I) X Y Z) =
        nabla2Ric x (vec4 (I := I) D X Y Z) := by
    have hreal := hNablaRic Dsec x (vec3 (I := I) X Y Z)
    rw [hDsec] at hreal
    have hcons :
        Fin.cons D (vec3 (I := I) X Y Z) =
          vec4 (I := I) D X Y Z := by
      funext q
      fin_cases q <;> rfl
    rw [hcons] at hreal
    exact hreal.symm
  have hswap :
      nabla0SFun (I := I) 3 cov Dsec swapped x (vec3 (I := I) X Y Z) =
        nabla2Ric x (vec4 (I := I) D Y X Z) := by
    have hperm := nabla0SFun_domDomCongr (I := I) cov Dsec
      (Equiv.swap (0 : Fin 3) 1) nablaRic x (vec3 (I := I) X Y Z)
    have hreal := hNablaRic Dsec x (vec3 (I := I) Y X Z)
    rw [hDsec] at hreal
    have hswapSlots :
        (vec3 (I := I) X Y Z) ∘ (Equiv.swap (0 : Fin 3) 1) =
          vec3 (I := I) Y X Z := by
      funext q
      fin_cases q <;> rfl
    have hcons :
        Fin.cons D (vec3 (I := I) Y X Z) =
          vec4 (I := I) D Y X Z := by
      funext q
      fin_cases q <;> rfl
    rw [hcons] at hreal
    rw [hperm, hswapSlots]
    exact hreal.symm
  have hrightTensor := nabla_partialEval0S (I := I) cov rotatedRm
    nablaRotatedRm hNablaRotated Dsec gradSection x
  have hright := congrArg
    (fun A => A (vec3 (I := I) X Y Z)) hrightTensor
  have hright' :
      nabla0SFun (I := I) 3 cov Dsec
          (partialEval0SField (I := I) rotatedRm gradSection) x
          (vec3 (I := I) X Y Z) =
        nablaRm04 x (vec5 (I := I) D X Y Z (gradSection x)) +
          Rm04 x (vec4 (I := I) X Y Z (cov gradSection x D)) := by
    rw [hDsec] at hright
    rw [Tensor0SSpace.add_apply, freezeFirstTwoArgs0S_apply,
      tensor0S_curry_apply_cons] at hright
    dsimp only [nablaRotatedRm, rotatedRm] at hright
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply] at hright
    have hfirstSlots :
        (fun q : Fin 5 =>
          metricTraceInput (I := I) D (gradSection x) (vec3 (I := I) X Y Z)
            (frontExtendEquiv rmGradSlots q)) =
          vec5 (I := I) D X Y Z (gradSection x) := by
      funext q
      fin_cases q <;> rfl
    have hsecondSlots :
        (fun q : Fin 4 =>
          (Fin.cons (cov gradSection x D) (vec3 (I := I) X Y Z) :
            Fin 4 -> TangentSpace I x) (rmGradSlots q)) =
          vec4 (I := I) X Y Z (cov gradSection x D) := by
      funext q
      fin_cases q <;> rfl
    rw [hfirstSlots, hsecondSlots] at hright
    exact hright
  change nabla2Ric x (vec4 (I := I) D X Y Z) -
      nabla2Ric x (vec4 (I := I) D Y X Z) =
    nablaRm04 x (vec5 (I := I) D X Y Z (gradSection x)) +
      Rm04 x (vec4 (I := I) X Y Z (cov gradSection x D))
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply] at hderEval
  rw [hleft, hswap, hright'] at hderEval
  simpa only [sub_eq_add_neg, smul_eq_mul, neg_one_mul] using hderEval

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_hessian_scalar
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    (X Y : TangentSpace I x) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let scalar : M -> Real := fun y => metricScalarAt (I := I) (M := M) g y
    let hscalar := metricScalar_smooth (I := I) (M := M) g
    let HessScalar := hessianSec (I := I) cov hcov scalar hscalar
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let gradSection := gradG (I := I) g f
    HessScalar x (vec2 (I := I) X Y) =
      2 * (nablaRic x (vec3 (I := I) X (gradSection x) Y) +
        Ric x (vec2 (I := I) (cov gradSection x X) Y)) := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let scalar : M -> Real := fun y => metricScalarAt (I := I) (M := M) g y
  let hscalar := metricScalar_smooth (I := I) (M := M) g
  let HessScalar := hessianSec (I := I) cov hcov scalar hscalar
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let gradSection := gradG (I := I) g f
  have hfield : duSec (I := I) scalar hscalar =
      (2 : Real) • partialEval0SField (I := I) Ric gradSection := by
    apply ContMDiffSection.ext
    intro y
    ext slots
    have hslots : slots = fun _ : Fin 1 => slots 0 := by
      funext q
      fin_cases q
      rfl
    rw [hslots]
    rw [duSec_apply, ContMDiffSection.coe_smul, Pi.smul_apply]
    change differential1FormFun (I := I) scalar y
        (fun _ : Fin 1 => slots 0) =
      (2 • partialEval0SField (I := I) Ric gradSection y)
        (fun _ : Fin 1 => slots 0)
    rw [Tensor0SSpace.smul_apply, partialEval0SField_apply,
      tensor0S_curry_one_apply]
    change differential1FormFun (I := I) scalar y
        (fun _ : Fin 1 => slots 0) =
      2 * metricRicciAt (I := I) (M := M) g y
        (vec2 (I := I) (gradSection y) (slots 0))
    rw [metricRicciAt_apply_eq_ricciTensor]
    simpa [scalar, gradSection] using
      gradientRicciSoliton_differential_scalar (I := I) h y (slots 0)
  obtain ⟨Xsec, hXsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hder := congrArg
    (fun A => nabla0SFun (I := I) 1 cov Xsec A x) hfield
  rw [nabla0SFun_smul (I := I)] at hder
  have hderEval := congrArg (fun A => A (fun _ : Fin 1 => Y)) hder
  have hleft :
      nabla0SFun (I := I) 1 cov Xsec (duSec (I := I) scalar hscalar) x
          (fun _ : Fin 1 => Y) =
        HessScalar x (vec2 (I := I) X Y) := by
    have hHess := hessianSec_realizesAt (I := I) cov hcov scalar hscalar x
    have hreal := hHess Xsec Y
    simpa [nablaDuAt, hXsec, HessScalar] using hreal.symm
  have hNablaRic : TotalNabla0SRealizes (I := I) 2 cov Ric nablaRic :=
    totalNabla0S_realizes (I := I) 2 cov Ric _
  have hrightTensor := nabla_partialEval0S (I := I) cov Ric nablaRic
    hNablaRic Xsec gradSection x
  have hright := congrArg (fun A => A (fun _ : Fin 1 => Y)) hrightTensor
  have hright' :
      nabla0SFun (I := I) 1 cov Xsec
          (partialEval0SField (I := I) Ric gradSection) x
          (fun _ : Fin 1 => Y) =
        nablaRic x (vec3 (I := I) X (gradSection x) Y) +
          Ric x (vec2 (I := I) (cov gradSection x X) Y) := by
    rw [hXsec] at hright
    rw [Tensor0SSpace.add_apply, freezeFirstTwoArgs0S_apply,
      tensor0S_curry_one_apply] at hright
    have hfirst :
        metricTraceInput (I := I) X (gradSection x) (fun _ : Fin 1 => Y) =
          vec3 (I := I) X (gradSection x) Y := by
      funext q
      fin_cases q <;> rfl
    rw [hfirst] at hright
    exact hright
  rw [Tensor0SSpace.smul_apply, hleft, hright'] at hderEval
  exact hderEval

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_trace_nablaRm
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (v w : TangentSpace I x) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Rm04 := metricRm04 (I := I) (M := M) g
    let nablaRm04 := totalNabla0S (I := I) 4 cov Rm04
      (totalNabla0S_regularity (I := I) 4 cov hcov Rm04)
    let gradSection := gradG (I := I) g f
    (∑ i : Idx, nablaRm04 x
        (vec5 (I := I) (basis i) (basis i) v w (gradSection x))) =
      -Rm04 x (vec4 (I := I) v (gradSection x) w (gradSection x)) := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Rm04 := metricRm04 (I := I) (M := M) g
  let nablaRm04 := totalNabla0S (I := I) 4 cov Rm04
    (totalNabla0S_regularity (I := I) 4 cov hcov Rm04)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let gradSection := gradG (I := I) g f
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hsymm := levi_civita_covariant_riemann_symmetries
    (I := I) (M := M) g (x := x)
  have hbianchi := levi_civita_second_bianchi
    (I := I) (M := M) g (x := x)
  have htrace := levi_civita_covariant_ricci_eq_riemann_trace
    (I := I) (M := M) g basis (identityInvMetric (Idx := Idx)) hinv
  have hsymm' : NablaRmSymmAt (I := I) (nablaRm04 x) := by
    simpa [cov, hcov, Rm04, nablaRm04, metricRm04, LeviCivita,
      metricCov, metricCov_smooth] using hsymm
  have hbianchi' : SecondBianchiAt (I := I) (nablaRm04 x) := by
    simpa [cov, hcov, Rm04, nablaRm04, metricRm04, LeviCivita,
      metricCov, metricCov_smooth] using hbianchi
  have htrace' : NablaRicTraceAt (I := I) basis
      (identityInvMetric (Idx := Idx)) (nablaRm04 x) (nablaRic x) := by
    simpa [cov, hcov, Rm04, nablaRm04, Ric, nablaRic, metricRm04,
      metricRicci, LeviCivita, metricCov, metricCov_smooth] using htrace
  have htrace_apply (A B C : TangentSpace I x) :
      nablaRic x (vec3 (I := I) A B C) =
        ∑ i : Idx, nablaRm04 x
          (vec5 (I := I) A (basis i) B C (basis i)) := by
    have ht := htrace' A B C
    simpa [cov, hcov, Rm04, nablaRm04, Ric, nablaRic,
      identityInvMetric, diagonalInvMetric] using ht
  have hterm (i : Idx) :
      nablaRm04 x
          (vec5 (I := I) (basis i) (basis i) v w (gradSection x)) +
        nablaRm04 x
          (vec5 (I := I) w (basis i) (gradSection x) v (basis i)) -
        nablaRm04 x
          (vec5 (I := I) (gradSection x) (basis i) w v (basis i)) = 0 := by
    have hb := hbianchi' (basis i) w (gradSection x) (basis i) v
    have hfirst := hsymm'.2.2 (basis i) (basis i) v w (gradSection x)
    have hsecondIn := hsymm'.2.1 w (basis i) (gradSection x) (basis i) v
    have hsecondOut := hsymm'.1 w (basis i) (gradSection x) (basis i) v
    have hthird := hsymm'.1 (gradSection x) (basis i) w (basis i) v
    rw [← hfirst] at hb
    rw [hsecondIn, hsecondOut] at hb
    rw [hthird] at hb
    linarith
  have hsum :
      (∑ i : Idx,
        (nablaRm04 x
            (vec5 (I := I) (basis i) (basis i) v w (gradSection x)) +
          nablaRm04 x
            (vec5 (I := I) w (basis i) (gradSection x) v (basis i)) -
          nablaRm04 x
            (vec5 (I := I) (gradSection x) (basis i) w v (basis i)))) =
        ∑ _i : Idx, (0 : Real) := by
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const_zero] at hsum
  rw [← htrace_apply w (gradSection x) v,
    ← htrace_apply (gradSection x) w v] at hsum
  have hcodazzi := gradientRicciSoliton_nablaRic_comm
    (I := I) (M := M) h x (gradSection x) w v
  have hRm13 : rm13RealizesConnection (I := I) cov
      (CovariantDerivative.rm13Section (I := I) (M := M) cov hcov) :=
    rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov)
  have hRm04 : rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04, metricRm04, cov, LeviCivita, metricCov] using
      (rm04Section_realizes (I := I) (M := M) g cov hcov)
  have hlower := rm04LowersRm13At_of_realizes
    (I := I) g cov
      (CovariantDerivative.rm13Section (I := I) (M := M) cov hcov)
      Rm04 hRm13 hRm04 x (gradSection x) w v (gradSection x)
  have hdu : duSec (I := I) f f.contMDiff x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradSection x)) := by
    change differential1FormFun (I := I) f x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradFun (I := I) g f x))
    exact differential1FormFun_eq_metric_dual_gradientFun (I := I) g f x
  rw [hdu] at hcodazzi
  have hcurv :
      nablaRic x (vec3 (I := I) (gradSection x) w v) -
          nablaRic x (vec3 (I := I) w (gradSection x) v) =
        Rm04 x (vec4 (I := I) (gradSection x) w v (gradSection x)) := by
    simpa [cov, hcov, Ric, nablaRic] using hcodazzi.trans hlower.symm
  have hRm04LC : rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04 := by
    simpa [cov, LeviCivita] using hRm04
  have hpair := rm04PairSymmAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04LC (x := x)
      (gradSection x) w v (gradSection x)
  have hout := rm04OutputSkewAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04LC (x := x)
      v (gradSection x) (gradSection x) w
  change (∑ i : Idx, nablaRm04 x
      (vec5 (I := I) (basis i) (basis i) v w (gradSection x))) =
    -Rm04 x (vec4 (I := I) v (gradSection x) w (gradSection x))
  rw [show (∑ i : Idx, nablaRm04 x
      (vec5 (I := I) (basis i) (basis i) v w (gradSection x))) =
      nablaRic x (vec3 (I := I) (gradSection x) w v) -
        nablaRic x (vec3 (I := I) w (gradSection x) v) by linarith]
  rw [hcurv]
  rw [show Rm04 x
      (vec4 (I := I) (gradSection x) w v (gradSection x)) =
      -Rm04 x (vec4 (I := I) v (gradSection x) w (gradSection x)) by
    rw [hpair]
    exact hout]

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_cov_grad
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    (X : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun y => gradFun (I := I) g f y) x X =
      (σ / 2 : Real) • X - ricEndoRaisedFib (I := I) g x X := by
  apply metricFlatLinear_injective (I := I) g x
  ext Y
  change g.inner x
      ((LeviCivita (I := I) g).toFun
        (fun y => gradFun (I := I) g f y) x X) Y =
    g.inner x ((σ / 2 : Real) • X - ricEndoRaisedFib (I := I) g x X) Y
  have hsol := h x X Y
  rw [hessFun_eq_cov_grad (I := I) g f.contMDiff x X Y] at hsol
  rw [← inner_ricEndoRaisedFib (I := I) (M := M) g x X Y] at hsol
  rw [map_sub, map_smul]
  change g.inner x
      ((LeviCivita (I := I) g).toFun
        (fun y => gradFun (I := I) g f y) x X) Y =
    (σ / 2) * g.inner x X Y -
      g.inner x (ricEndoRaisedFib (I := I) g x X) Y
  linear_combination hsol

omit [SigmaCompactSpace M] in
private theorem curvatureAction0SAt_metricRicci_symm
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M)) {x : M}
    (X Y U V : TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13
        (metricRicciAt (I := I) (M := M) g x) X Y
        (vec2 (I := I) U V) =
      curvatureAction0SAt (I := I) Rm13
        (metricRicciAt (I := I) (M := M) g x) X Y
        (vec2 (I := I) V U) := by
  let Ric := metricRicciAt (I := I) (M := M) g x
  have hzero : oneFormAtSlot0S (I := I) Ric (vec2 (I := I) U V) 0 =
      oneFormAtSlot0S (I := I) Ric (vec2 (I := I) V U) 1 := by
    ext W
    have hW : W = fun _ : Fin 1 => W 0 := by
      funext q
      fin_cases q
      rfl
    rw [hW]
    rw [oneFormAtSlot0S_apply, oneFormAtSlot0S_apply]
    have hleft : Function.update (vec2 (I := I) U V) 0 (W 0) =
        vec2 (I := I) (W 0) V := by
      funext q
      fin_cases q <;> simp [vec2, Curvature.vec2]
    have hright : Function.update (vec2 (I := I) V U) 1 (W 0) =
        vec2 (I := I) V (W 0) := by
      funext q
      fin_cases q <;> simp [vec2, Curvature.vec2]
    rw [hleft, hright]
    simpa [Ric, metricRicciAt_apply_eq_ricciTensor] using
      ricciTensor_symm (I := I) g x (W 0) V
  have hone : oneFormAtSlot0S (I := I) Ric (vec2 (I := I) U V) 1 =
      oneFormAtSlot0S (I := I) Ric (vec2 (I := I) V U) 0 := by
    ext W
    have hW : W = fun _ : Fin 1 => W 0 := by
      funext q
      fin_cases q
      rfl
    rw [hW]
    rw [oneFormAtSlot0S_apply, oneFormAtSlot0S_apply]
    have hleft : Function.update (vec2 (I := I) U V) 1 (W 0) =
        vec2 (I := I) U (W 0) := by
      funext q
      fin_cases q <;> simp [vec2, Curvature.vec2]
    have hright : Function.update (vec2 (I := I) V U) 0 (W 0) =
        vec2 (I := I) (W 0) U := by
      funext q
      fin_cases q <;> simp [vec2, Curvature.vec2]
    rw [hleft, hright]
    simpa [Ric, metricRicciAt_apply_eq_ricciTensor] using
      ricciTensor_symm (I := I) g x U (W 0)
  unfold curvatureAction0SAt
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change -(Rm13 x (oneFormAtSlot0S (I := I) Ric (vec2 (I := I) U V) 0)
        (vec3 (I := I) X Y U) +
      Rm13 x (oneFormAtSlot0S (I := I) Ric (vec2 (I := I) U V) 1)
        (vec3 (I := I) X Y V)) =
    -(Rm13 x (oneFormAtSlot0S (I := I) Ric (vec2 (I := I) V U) 0)
        (vec3 (I := I) X Y V) +
      Rm13 x (oneFormAtSlot0S (I := I) Ric (vec2 (I := I) V U) 1)
        (vec3 (I := I) X Y U))
  rw [hzero, hone]
  ring

omit [SigmaCompactSpace M] in
private theorem ricEndoRaisedFib_eq_sum_orthonormalBasis
    (g : SmoothRiemannianMetric I M) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (i : Idx) :
    ricEndoRaisedFib (I := I) g x (basis i) =
      ∑ k : Idx, ricciTensor (I := I) g x (basis i) (basis k) • basis k := by
  classical
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hcoeff (j : Idx) :
      basis.repr (ricEndoRaisedFib (I := I) g x (basis i)) j =
        ricciTensor (I := I) g x (basis i) (basis j) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
      (identityInvMetric (Idx := Idx)) hinv]
    rw [Finset.sum_eq_single j]
    · simp only [identityInvMetric, diagonalInvMetric, if_pos, one_mul]
      rw [inner_ricEndoRaisedFib (I := I) (M := M)]
    · intro k _ hkj
      simp [identityInvMetric, diagonalInvMetric, Ne.symm hkj]
    · simp
  calc
    ricEndoRaisedFib (I := I) g x (basis i) =
        ∑ k : Idx,
          basis.repr (ricEndoRaisedFib (I := I) g x (basis i)) k • basis k :=
      (basis.sum_repr _).symm
    _ = ∑ k : Idx,
        ricciTensor (I := I) g x (basis i) (basis k) • basis k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoeff k]

omit [SigmaCompactSpace M] in
omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_roughRicci_component
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (a b : Idx) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Rm04 := metricRm04 (I := I) (M := M) g
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let nabla2Ric := totalNabla0S (I := I) 3 cov nablaRic
      (totalNabla0S_regularity (I := I) 3 cov hcov nablaRic)
    let gradSection := gradG (I := I) g f
    (∑ i : Idx, nabla2Ric x
        (vec4 (I := I) (basis i) (basis i) (basis a) (basis b))) -
        nablaRic x (vec3 (I := I) (gradSection x) (basis a) (basis b)) =
      σ * Ric x (vec2 (I := I) (basis a) (basis b)) +
        2 * rm04RicciContractionAt (I := I) basis (Rm04 x)
          (identityInvMetric (Idx := Idx)) (Ric x) a b := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Rm13 := CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 := metricRm04 (I := I) (M := M) g
  let nablaRm04 := totalNabla0S (I := I) 4 cov Rm04
    (totalNabla0S_regularity (I := I) 4 cov hcov Rm04)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let nabla2Ric := totalNabla0S (I := I) 3 cov nablaRic
    (totalNabla0S_regularity (I := I) 3 cov hcov nablaRic)
  let gradSection := gradG (I := I) g f
  let scalar : M -> Real := fun y => metricScalarAt (I := I) (M := M) g y
  let hscalar := metricScalar_smooth (I := I) (M := M) g
  let HessScalar := hessianSec (I := I) cov hcov scalar hscalar
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hRm13 : rm13RealizesConnection (I := I) cov Rm13 :=
    rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov)
  have hRm04 : rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04, metricRm04, cov, LeviCivita, metricCov] using
      (rm04Section_realizes (I := I) (M := M) g cov hcov)
  have hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) :=
    rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x
  have hCodazziTerm (i : Idx) :
      nabla2Ric x
          (vec4 (I := I) (basis i) (basis i) (basis a) (basis b)) =
        nabla2Ric x
            (vec4 (I := I) (basis i) (basis a) (basis i) (basis b)) +
          nablaRm04 x
            (vec5 (I := I) (basis i) (basis i) (basis a) (basis b)
              (gradSection x)) +
          Rm04 x
            (vec4 (I := I) (basis i) (basis a) (basis b)
              (cov gradSection x (basis i))) := by
    have hc := gradientRicciSoliton_nabla2Ric_comm
      (I := I) (M := M) h x (basis i) (basis i) (basis a) (basis b)
    have hc' :
        nabla2Ric x
              (vec4 (I := I) (basis i) (basis i) (basis a) (basis b)) -
            nabla2Ric x
              (vec4 (I := I) (basis i) (basis a) (basis i) (basis b)) =
          nablaRm04 x
              (vec5 (I := I) (basis i) (basis i) (basis a) (basis b)
                (gradSection x)) +
            Rm04 x
              (vec4 (I := I) (basis i) (basis a) (basis b)
                (cov gradSection x (basis i))) := by
      simpa [cov, hcov, Rm04, nablaRm04, Ric, nablaRic, nabla2Ric,
        gradSection] using hc
    linarith
  have hCodazziSum :
      (∑ i : Idx, nabla2Ric x
          (vec4 (I := I) (basis i) (basis i) (basis a) (basis b))) =
        (∑ i : Idx, nabla2Ric x
            (vec4 (I := I) (basis i) (basis a) (basis i) (basis b))) +
          (∑ i : Idx, nablaRm04 x
            (vec5 (I := I) (basis i) (basis i) (basis a) (basis b)
              (gradSection x))) +
          ∑ i : Idx, Rm04 x
            (vec4 (I := I) (basis i) (basis a) (basis b)
              (cov gradSection x (basis i))) := by
    simp_rw [hCodazziTerm]
    simp only [Finset.sum_add_distrib]
  have hNabla20 : Nabla20SRealizesAt (I := I) 2
      (leviCivitaConnectionOfMetric (I := I) g) Ric nablaRic x
      (nabla2Ric x) := by
    constructor
    · intro y X slots
      exact (totalNabla0S_realizes (I := I) 2 cov Ric _) X y slots
    · intro X slots
      exact totalNabla0SFun_apply_section (I := I) 3 cov X nablaRic x slots
  have hRm13LC : rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13 := by
    simpa [cov, LeviCivita] using hRm13
  have hRicciIdentity := tensor0S_ricciIdentity_of_leviCivita
    (I := I) g Rm13 Ric nablaRic (Ric x) (nablaRic x) (nabla2Ric x)
      hRm13LC rfl rfl hNabla20
  have hRicciTerm (i : Idx) :
      nabla2Ric x
          (vec4 (I := I) (basis i) (basis a) (basis i) (basis b)) =
        nabla2Ric x
            (vec4 (I := I) (basis a) (basis i) (basis i) (basis b)) +
          curvatureAction0SAt (I := I) Rm13 (Ric x)
            (basis i) (basis a) (vec2 (I := I) (basis b) (basis i)) := by
    have hc := hRicciIdentity (basis i) (basis a)
      (vec2 (I := I) (basis i) (basis b))
    have hleft : metricTraceInput (I := I) (basis i) (basis a)
        (vec2 (I := I) (basis i) (basis b)) =
      vec4 (I := I) (basis i) (basis a) (basis i) (basis b) := by
      funext q
      fin_cases q <;> rfl
    have hright : metricTraceInput (I := I) (basis a) (basis i)
        (vec2 (I := I) (basis i) (basis b)) =
      vec4 (I := I) (basis a) (basis i) (basis i) (basis b) := by
      funext q
      fin_cases q <;> rfl
    rw [hleft, hright] at hc
    have hact :
        curvatureAction0SAt (I := I) Rm13 (Ric x)
            (basis i) (basis a) (vec2 (I := I) (basis i) (basis b)) =
          curvatureAction0SAt (I := I) Rm13 (Ric x)
            (basis i) (basis a) (vec2 (I := I) (basis b) (basis i)) := by
      simpa [Ric, metricRicci_apply] using
        curvatureAction0SAt_metricRicci_symm
          (I := I) (M := M) g Rm13
            (basis i) (basis a) (basis i) (basis b)
    rw [hact] at hc
    linarith
  have hRicciSum :
      (∑ i : Idx, nabla2Ric x
          (vec4 (I := I) (basis i) (basis a) (basis i) (basis b))) =
        (∑ i : Idx, nabla2Ric x
            (vec4 (I := I) (basis a) (basis i) (basis i) (basis b))) +
          ∑ i : Idx, curvatureAction0SAt (I := I) Rm13 (Ric x)
            (basis i) (basis a) (vec2 (I := I) (basis b) (basis i)) := by
    simp_rw [hRicciTerm]
    simp only [Finset.sum_add_distrib]
  have hBianchiTrace :
      (∑ i : Idx, nabla2Ric x
          (vec4 (I := I) (basis a) (basis i) (basis i) (basis b))) =
        (1 / 2 : Real) * HessScalar x
          (vec2 (I := I) (basis a) (basis b)) := by
    have hb := levi_civita_nabla_contracted_bianchi
      (I := I) (M := M) g basis (identityInvMetric (Idx := Idx)) hinv
        (basis a) (basis b)
    simpa [cov, hcov, Ric, nablaRic, nabla2Ric, scalar, hscalar, HessScalar,
      metricRicci, metricRicciAt, metricScalarAt,
      CovariantDerivative.ricciCurvatureAt, LeviCivita, metricCov, metricCov_smooth,
      identityInvMetric, diagonalInvMetric] using hb
  have hScalarTrace :
      HessScalar x (vec2 (I := I) (basis a) (basis b)) =
        2 * (nablaRic x
            (vec3 (I := I) (basis a) (gradSection x) (basis b)) +
          Ric x (vec2 (I := I) (cov gradSection x (basis a)) (basis b))) := by
    simpa [cov, hcov, Ric, nablaRic, gradSection, scalar, hscalar, HessScalar]
      using gradientRicciSoliton_hessian_scalar
        (I := I) (M := M) h x (basis a) (basis b)
  have hTraceNablaRm :
      (∑ i : Idx, nablaRm04 x
          (vec5 (I := I) (basis i) (basis i) (basis a) (basis b)
            (gradSection x))) =
        -Rm04 x (vec4 (I := I) (basis a) (gradSection x)
          (basis b) (gradSection x)) := by
    simpa [cov, hcov, Rm04, nablaRm04, gradSection] using
      gradientRicciSoliton_trace_nablaRm
        (I := I) (M := M) h x basis horth (basis a) (basis b)
  have hdu : duSec (I := I) f f.contMDiff x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradSection x)) := by
    change differential1FormFun (I := I) f x =
      dualToCotangent (I := I)
        ((tangentFlatLinearGen (I := I) g x) (gradFun (I := I) g f x))
    exact differential1FormFun_eq_metric_dual_gradientFun (I := I) g f x
  have hFirstCodazzi :
      nablaRic x
          (vec3 (I := I) (basis a) (gradSection x) (basis b)) -
        nablaRic x
          (vec3 (I := I) (gradSection x) (basis a) (basis b)) =
      Rm04 x (vec4 (I := I) (basis a) (gradSection x)
        (basis b) (gradSection x)) := by
    have hc := gradientRicciSoliton_nablaRic_comm
      (I := I) (M := M) h x (basis a) (gradSection x) (basis b)
    rw [hdu] at hc
    have hlower := hLower (basis a) (gradSection x) (basis b) (gradSection x)
    simpa [cov, hcov, Rm13, Ric, nablaRic] using hc.trans hlower.symm
  have hStructure :
      (∑ i : Idx, nabla2Ric x
          (vec4 (I := I) (basis i) (basis i) (basis a) (basis b))) -
          nablaRic x
            (vec3 (I := I) (gradSection x) (basis a) (basis b)) =
        (∑ i : Idx, curvatureAction0SAt (I := I) Rm13 (Ric x)
            (basis i) (basis a) (vec2 (I := I) (basis b) (basis i))) +
          (∑ i : Idx, Rm04 x
            (vec4 (I := I) (basis i) (basis a) (basis b)
              (cov gradSection x (basis i)))) +
          Ric x (vec2 (I := I) (cov gradSection x (basis a)) (basis b)) := by
    linarith [hCodazziSum, hRicciSum, hBianchiTrace, hScalarTrace,
      hTraceNablaRm, hFirstCodazzi]
  have hRicRm13 : ricciTensorRealizesRm13Trace (I := I) Ric Rm13 := by
    have h := (metricCurvatureSections (I := I) (M := M) g).ricciRealizes
    change ricciTensorRealizesRm13Trace (I := I)
      (metricRicci (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g) at h
    simpa only [Ric, Rm13, metricRm13, cov, LeviCivita, metricCov] using h
  have hTrace : RicciRealizesRm04FirstTraceAt (I := I)
      (Ric x) (Rm04 x) (identityInvMetric (Idx := Idx)) basis :=
    ricciFirstTraceAt_of_rm13_section (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv Ric Rm13 Rm04 hRicRm13 hLower
  have hRm04LC : rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04 := by
    simpa [cov, LeviCivita] using hRm04
  have hPair := rm04PairSymmAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04LC (x := x)
  have hOutput := rm04OutputSkewAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04LC (x := x)
  have hFirst := firstBianchiAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04LC (x := x)
  have hRicSymm : ∀ i j : Idx,
      Ric x (vec2 (I := I) (basis i) (basis j)) =
        Ric x (vec2 (I := I) (basis j) (basis i)) := by
    intro i j
    simpa [Ric, metricRicci_apply, metricRicciAt_apply_eq_ricciTensor] using
      ricciTensor_symm (I := I) g x (basis i) (basis j)
  have hInvSymm : ∀ i j : Idx,
      identityInvMetric (Idx := Idx) i j = identityInvMetric j i := by
    intro i j
    simp [identityInvMetric, diagonalInvMetric, eq_comm]
  have hAction :
      (∑ i : Idx, curvatureAction0SAt (I := I) Rm13 (Ric x)
          (basis i) (basis a) (vec2 (I := I) (basis b) (basis i))) =
        rm04RicciContractionAt (I := I) basis (Rm04 x)
            (identityInvMetric (Idx := Idx)) (Ric x) a b +
          ricciQuadraticAt (I := I) basis
            (identityInvMetric (Idx := Idx)) (Ric x) a b := by
    have ha := contracted_curvatureAction0SAt_vec2_eq
      (I := I) g basis (identityInvMetric (Idx := Idx)) hinv
        Rm13 (Rm04 x) (Ric x) hLower hTrace hPair hOutput hFirst
          hRicSymm hInvSymm a b
    simpa [identityInvMetric, diagonalInvMetric] using ha
  have hRicTrace :
      Ric x (vec2 (I := I) (basis a) (basis b)) =
        ∑ i : Idx, Rm04 x
          (vec4 (I := I) (basis i) (basis a) (basis b) (basis i)) := by
    have ht := hTrace a b
    simpa [identityInvMetric, diagonalInvMetric] using ht
  have hCovGrad (i : Idx) :
      cov gradSection x (basis i) =
        (σ / 2 : Real) • basis i - ricEndoRaisedFib (I := I) g x (basis i) := by
    change (LeviCivita (I := I) g).toFun
        (fun y => gradFun (I := I) g f y) x (basis i) = _
    exact gradientRicciSoliton_cov_grad (I := I) (M := M) h x (basis i)
  have hRaised (i : Idx) :
      ricEndoRaisedFib (I := I) g x (basis i) =
        ∑ k : Idx, Ric x (vec2 (I := I) (basis i) (basis k)) • basis k := by
    simpa [Ric, metricRicci_apply, metricRicciAt_apply_eq_ricciTensor] using
      ricEndoRaisedFib_eq_sum_orthonormalBasis
        (I := I) (M := M) g x basis horth i
  have hQuadratic :
      Ric x (vec2 (I := I) (ricEndoRaisedFib (I := I) g x (basis a))
          (basis b)) =
        ricciQuadraticAt (I := I) basis
          (identityInvMetric (Idx := Idx)) (Ric x) a b := by
    rw [hRaised]
    have hfun :
        (fun q : Fin 2 => if q = 0 then
          (∑ k : Idx, Ric x (vec2 (I := I) (basis a) (basis k)) • basis k)
          else basis b) =
          vec2 (I := I)
            (∑ k : Idx, Ric x (vec2 (I := I) (basis a) (basis k)) • basis k)
            (basis b) := by
      funext q
      rfl
    have hcurry := tensor0S_curry_one_apply (I := I) (Ric x)
      (∑ k : Idx, Ric x (vec2 (I := I) (basis a) (basis k)) • basis k)
      (basis b)
    rw [hfun] at hcurry
    rw [hcurry.symm]
    rw [_root_.map_sum, Tensor0SSpace.sum_apply]
    simp only [map_smul, Tensor0SSpace.smul_apply, smul_eq_mul,
      tensor0S_curry_one_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hvec :
        (fun q : Fin 2 => if q = 0 then basis k else basis b) =
          vec2 (I := I) (basis k) (basis b) := by
      funext q
      fin_cases q <;> rfl
    rw [hvec]
    simp [oneUp02CompAt,
      identityInvMetric, diagonalInvMetric]
  have hRmMapSub (i : Idx) (U V : TangentSpace I x) :
      Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) (U - V)) =
        Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) U) -
          Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) V) := by
    let m := vec4 (I := I) (basis i) (basis a) (basis b)
        (0 : TangentSpace I x)
    have hm := (Rm04 x).map_update_sub m (3 : Fin 4) U V
    have hleft : Function.update m (3 : Fin 4) (U - V) =
        vec4 (I := I) (basis i) (basis a) (basis b) (U - V) := by
      funext q
      fin_cases q <;> rfl
    have hU : Function.update m (3 : Fin 4) U =
        vec4 (I := I) (basis i) (basis a) (basis b) U := by
      funext q
      fin_cases q <;> rfl
    have hV : Function.update m (3 : Fin 4) V =
        vec4 (I := I) (basis i) (basis a) (basis b) V := by
      funext q
      fin_cases q <;> rfl
    rw [hleft, hU, hV] at hm
    exact hm
  have hRmMapSmul (i : Idx) (c : Real) :
      Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) (c • basis i)) =
        c * Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) (basis i)) := by
    let m := vec4 (I := I) (basis i) (basis a) (basis b)
        (0 : TangentSpace I x)
    have hm := (Rm04 x).map_update_smul m (3 : Fin 4) c (basis i)
    have hleft : Function.update m (3 : Fin 4) (c • basis i) =
        vec4 (I := I) (basis i) (basis a) (basis b) (c • basis i) := by
      funext q
      fin_cases q <;> rfl
    have hright : Function.update m (3 : Fin 4) (basis i) =
        vec4 (I := I) (basis i) (basis a) (basis b) (basis i) := by
      funext q
      fin_cases q <;> rfl
    rw [hleft, hright] at hm
    simpa [smul_eq_mul] using hm
  have hRmMapSum (i : Idx) (c : Idx -> Real) :
      Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b)
          (∑ k : Idx, c k • basis k)) =
        ∑ k : Idx, c k * Rm04 x
          (vec4 (I := I) (basis i) (basis a) (basis b) (basis k)) := by
    let m := vec4 (I := I) (basis i) (basis a) (basis b)
        (0 : TangentSpace I x)
    have hm := (Rm04 x).toMultilinearMap.map_update_sum Finset.univ
      (3 : Fin 4) (fun k => c k • basis k) m
    change Rm04 x (Function.update m (3 : Fin 4)
        (∑ k : Idx, c k • basis k)) =
      ∑ k : Idx, Rm04 x (Function.update m (3 : Fin 4) (c k • basis k)) at hm
    have hleft : Function.update m (3 : Fin 4) (∑ k : Idx, c k • basis k) =
        vec4 (I := I) (basis i) (basis a) (basis b)
          (∑ k : Idx, c k • basis k) := by
      funext q
      fin_cases q <;> rfl
    rw [hleft] at hm
    rw [show (∑ k : Idx,
        (Rm04 x) (Function.update m (3 : Fin 4) (c k • basis k))) =
        ∑ k : Idx, c k * Rm04 x
          (vec4 (I := I) (basis i) (basis a) (basis b) (basis k)) by
      apply Finset.sum_congr rfl
      intro k _
      have hmap := Tensor0SSpace.map_update_smul (I := I) (Rm04 x) m
        (3 : Fin 4) (c k) (basis k)
      have hvec : Function.update m (3 : Fin 4) (basis k) =
          vec4 (I := I) (basis i) (basis a) (basis b) (basis k) := by
        funext q
        fin_cases q <;> rfl
      rw [hvec] at hmap
      simpa [smul_eq_mul] using hmap] at hm
    exact hm
  have hRiemann :
      (∑ i : Idx, Rm04 x
        (vec4 (I := I) (basis i) (basis a) (basis b)
          (cov gradSection x (basis i)))) =
        (σ / 2 : Real) * Ric x (vec2 (I := I) (basis a) (basis b)) +
          rm04RicciContractionAt (I := I) basis (Rm04 x)
            (identityInvMetric (Idx := Idx)) (Ric x) a b := by
    have hterm (i : Idx) :
        Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b)
            (cov gradSection x (basis i))) =
          (σ / 2 : Real) * Rm04 x
              (vec4 (I := I) (basis i) (basis a) (basis b) (basis i)) -
            Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b)
              (ricEndoRaisedFib (I := I) g x (basis i))) := by
      rw [hCovGrad i, hRmMapSub, hRmMapSmul]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hRicTrace]
    have hInput : ∀ U V Z W : TangentSpace I x,
        Rm04 x (vec4 (I := I) V U Z W) =
          -Rm04 x (vec4 (I := I) U V Z W) := by
      exact rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04LC (x := x)
    have hraisedRm :
        (∑ i : Idx, Rm04 x
          (vec4 (I := I) (basis i) (basis a) (basis b)
            (ricEndoRaisedFib (I := I) g x (basis i)))) =
          -rm04RicciContractionAt (I := I) basis (Rm04 x)
            (identityInvMetric (Idx := Idx)) (Ric x) a b := by
      simp_rw [hRaised]
      simp_rw [hRmMapSum]
      have hContraction :
          rm04RicciContractionAt (I := I) basis (Rm04 x)
              (identityInvMetric (Idx := Idx)) (Ric x) a b =
            ∑ i : Idx, ∑ k : Idx,
              Rm04 x (vec4 (I := I) (basis a) (basis i) (basis b) (basis k)) *
                Ric x (vec2 (I := I) (basis i) (basis k)) := by
        unfold rm04RicciContractionAt raised02CompAt
        simp only [identityInvMetric, diagonalInvMetric]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        simp
      calc
        (∑ i : Idx, ∑ k : Idx,
            Ric x (vec2 (I := I) (basis i) (basis k)) *
              Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) (basis k))) =
          (∑ i : Idx, ∑ k : Idx,
              Ric x (vec2 (I := I) (basis i) (basis k)) *
                (-Rm04 x (vec4 (I := I) (basis a) (basis i) (basis b) (basis k)))) := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  rw [hInput (basis a) (basis i) (basis b) (basis k)]
        _ = -∑ i : Idx, ∑ k : Idx,
              Rm04 x (vec4 (I := I) (basis a) (basis i) (basis b) (basis k)) *
                Ric x (vec2 (I := I) (basis i) (basis k)) := by
                  simp only [mul_neg, Finset.sum_neg_distrib, neg_inj]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  ring
        _ = -rm04RicciContractionAt (I := I) basis (Rm04 x)
              (identityInvMetric (Idx := Idx)) (Ric x) a b := by
                simpa only using congrArg (fun z : Real => -z) hContraction.symm
    rw [hraisedRm]
    ring
  have hRicMapSub (U V : TangentSpace I x) :
      Ric x (vec2 (I := I) (U - V) (basis b)) =
        Ric x (vec2 (I := I) U (basis b)) -
          Ric x (vec2 (I := I) V (basis b)) := by
    let m := vec2 (I := I) (0 : TangentSpace I x) (basis b)
    have hm := (Ric x).map_update_sub m (0 : Fin 2) U V
    have hleft : Function.update m (0 : Fin 2) (U - V) =
        vec2 (I := I) (U - V) (basis b) := by
      funext q
      fin_cases q <;> rfl
    have hU : Function.update m (0 : Fin 2) U =
        vec2 (I := I) U (basis b) := by
      funext q
      fin_cases q <;> rfl
    have hV : Function.update m (0 : Fin 2) V =
        vec2 (I := I) V (basis b) := by
      funext q
      fin_cases q <;> rfl
    rw [hleft, hU, hV] at hm
    exact hm
  have hRicMapSmul (c : Real) :
      Ric x (vec2 (I := I) (c • basis a) (basis b)) =
        c * Ric x (vec2 (I := I) (basis a) (basis b)) := by
    let m := vec2 (I := I) (0 : TangentSpace I x) (basis b)
    have hm := (Ric x).map_update_smul m (0 : Fin 2) c (basis a)
    have hleft : Function.update m (0 : Fin 2) (c • basis a) =
        vec2 (I := I) (c • basis a) (basis b) := by
      funext q
      fin_cases q <;> rfl
    have hright : Function.update m (0 : Fin 2) (basis a) =
        vec2 (I := I) (basis a) (basis b) := by
      funext q
      fin_cases q <;> rfl
    rw [hleft, hright] at hm
    simpa [smul_eq_mul] using hm
  have hRicTerm :
      Ric x (vec2 (I := I) ((cov gradSection x) (basis a)) (basis b)) =
        (σ / 2 : Real) * Ric x (vec2 (I := I) (basis a) (basis b)) -
          ricciQuadraticAt (I := I) basis
            (identityInvMetric (Idx := Idx)) (Ric x) a b := by
    rw [hCovGrad a, hRicMapSub, hRicMapSmul, hQuadratic]
  have hfinal :
      (∑ i : Idx, curvatureAction0SAt (I := I) Rm13 (Ric x)
          (basis i) (basis a) (vec2 (I := I) (basis b) (basis i))) +
        (∑ i : Idx, Rm04 x
          (vec4 (I := I) (basis i) (basis a) (basis b)
            ((cov gradSection x) (basis i)))) +
        Ric x (vec2 (I := I) ((cov gradSection x) (basis a)) (basis b)) =
      σ * Ric x (vec2 (I := I) (basis a) (basis b)) +
        2 * rm04RicciContractionAt (I := I) basis (Rm04 x)
          (identityInvMetric (Idx := Idx)) (Ric x) a b := by
    rw [hAction, hRiemann, hRicTerm]
    ring
  dsimp only
  rw [hStructure]
  simpa only [Ric, Rm04] using hfinal

omit [SigmaCompactSpace M] in
theorem gradientRicciSoliton_weightedRoughLaplacian_ricci
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M) :
    weightedRoughLaplacian0S (I := I) g f
        (metricRicci (I := I) (M := M) g) x =
      σ • metricRicciAt (I := I) (M := M) g x -
        2 • curvatureRicciContractionAt (I := I) (M := M) g x := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := ob.toBasis
  have horth : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change D.inner (ob i) (ob j) = if i = j then 1 else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots : slots = ![slots 0, slots 1] := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]
  simp only [component0S_apply]
  have hbridge := Operator.weightedRoughLaplacian0S_metricRicci_apply_eq_sum_orthonormalBasis
    (I := I) (M := M) g f x basis horth
      (basis (slots 0)) (basis (slots 1))
  have hc := gradientRicciSoliton_roughRicci_component
    (I := I) (M := M) h x basis horth (slots 0) (slots 1)
  have hcurv := curvatureRicciContractionAt_eq_neg_rm04RicciContractionAt
    (I := I) (M := M) g x basis horth (slots 0) (slots 1)
  have hsum :
      (σ • metricRicciAt (I := I) (M := M) g x -
        2 • curvatureRicciContractionAt (I := I) (M := M) g x)
          (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        σ * metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) +
          2 * rm04RicciContractionAt (I := I) basis
            (metricRm04At (I := I) (M := M) g x)
            (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
            (metricRicciAt (I := I) (M := M) g x) (slots 0) (slots 1) := by
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul]
    have hsmul : (2 • curvatureRicciContractionAt (I := I) (M := M) g x)
          (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        2 * curvatureRicciContractionAt (I := I) (M := M) g x
          (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) := by
      rw [two_smul]
      rw [Tensor0SSpace.add_apply]
      ring
    rw [hsmul]
    rw [hcurv]
    simp only [metricRicciAt_apply_eq_ricciTensor]
    ring
  rw [show (fun a : Fin 2 => basis (![slots 0, slots 1] a)) =
      vec2 (I := I) (basis (slots 0)) (basis (slots 1)) by
        funext a
        fin_cases a <;> rfl]
  rw [hbridge]
  rw [hsum]
  simpa [metricRicciAt_apply_eq_ricciTensor] using hc

omit [SigmaCompactSpace M] in
theorem gradientRicciSoliton_weightedLaplacian_ricci_norm_sq
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    weightedLaplacian (I := I) g f
        (⟨fun y : M => normSq0S (I := I) g y 2 (Ric y),
          normSq0S_smooth (I := I) g Ric⟩ : C^∞⟮I, M; Real⟯) x =
      2 * σ * normSq0S (I := I) g x 2 (Ric x) -
        4 * inner0S (I := I) g x 2
          (curvatureRicciContractionAt (I := I) (M := M) g x) (Ric x) +
        2 * normSq0S (I := I) g x 3 (nablaRic x) := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  have hnorm := Operator.weightedLaplacian_normSq0S
    (I := I) (M := M) g f Ric x
  have hric := gradientRicciSoliton_weightedRoughLaplacian_ricci
    (I := I) (M := M) h x
  change weightedLaplacian (I := I) g f
      (⟨fun y : M => normSq0S (I := I) g y 2 (Ric y),
        normSq0S_smooth (I := I) g Ric⟩ : C^∞⟮I, M; Real⟯) x = _
  rw [hnorm, hric]
  rw [inner0S_sub_left, _root_.Tensor0SBundle.inner0S_smul_left,
    two_smul, inner0S_add_left]
  simp only [normSq0S_eq_inner]
  rw [← metricRicci_apply]
  ring

end DifferentialGeometry.Geometry
