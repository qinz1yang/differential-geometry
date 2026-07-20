import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionHeatProbeEnergy
import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace ReactionTwoDim

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Bundle Tensor0SBundle
open Tensor0SNabla
open DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


private lemma curry_eval1 [T2Space M] [SigmaCompactSpace M] {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 z)
    (v0 : TangentSpace I z) (vs : Fin 1 -> TangentSpace I z) :
    (tensor0S_curry (𝕜 := Real) (I := I) 1 z T v0) vs = T (Fin.cons v0 vs) :=
  TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) T v0 vs


theorem ricciSharpEndo_twoDim [T2Space M] [SigmaCompactSpace M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) (X : TangentSpace I x) :
    ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X
      = gaussCurvature (I := I) g x • X := by
  have key : ∀ Y : TangentSpace I x,
      g.inner x (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X) Y
        = g.inner x (gaussCurvature (I := I) g x • X) Y := by
    intro Y
    have h1 : ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X
        = cotangentSharp (I := I) g x
            ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) (metricRicci (I := I) g x) X) := rfl
    rw [h1, cotangentSharp_inner, cotangentToDual_apply]
    rw [curry_eval1 (I := I) (metricRicci (I := I) g x) X (fun _ : Fin 1 => Y)]
    rw [show (Fin.cons X (fun _ : Fin 1 => Y) : Fin 2 → TangentSpace I x)
        = vec2 (I := I) X Y from by funext i; fin_cases i <;> rfl]
    rw [metricRicci_apply, ricci_eq_gaussCurvature_smul_metric_twoDim hdim g x X Y]
    simp [map_smul]
  by_contra hne
  set v : TangentSpace I x := ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X
      - gaussCurvature (I := I) g x • X with hv
  have hvne : v ≠ 0 := by
    intro h0
    rw [hv, sub_eq_zero] at h0
    exact hne h0
  have hpos := g.pos x v hvne
  have hzero : g.inner x v v = 0 := by
    have keyC : g.inner x (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X)
        = g.inner x (gaussCurvature (I := I) g x • X) := ContinuousLinearMap.ext key
    have step : g.inner x v
        = g.inner x (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X)
          - g.inner x (gaussCurvature (I := I) g x • X) := by
      rw [hv]; exact map_sub (g.inner x) _ _
    have step2 : g.inner x v v
        = (g.inner x (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x) X)
          - g.inner x (gaussCurvature (I := I) g x • X)) v := by rw [step]
    rw [step2, ContinuousLinearMap.sub_apply, keyC, sub_self]
  exact absurd hzero (ne_of_gt hpos)


private lemma endoFirst_apply' [T2Space M] [SigmaCompactSpace M] {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X Y : TangentSpace I x) :
    endoSlotFirst (I := I) A T (vec2 (I := I) X Y) = T (vec2 (I := I) (A X) Y) := by
  have h1 : tensor0S_curry (𝕜 := Real) (I := I) 1 x (endoSlotFirst (I := I) A T)
      = ((tensor0S_curry (𝕜 := Real) (I := I) 1 x) T).comp A :=
    (tensor0S_curry (𝕜 := Real) (I := I) 1 x).apply_symm_apply _
  have e1 : endoSlotFirst (I := I) A T (vec2 (I := I) X Y)
      = (tensor0S_curry (𝕜 := Real) (I := I) 1 x (endoSlotFirst (I := I) A T) X)
          (fun _ : Fin 1 => Y) := by
    rw [curry_eval1 (I := I) (endoSlotFirst (I := I) A T) X (fun _ : Fin 1 => Y)]
    congr 1
    funext i; fin_cases i <;> rfl
  rw [e1, h1, ContinuousLinearMap.comp_apply,
    curry_eval1 (I := I) T (A X) (fun _ : Fin 1 => Y)]
  congr 1
  funext i; fin_cases i <;> rfl


private lemma smul_slot0 [T2Space M] [SigmaCompactSpace M] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (X Y : TangentSpace I x) :
    T (vec2 (I := I) (c • X) Y) = c * T (vec2 (I := I) X Y) := by
  have h0 : vec2 (I := I) (c • X) Y
      = Function.update (vec2 (I := I) X Y) 0 (c • X) := by
    funext i; fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h1 : vec2 (I := I) X Y = Function.update (vec2 (I := I) X Y) 0 X := by
    funext i; fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [h0, T.map_update_smul, ← h1]
  simp


private lemma smul_slot1 [T2Space M] [SigmaCompactSpace M] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (X Y : TangentSpace I x) :
    T (vec2 (I := I) X (c • Y)) = c * T (vec2 (I := I) X Y) := by
  have h0 : vec2 (I := I) X (c • Y)
      = Function.update (vec2 (I := I) X Y) 1 (c • Y) := by
    funext i; fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h1 : vec2 (I := I) X Y = Function.update (vec2 (I := I) X Y) 1 Y := by
    funext i; fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [h0, T.map_update_smul, ← h1]
  simp


private lemma endoSecond_apply' [T2Space M] [SigmaCompactSpace M] {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (X Y : TangentSpace I x) :
    endoSlotSecond (I := I) A T (vec2 (I := I) X Y) = T (vec2 (I := I) X (A Y)) := by
  have hswap : ∀ P Q : TangentSpace I x,
      (fun i => (vec2 (I := I) P Q) ((Equiv.swap (0 : Fin 2) 1) i)) = vec2 (I := I) Q P := by
    intro P Q; funext i
    fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hkey : endoSlotSecond (I := I) A T (vec2 (I := I) X Y)
      = endoSlotFirst (I := I) A (T.domDomCongr (Equiv.swap (0 : Fin 2) 1))
          (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) := rfl
  rw [hkey, hswap X Y, endoFirst_apply' (I := I) A (T.domDomCongr (Equiv.swap (0 : Fin 2) 1)) Y X]
  change T (fun i => (vec2 (I := I) (A Y) X) ((Equiv.swap (0 : Fin 2) 1) i))
      = T (vec2 (I := I) X (A Y))
  rw [hswap (A Y) X]


theorem ricciReactionInner_twoDim [T2Space M] [SigmaCompactSpace M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    ricciReactionInner (I := I) g x (metricRicci (I := I) g x) T
      = 4 * gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 T := by
  have hvec : ∀ v : Fin 2 → TangentSpace I x, v = vec2 (I := I) (v 0) (v 1) := by
    intro v; funext i; fin_cases i <;> rfl
  have hFirst : endoSlotFirst (I := I)
      (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x)) T
      = gaussCurvature (I := I) g x • T := by
    ext v
    rw [hvec v, endoFirst_apply', ricciSharpEndo_twoDim hdim g x (v 0),
      smul_slot0 T (gaussCurvature (I := I) g x) (v 0) (v 1)]
    simp
  have hSecond : endoSlotSecond (I := I)
      (ricciSharpEndo (I := I) g x (metricRicci (I := I) g x)) T
      = gaussCurvature (I := I) g x • T := by
    ext v
    rw [hvec v, endoSecond_apply', ricciSharpEndo_twoDim hdim g x (v 1),
      smul_slot1 T (gaussCurvature (I := I) g x) (v 0) (v 1)]
    simp
  rw [ricciReactionInner, hFirst, hSecond, inner0S_smul_left]
  rw [show inner0S (I := I) g x 2 T T = normSq0S (I := I) g x 2 T from rfl]
  ring


theorem scalarCurvatureFromRicciInVolumeFrameOn_twoDim
    [T2Space M] [SigmaCompactSpace M]
    (hdim : Module.finrank Real E = 2)
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family
        S.toRealizedCandidate.ricci t x
      = 2 * gaussCurvature (I := I) (S.family.metric t) x := by
  classical
  set g : SmoothRiemannianMetric I M := S.family.metric t with hgdef
  set K : Real := gaussCurvature (I := I) g x with hKdef
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hunfold : scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family
        S.toRealizedCandidate.ricci t x
      = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          Volume.volumeTraceInvMetricComponents (I := I) (M := M) g x i j *
            S.toRealizedCandidate.ricci t x
              (Volume.volumeTraceFrame (I := I) (M := M) i x)
              (Volume.volumeTraceFrame (I := I) (M := M) j x) :=
    scalarCurvatureFromRicciTraceInFrame_apply (I := I) (M := M)
      (S.toRealizedCandidate.ricci t)
      (Volume.volumeTraceInvMetricComponents (I := I) (M := M) g)
      (Volume.volumeTraceFrame (I := I) (M := M)) x
  have hRic : ∀ i j : Fin (Module.finrank Real E),
      S.toRealizedCandidate.ricci t x
          (Volume.volumeTraceFrame (I := I) (M := M) i x)
          (Volume.volumeTraceFrame (I := I) (M := M) j x)
        = K * chartGramMatrix (I := I) g x x i j := by
    intro i j
    have hshow : S.toRealizedCandidate.ricci t x
        (Volume.volumeTraceFrame (I := I) (M := M) i x)
        (Volume.volumeTraceFrame (I := I) (M := M) j x)
        = metricRicciAt (I := I) g x
            (vec2 (I := I) (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x)) := rfl
    rw [hshow, ricci_eq_gaussCurvature_smul_metric_twoDim hdim g x, chartGramMatrix_apply]
  have hginv : ∀ i j : Fin (Module.finrank Real E),
      Volume.volumeTraceInvMetricComponents (I := I) (M := M) g x i j
        = chartInvGramMatrix (I := I) g x x i j := fun _ _ => rfl
  have hsym : ∀ i j : Fin (Module.finrank Real E),
      chartGramMatrix (I := I) g x x i j = chartGramMatrix (I := I) g x x j i := by
    intro i j
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    exact g.symm x _ _
  have hrow : ∀ i : Fin (Module.finrank Real E),
      ∑ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g x x i j * chartGramMatrix (I := I) g x x i j
        = (1 : Real) := by
    intro i
    have hflip : ∀ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g x x i j * chartGramMatrix (I := I) g x x i j
          = chartInvGramMatrix (I := I) g x x i j * chartGramMatrix (I := I) g x x j i := by
      intro j; rw [← hsym i j]
    rw [Finset.sum_congr rfl (fun j _ => hflip j), ← Matrix.mul_apply,
      chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase, Matrix.one_apply_eq]
  have hcard : (∑ _i : Fin (Module.finrank Real E), (1 : Real)) = 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
    norm_num
  rw [hunfold]
  calc
    (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        Volume.volumeTraceInvMetricComponents (I := I) (M := M) g x i j *
          S.toRealizedCandidate.ricci t x
            (Volume.volumeTraceFrame (I := I) (M := M) i x)
            (Volume.volumeTraceFrame (I := I) (M := M) j x))
        = ∑ i : Fin (Module.finrank Real E), K *
            (∑ j : Fin (Module.finrank Real E),
              chartInvGramMatrix (I := I) g x x i j *
                chartGramMatrix (I := I) g x x i j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hginv i j, hRic i j]
          ring
    _ = ∑ _i : Fin (Module.finrank Real E), K * (1 : Real) := by
          exact Finset.sum_congr rfl (fun i _ => by rw [hrow i])
    _ = K * (∑ _i : Fin (Module.finrank Real E), (1 : Real)) := by
          rw [Finset.mul_sum]
    _ = 2 * K := by rw [hcard]; ring


theorem nablaRic_twoDim [T2Space M] [SigmaCompactSpace M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) (M := M) g) (metricRicci (I := I) (M := M) g) x
        (vec3 (I := I) A B C)
      = extDerivFun (I := I) (gaussCurvature (I := I) g) x A * g.inner x B C := by
  classical
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let K : M -> Real := fun y : M => gaussCurvature (I := I) g y
  have hK : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) K :=
    gaussCurvature_contMDiff (I := I) (M := M) g
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 1)
  let dK : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    duSec (I := I) K hK
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) g
  let smulSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
      K hK metricSec
  have hdK : ∀ y : M, ∀ v : TangentSpace I y,
      dK y (fun _ : Fin 1 => v) = extDerivFun (I := I) K y v := by
    intro y v
    change differential1FormFun (I := I) K y (fun _ : Fin 1 => v) = extDerivFun (I := I) K y v
    rw [differential1FormFun_apply_eq_extDerivFun]
  have hRicEq : Ric = smulSec := by
    apply DFunLike.ext
    intro y
    apply ContinuousMultilinearMap.ext
    intro slots
    have hslots : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i
      fin_cases i <;> rfl
    have h2 := ricci_eq_gaussCurvature_smul_metric_twoDim hdim g y (slots 0) (slots 1)
    rw [hslots]
    change metricRicciAt (I := I) (M := M) g y (vec2 (I := I) (slots 0) (slots 1)) =
      K y * metricSec y (vec2 (I := I) (slots 0) (slots 1))
    simpa [K, metricSec, metricTensorField_apply,
      DifferentialGeometry.Integral.Connection.vec2] using h2
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_smooth (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose
  have hX : X x = A :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose_spec
  let slots : Fin 2 -> TangentSpace I x := vec2 (I := I) B C
  have hreal :=
    nabla_smul_metric (I := I) (M := M) cov g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      K hK dK hdK
  have happly := TotalNabla0SRealizes.apply (I := I) hreal X x slots
  have hsection :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X smulSec x slots
  have htot :
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          dK metricSec) x (Fin.cons (X x) slots) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov smulSec x (Fin.cons (X x) slots) := by
    calc
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          dK metricSec) x (Fin.cons (X x) slots)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov X smulSec x slots := by
          simpa [metricSec, smulSec] using happly
      _ =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov smulSec x (Fin.cons (X x) slots) := hsection.symm
  have hslots3 : Fin.cons A slots = vec3 (I := I) A B C := by
    funext i
    fin_cases i <;> rfl
  have hslots3X : Fin.cons (X x) slots = vec3 (I := I) A B C := by
    rw [hX, hslots3]
  have hprodEval :
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          dK metricSec) x (Fin.cons (X x) slots) =
        extDerivFun (I := I) K x A * g.inner x B C := by
    change (Bundle.continuousMultilinearMap.product_fun
        (dK x) (metricSec x)) (Fin.cons (X x) slots) =
      extDerivFun (I := I) K x A * g.inner x B C
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft : Fin.cons (X x) slots ∘ Fin.castAdd 2 = fun _ : Fin 1 => A := by
      funext i
      fin_cases i
      exact hX
    have hright : Fin.cons (X x) slots ∘ Fin.natAdd 1 = slots := by
      funext i
      fin_cases i <;> rfl
    rw [hleft, hright, ← hdK x A]
    congr 1
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric x (vec3 (I := I) A B C)
        =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov smulSec x (vec3 (I := I) A B C) := by rw [hRicEq]
    _ =
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          dK metricSec) x (Fin.cons (X x) slots) := by rw [← hslots3X, ← htot]
    _ = extDerivFun (I := I) K x A * g.inner x B C := hprodEval


set_option linter.unusedVariables false in
theorem reaction_integrand_twoDim
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (hdim : Module.finrank Real E = 2)
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t₀ : RealTimeInterval.RegularTime D) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    ricciReactionInner (I := I) (S.family.metric (t₀ : Real)) x
        (metricRicci (I := I) (S.family.metric (t₀ : Real)) x) T
      + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
          (ricciVariationOneFormReaction (I := I) (S.family.metric (t₀ : Real)) x
            (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (S.family.connection (t₀ : Real))
              (metricRicci (I := I) (S.family.metric (t₀ : Real))) x) α) T
      - scalarCurvatureFromRicciInVolumeFrameOn (I := I) (M := M) S.family
          S.toRealizedCandidate.ricci (t₀ : Real) x
        * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 T
      = 2 * gaussCurvature (I := I) (S.family.metric (t₀ : Real)) x
          * normSq0S (I := I) (S.family.metric (t₀ : Real)) x 2 T
        + 2 * inner0S (I := I) (S.family.metric (t₀ : Real)) x 2
            (oneFormReaction2D (I := I) (S.family.metric (t₀ : Real)) α) T := by
  classical
  set g : SmoothRiemannianMetric I M := S.family.metric (t₀ : Real) with hgdef
  set nablaRic : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (S.family.connection (t₀ : Real)) (metricRicci (I := I) g) x with hnabladef
  have hconn : S.family.connection (t₀ : Real) = metricCov (I := I) (M := M) g := rfl
  have hRicDeriv : ∀ Y V W : TangentSpace I x,
      nablaRic (vec3 (I := I) Y V W)
        = extDerivFun (I := I) (gaussCurvature (I := I) g) x Y * g.inner x V W := by
    intro Y V W
    rw [hnabladef, hconn]
    exact nablaRic_twoDim hdim g x Y V W
  have hreac : oneFormReaction2D (I := I) g α
      = ricciVariationOneFormReaction (I := I) g x nablaRic α :=
    oneFormReaction2D_eq_ricciVariation (I := I) hdim g α nablaRic hRicDeriv
  rw [ricciReactionInner_twoDim hdim g x T,
    scalarCurvatureFromRicciInVolumeFrameOn_twoDim hdim S (t₀ : Real) x,
    ← hgdef, ← hreac]
  ring


end ReactionTwoDim
end Evolution
end DifferentialGeometry.PDE.RicciFlow
