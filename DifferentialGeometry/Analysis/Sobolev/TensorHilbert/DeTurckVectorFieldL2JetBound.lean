import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import Mathlib.Analysis.MeanInequalities

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieWEndoSection (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => deTurckLieWEndo (I := I) g₁ g_bg x
  contMDiff_toFun := deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg

@[simp] lemma deTurckLieWEndoSection_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg x =
      deTurckLieWEndo (I := I) g₁ g_bg x := rfl

def deTurckLieWEndoInsert (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 1 :=
  slotInsertEndoCc (I := I) (M := M) g₀ 0
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)

private def wVF (g₁ g_bg : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b :=
  fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b

private def wXi (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ g_bg

private def wOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (wXi (I := I) (M := M) g₀ g₁ g_bg)

private def wAlphaA (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg))

private def wCA (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (connDiffLoweredCc (I := I) g₀ g₁))

private def wAlphaB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
    (wOmega (I := I) (M := M) g₀ g₁ g_bg)

private def wAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  wAlphaA (I := I) (M := M) g₀ g₁ g_bg + wAlphaB (I := I) (M := M) g₀ g₁ g_bg

private lemma connDiffLoweredCc_unitModel' (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

private lemma connDiffLoweredCc_unitModel_apply' (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [connDiffLoweredCc_unitModel']
  rfl

private lemma unitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]

private lemma wXi_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (wXi (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (m 0) (m 1)) (m 2) := by
  rw [wXi, unitModel_sub, ContinuousMultilinearMap.sub_apply,
    connDiffLoweredCc_unitModel_apply', connDiffLoweredCc_unitModel_apply']
  rw [show g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, ContinuousLinearMap.sub_apply]]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ g_bg x (m 0) (m 1)]

private lemma wOmega_toSection_unit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (wXi (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [wOmega, appCc_toSection]
  rfl

private lemma wOmega_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => z) =
      g₀.inner x (wVF (I := I) (M := M) g₁ g_bg x) z := by
  classical
  rw [unitModel, wOmega_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (wXi (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) (fun _ : Fin 1 => z) =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x) (vs := fun _ : Fin 1 => z)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
        (fun _ : Fin 1 => (show E from z)))]
    have hm : Tensor0SSpace.toModel D
        (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
          (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
            (fun _ : Fin 1 => (show E from z)))) =
        unitModel (I := I) (M := M) g₀ 3 (wXi (I := I) (M := M) g₀ g₁ g_bg) x
          ![smoothOrthoFrame (I := I) g₁ x i x, smoothOrthoFrame (I := I) g₁ x i x, z] := by
      rw [unitModel, ← hD]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hm, wXi_unitModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, ContinuousLinearMap.sum_apply]]
  rw [wVF, ← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ g_bg x]

private lemma wOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (wVF (I := I) (M := M) g₁ g_bg x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (wVF (I := I) (M := M) g₁ g_bg x) (m 0) :=
    wOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x (m 0)
  rw [hL]
  have hR : Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (wVF (I := I) (M := M) g₁ g_bg x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (wVF (I := I) (M := M) g₁ g_bg x)) (m 0) := by
    rw [cotangentToDual_apply]
    rfl
  rw [hR, cotangentToDual_g0FlatCLM]

private lemma unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

private lemma tensor0SCovariantDerivative01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (Y x) (fun i => Fin.elim0 i)) =
      directionalDerivAt (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v)
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

private lemma wOmega_toSection_unitZero (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (b : M) :
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 1 I b from
        (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection b)
      (unitZeroSec (I := I) (M := M) b) =
      g0FlatCLM (I := I) g₀ b (wVF (I := I) (M := M) g₁ g_bg b) :=
  wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg b

private lemma unitEvalSection_wOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      g₀.inner b (wVF (I := I) (M := M) g₁ g_bg b) z := by
  rw [unitEvalSection_apply, wOmega_toSection_unitZero]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (wVF (I := I) (M := M) g₁ g_bg b))
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (wVF (I := I) (M := M) g₁ g_bg b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (wVF (I := I) (M := M) g₁ g_bg b))
        (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (wVF (I := I) (M := M) g₁ g_bg b))
        (fun _ : Fin 1 => (show E from z))
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

private lemma wVF_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (wVF (I := I) (M := M) g₁ g_bg b)) :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff

private lemma wAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (wAlphaA (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [wAlphaA, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, w] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![w, u] from by
    funext i; fin_cases i <;> simp]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (wOmega (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x) ![w, u]]
  rw [show (![w, u] : Fin 2 → TangentSpace I x) 0 = w from rfl]
  rw [show Matrix.vecTail (![w, u] : Fin 2 → TangentSpace I x) = ![u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (wOmega (I := I) (M := M) g₀ g₁ g_bg) x w]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 1
    (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (wOmega (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons (Y x) (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [tensor0SCovariantDerivative01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (Y b) (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (wVF (I := I) (M := M) g₁ g_bg b) (Y b)) := by
    funext b
    exact unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDerivAt_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := wVF (I := I) (M := M) g₁ g_bg) (W := fun b => Y b)
    (wVF_contMDiff (I := I) (M := M) g₁ g_bg) Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w)
        (fun i => Fin.elim0 i)) =
      g₀.inner x (wVF (I := I) (M := M) g₁ g_bg x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

private lemma interior_product_toModel_eval' (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

private lemma wAlphaB_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (wAlphaB (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w) u := by
  classical
  rw [unitModel, wAlphaB, appCc_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [wCA, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (wVF (I := I) (M := M) g₁ g_bg x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (wVF (I := I) (M := M) g₁ g_bg x)]
  rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
    (wVF (I := I) (M := M) g₁ g_bg x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (Fin.cons (show E from wVF (I := I) (M := M) g₁ g_bg x)
        (fun k : Fin 2 => (show E from (![u, w] : Fin 2 → TangentSpace I x) k))) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁)) x
        ![wVF (I := I) (M := M) g₁ g_bg x, u, w] := by
    rw [unitModel, ← hD]
    rfl
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![wVF (I := I) (M := M) g₁ g_bg x, u, w] : Fin 3 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![wVF (I := I) (M := M) g₁ g_bg x, w, u] from by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]]
  rw [connDiffLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

private lemma wEndo_eq_covDeriv_add_connDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w := by
  have hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (wVF (I := I) (M := M) g₁ g_bg b)) x :=
    ((wVF_contMDiff (I := I) (M := M) g₁ g_bg) x).mdifferentiableAt (by simp)
  have hcd := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀
    (σ := wVF (I := I) (M := M) g₁ g_bg) (x := x) hW w
  have hEndo : deTurckLieWEndo (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₁).toFun (wVF (I := I) (M := M) g₁ g_bg) x w := rfl
  rw [hEndo, hcd]
  abel

private lemma cotangentToDual_slotInsertEndoFib' (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k; fin_cases k; simp]
  rfl

private lemma cotangentToDual_cometricRaise_wAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (wAlpha (I := I) (M := M) g₀ g₁ g_bg) x
        ![inverseMetricSharpFib (I := I) g₀ x om, w] := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (wAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (wAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => w) from rfl]
  rw [interior_product_toModel_eval' (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (wAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

private theorem deTurckLieWEndoInsert_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (wAlpha (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [cotangentToDual_cometricRaise_wAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g_bg x) om w]
  rw [wEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [wAlpha, unitModel_add, ContinuousMultilinearMap.add_apply,
    wAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    wAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w +
          PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w) from by
    rw [← cotangentToDualLinear_apply, map_add]]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w)).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w)).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun (wVF (I := I) (M := M) g₁ g_bg) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_bg x) w)]

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedVariables false in
private theorem diagonalProductTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]; nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

set_option linter.unusedVariables false in
private theorem diagonalProductGrid_rfns_integral_ballUniform_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a + 1 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := diagonalProductTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finset_sum
        intro n hn
        apply MeasureTheory.integrable_finset_sum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finset_sum _
        (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

section RaisedKoszulSuccHelpers

private lemma raisedKoszul_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hsqrt := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hsqrt

private lemma raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S : SmoothCcTensor g₀ 0 s) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n (domDomCongrSection (I := I) g₀ σ S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + n) x
        ((iteratedCovGrad (I := I) g₀ 0 s n
          (domDomCongrSection (I := I) g₀ σ S)).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + n) x
        ((iteratedCovGrad (I := I) g₀ 0 s n S).toSection x)) :=
    funext fun x =>
      riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) g₀ σ S n x
  rw [hpt]

private lemma raisedKoszul_norm_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 m (symmS (I := I) g₀ P)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ := by
  rw [iteratedCovGrad_symmS_eq (I := I) g₀ P m]
  refine le_trans (norm_add_le _ _) ?_
  simp only [norm_smul, Real.norm_eq_abs]
  rw [raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 2 (Equiv.swap 0 1) P m,
    show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
  linarith

private lemma raisedKoszul_norm_iteratedCovGrad_eq_koszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) g₀ g₁ P htie,
    SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (koszulCovecCc (I := I) g₀ P))).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)).toSection x)) :=
    funext fun x =>
      rfns_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) g₀ P n x
  rw [hpt]

private lemma raisedKoszul_norm_iteratedCovGrad_koszul_le
    (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)‖ ≤
      (3 / 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ := by
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ P with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hkos : koszulCovecCc (I := I) g₀ P = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hWeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) (symmS (I := I) g₀ P)‖ := by
    refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs, hW, symmSCovGrad3_def]
    have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ P))).toSection x)) =
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) (symmS (I := I) g₀ P)).toSection x)) :=
      funext fun x =>
        rfns_iteratedCovGrad_covGrad_comm_rs (I := I) g₀ 0 2 n (symmS (I := I) g₀ P) x
    rw [hpt]
  have hDAeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DA‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDA]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hDBeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DB‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDB]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hDCeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DC‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDC]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hsymmS_le := raisedKoszul_norm_iteratedCovGrad_symmS_le (I := I) g₀ P (n + 1)
  have hWbound : ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ := le_trans (le_of_eq hWeq) hsymmS_le
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 n (DA + DB - DC)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n DA‖ + ‖iteratedCovGrad (I := I) g₀ 0 3 n DB‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 3 n DC‖ := by
    rw [show DA + DB - DC = DA + DB + (-DC) from by abel, iteratedCovGrad_add,
      iteratedCovGrad_add, iteratedCovGrad_neg]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
    exact add_le_add (norm_add_le _ _) le_rfl
  rw [hDAeq, hDBeq, hDCeq] at htri
  rw [hkos, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs,
    show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
  linarith [htri, hWbound]

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
private theorem raisedKoszul_order0sup_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤ F i := by
  obtain ⟨C, hC_nn, hC⟩ :=
    rfns_raisedKoszul_le_of_lt_one (I := I) g₀ (le_max_right δ₀ 0) (max_lt hδ₀ one_pos)
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) g₀ a ha_super
  refine ⟨C * (Csob * R), fun i => ((i : ℝ) + 1) * ((3 / 2) * R) ^ 2,
    mul_nonneg hC_nn (mul_nonneg hCsob_nn hR), fun i => by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x) := by
          have heq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
          rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x v v := g₀.pos x v hv
    have hbound := hδ x v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x v v| := abs_nonneg _
    have hδ0 : 0 ≤ δ := by
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hrfns := hC g₁ P htie (le_trans hδ_le (le_max_left δ₀ 0)) hδ0 hδ x
    have henv := hCsob P P hR hPball hPball 0 (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩) x
    simp only [DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_zero] at henv
    letI instTens12 : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + 1) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
    set N : ℝ := ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖ with hN_def
    have hN_nn : 0 ≤ N := norm_nonneg _
    have hnorm_le : N ≤ Csob * R := by
      refine le_trans ?_ henv
      exact Finset.single_le_sum (f := fun j =>
          letI : Bundle.RiemannianBundle
              (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)
          (fun j _ =>
            letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x))
          (by simp : (1 : ℕ) ∈ Finset.range 3)
    have hsq : N ^ 2 ≤ (Csob * R) ^ 2 := by nlinarith [hnorm_le, hN_nn]
    refine le_trans hrfns ?_
    rw [show (C * (Csob * R)) ^ 2 = C ^ 2 * (Csob * R) ^ 2 from by rw [mul_pow]]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
  · intro i hi
    have hbnd : ∀ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
          ((3 / 2) * R) ^ 2 := by
      intro n hn
      have hni : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have h3a := raisedKoszul_norm_iteratedCovGrad_eq_koszul (I := I) g₀ g₁ P htie n
      have h3b := raisedKoszul_norm_iteratedCovGrad_koszul_le (I := I) g₀ P n
      have hPn1 : ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ≤ R := hPball (n + 1) (by omega)
      have hle : ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ≤
          (3 / 2) * R := by
        rw [h3a]
        exact le_trans h3b (mul_le_mul_of_nonneg_left hPn1 (by norm_num))
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    refine le_trans (Finset.sum_le_sum hbnd) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

end RaisedKoszulSuccHelpers

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem cometricCastG0_order0sup_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤ F i := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_mos, hK_mos_nn, hK_mos⟩ :=
    diagonalProductGrid_rfns_integral_ballUniform_succ
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_mos q with hKW_def
  set FW : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1), KW q with hFW_def
  set KD : ℕ → ℝ := fun l => appCcGdiag (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * FW l with hKD_def
  set aL : ℕ → ℝ :=
    fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  set Ff : ℕ → ℝ :=
    fun i => ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * KD l) with hFf_def
  set ΛT2 : ℝ := fr ^ 2 * C_base 0 with hΛT2_def
  have hFnn : ∀ i, 0 ≤ Ff i := by
    intro i
    simp only [hFf_def]
    apply Finset.sum_nonneg
    intro l _
    have h1 : 0 ≤ aL l := by simp only [haL_def]; positivity
    have h2 : 0 ≤ KD l := by
      simp only [hKD_def, hFW_def, hKW_def]
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg _)
        (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) ?_
      exact Finset.sum_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (by positivity) (hC_base_nn q)) (hK_mos_nn q))
    linarith
  refine ⟨Real.sqrt (2 * SΦ 0 + 2 * (SΦ 0 * ΛT2)), Ff, Real.sqrt_nonneg _, hFnn, ?_⟩
  · intro g₁ P δ hδ_le hδ htie hPball
    by_cases hMne : Nonempty M
    · obtain ⟨x₀⟩ := hMne
      have hδ0 : 0 ≤ δ := by
        obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
          haveI : Nontrivial (TangentSpace I x₀) := by
            have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
              have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
              rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
            exact Module.nontrivial_of_finrank_pos hfr'
          exact exists_ne 0
        have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
        have hbound := hδ x₀ v v
        have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
        have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      set W : SmoothCcTensor g₀ 3 3 :=
        slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        with hW_def
      have hid : cometricCastG0 (I := I) g₀ g₁ =
          Φ + appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W := by
        have h := cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
        rw [← hΦ_def, ← hW_def] at h
        exact h
      have hΛT : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x) ≤ ΛT2 := by
        intro x
        have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) 0 x
        simp only [iteratedCovGrad_zero] at h1
        rw [← hW_def, ← hfr_def] at h1
        have h2 := hC_base g₁ P htie hδ_le hδ0 hδ 0 x
        simp only [iteratedCovGrad_zero] at h2
        have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
          simp
        rw [hgrid0, mul_one] at h2
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x)
            ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                ((slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) := h1
          _ ≤ fr ^ 2 * C_base 0 := mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
          _ = ΛT2 := hΛT2_def.symm
      have hstep2 : ∀ q : ℕ, q ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤ KW q := by
        intro q hq
        obtain ⟨hgi, hgb⟩ := hK_mos P hPball q hq
        have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
              fr ^ 2 * C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
          intro x
          have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
          rw [← hW_def, ← hfr_def] at h1
          have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
              ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 q
                    (slotInsertEndoCc (I := I) (M := M) g₀ 0
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
            _ ≤ fr ^ 2 * (C_base q *
                  (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                    ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
                mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
            _ = fr ^ 2 * C_base q *
                  (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                    ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
        have hint : MeasureTheory.Integrable
            (fun x => fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul, hKW_def]
        exact mul_le_mul_of_nonneg_left hgb (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
      have hstep3 : ∀ l : ℕ, l ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
            KD l := by
        intro l hl
        have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 1 l
                  (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
              (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
                (∑ q ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                    ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) := by
          intro x
          refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
            (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg _)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun i' _ => ?_)
          refine mul_le_mul (hSΦ i' x) ?_
            (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
          intro q hq
          rw [Finset.mem_range] at hq ⊢
          omega
        have hint : MeasureTheory.Integrable
            (fun x => (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          apply MeasureTheory.Integrable.const_mul
          apply MeasureTheory.integrable_finset_sum
          intro q _
          exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
          (iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum _ (fun q _ =>
            integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
              (iteratedCovGrad (I := I) g₀ 3 3 q W))]
        have hconv : ∀ q ∈ Finset.range (l + 1),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
            ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 := by
          intro q _
          rw [SmoothCcTensor.norm_def,
            tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (3 + q)
              (iteratedCovGrad (I := I) g₀ 3 3 q W)]
        rw [Finset.sum_congr rfl hconv]
        simp only [hKD_def]
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        simp only [hFW_def]
        exact Finset.sum_le_sum (fun q hq => hstep2 q (by rw [Finset.mem_range] at hq; omega))
      refine ⟨?_, ?_⟩
      · intro x
        have hΛT2_nn : 0 ≤ ΛT2 := by rw [hΛT2_def]; exact mul_nonneg (sq_nonneg fr) (hC_base_nn 0)
        rw [Real.sq_sqrt (by
          have := hSΦ_nn 0
          have := mul_nonneg (hSΦ_nn 0) hΛT2_nn
          linarith : (0 : ℝ) ≤ 2 * SΦ 0 + 2 * (SΦ 0 * ΛT2))]
        rw [hid, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 1 x
          (Φ.toSection x) ((appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x)) ?_
        have hΦ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (Φ.toSection x) ≤ SΦ 0 := by
          have h := hSΦ 0 x
          simp only [iteratedCovGrad_zero] at h
          exact h
        have hDIFF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x) ≤ SΦ 0 * ΛT2 := by
          refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 3 1 x
            (Φ.toSection x) (W.toSection x)) ?_
          exact mul_le_mul hΦ0 (hΛT x) (riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn 0)
        linarith
      · intro i hi
        simp only [hFf_def]
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl_a : l ≤ a + 1 := by rw [Finset.mem_range] at hl; omega
        rw [hid, iteratedCovGrad_add]
        have hKDl := hstep3 l hl_a
        have haLl : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
        have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
            iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)))
          (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
            (iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
        nlinarith [hsq, hKDl, haLl,
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
            ‖iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)‖)]
    · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
      refine ⟨fun x => (hem.false x).elim, ?_⟩
      intro i hi
      have hz : ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ = 0 := by
        intro l
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hsum0 : (∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [hz l]; ring
      rw [hsum0]
      exact hFnn i

private theorem exists_window_pointwise_jet_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Λw : ℝ, 0 ≤ Λw ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ j : ℕ, j ≤ 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤ Λw ^ 2 := by
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  refine ⟨Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R, by positivity, ?_⟩
  intro P hPball j hj x
  have hsum_le : ∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    calc ∑ i ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2
        ≤ ∑ _i ∈ Finset.range (a + 1 + 1), R ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ a + 2 := by have := Finset.mem_range.mp hi; omega
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hPball i hile, hR]
      _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hwin := hCemb P x
  have hjmem : j ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤
      ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) :=
    Finset.single_le_sum
      (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
      (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) hjmem
  have hLam2 : (Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R) ^ 2 =
      Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hLam2]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
      ≤ ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := hsingle
    _ ≤ Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := hwin
    _ ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring

set_option linter.unusedVariables false in
private theorem raisedKoszul_rfns_lowOrder_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
          Λ := by
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  refine ⟨10 * Λw ^ 2, by positivity, ?_⟩
  intro g₁ P htie hPball n hn x
  have hTjet : ∀ j : ℕ, j ≤ 1 + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
    fun j hj y => hΛw P hPball j (by omega) y
  have hkos := rfns_iteratedCovGrad_koszulCovecCc_le (I := I) (M := M) g₀ 1 P hTjet n hn x
  have heqr : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)).toSection x) := by
    rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) g₀ g₁ P htie]
    exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) g₀ P n x
  rw [heqr]
  exact hkos

private lemma gInvRaisedEndo_self' (g₀ : SmoothRiemannianMetric I M) (x : M) :
    gInvRaisedEndo (I := I) g₀ g₀ x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM, ContinuousLinearMap.id_apply]

private lemma fullRaisedEndoField_decomp' (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) =
      gInvDiffRaisedEndo (I := I) g₀ g₁ x from rfl]
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_self', ContinuousLinearMap.id_apply]
  rw [gInvRaisedEndo_eq_diff_add_id]

private lemma slotInsertEndoCc_add' (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

private lemma sharpFlatEndoCc_eq_insert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g₀ g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g₀ g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om (gInvRaisedEndo (I := I) g₀ g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (gInvRaisedEndo (I := I) g₀ g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (gInvRaisedEndo (I := I) g₀ g₁ x w)).symm]
  rw [show gInvRaisedEndo (I := I) g₀ g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w) from by
    rw [gInvRaisedEndo_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g₀.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

private lemma window_grid_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (n : ℕ) {Λw : ℝ}
    (hwin : ∀ j : ℕ, j ≤ n → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤ Λw ^ 2)
    (x : M) :
    (∑ m ∈ Finset.range (n + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ k : Fin m,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
      (∑ m ∈ Finset.range (n + 1),
        ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n := by
  have hmax1 : (1 : ℝ) ≤ max (Λw ^ 2) 1 := le_max_right _ _
  have hmax_nn : (0 : ℝ) ≤ max (Λw ^ 2) 1 := le_trans zero_le_one hmax1
  have hterm : ∀ m ∈ Finset.range (n + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple m n,
      (∏ k : Fin m,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
        max (Λw ^ 2) 1 ^ n := by
    intro m hm e he
    have hsum_e : ∑ k, e k = n := Finset.Nat.mem_antidiagonalTuple.mp he
    have hek_le : ∀ k : Fin m, e k ≤ n := by
      intro k
      rw [← hsum_e]
      exact Finset.single_le_sum (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
    have hprod1 : (∏ k : Fin m,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
        ∏ _k : Fin m, max (Λw ^ 2) 1 := by
      apply Finset.prod_le_prod
      · intro k _
        exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e k) x _
      · intro k _
        exact le_trans (hwin (e k) (hek_le k) x) (le_max_left _ _)
    have hm_le : m ≤ n := by have := Finset.mem_range.mp hm; omega
    calc (∏ k : Fin m,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x))
        ≤ ∏ _k : Fin m, max (Λw ^ 2) 1 := hprod1
      _ = max (Λw ^ 2) 1 ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ max (Λw ^ 2) 1 ^ n := pow_le_pow_right₀ hmax1 hm_le
  calc (∑ m ∈ Finset.range (n + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
          ∏ k : Fin m,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x))
      ≤ ∑ m ∈ Finset.range (n + 1),
          ∑ _e ∈ Finset.Nat.antidiagonalTuple m n, max (Λw ^ 2) 1 ^ n := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro e he
        exact hterm m hm e he
    _ = (∑ m ∈ Finset.range (n + 1),
          ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_const, nsmul_eq_mul]

set_option linter.unusedVariables false in
private theorem sharpFlatEndoCc_lowOrder_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_mos, hK_mos_nn, hK_mos⟩ :=
    diagonalProductGrid_rfns_integral_ballUniform_succ (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  have hSId_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 (1 + n)
      (iteratedCovGrad (I := I) g₀ 1 1 n IdIns)
  choose SId hSId_nn hSId using hSId_ex
  set Gw : ℕ → ℝ := fun n => (∑ m ∈ Finset.range (n + 1),
    ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n with hGw_def
  have hGw_nn : ∀ n, 0 ≤ Gw n := by
    intro n
    rw [hGw_def]
    apply mul_nonneg (Finset.sum_nonneg (fun m _ => Nat.cast_nonneg _))
    apply pow_nonneg
    exact le_trans zero_le_one (le_max_right _ _)
  set FId : ℕ → ℝ := fun q => ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 with hFId_def
  have hFId_nn : ∀ q, 0 ≤ FId q := fun q => sq_nonneg _
  refine ⟨fun n => 2 * (C_base n * Gw n) + 2 * SId n,
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * (C_base q * K_mos q) + 2 * FId q),
    fun n => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hC_base_nn n) (hGw_nn n)))
      (mul_nonneg (by norm_num) (hSId_nn n)),
    fun i => Finset.sum_nonneg (fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hC_base_nn q) (hK_mos_nn q)))
      (mul_nonneg (by norm_num) (hFId_nn q))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [sharpFlatEndoCc_eq_insert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_decomp' (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add' (I := I) (M := M) g₀ 0]
  have hDiff_pt : ∀ n : ℕ, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤
      C_base n * ∑ m ∈ Finset.range (n + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
          ∏ k : Fin m,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x) :=
    fun n x => hC_base g₁ P htie hδ_le hδ0 hδ n x
  refine ⟨?_, ?_⟩
  · intro n hn x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) := by
      rw [hdecomp, iteratedCovGrad_add]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns +
            iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + n) x _ _
    have hwin_n : ∀ j : ℕ, j ≤ n → ∀ y : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
      fun j hj y => hΛw P hPball j (by omega) y
    have hgrid := window_grid_le (I := I) (M := M) g₀ P n hwin_n x
    have hDn : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤ C_base n * Gw n :=
      le_trans (hDiff_pt n x) (by
        rw [hGw_def]
        exact mul_le_mul_of_nonneg_left hgrid (hC_base_nn n))
    have hIn := hSId n x
    linarith [hsplit, hDn, hIn]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
          2 * (C_base q * K_mos q) + 2 * FId q := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      obtain ⟨hgi, hgb⟩ := hK_mos P hPball q hq_le
      have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ C_base q * K_mos q := by
        have hint : MeasureTheory.Integrable
            (fun x => C_base q *
              (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
                ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
          1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint (fun x => hDiff_pt q x)
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul]
        exact mul_le_mul_of_nonneg_left hgb (hC_base_nn q)
      have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
            ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
        rw [hdecomp, iteratedCovGrad_add]
        exact norm_add_le _ _
      have hFIdq : FId q = ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := rfl
      nlinarith [htri, hDq, hFIdq.ge,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]
    exact Finset.sum_le_sum hterm

set_option linter.unusedVariables false in
private theorem connDiffSection_lowOrder_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛKlow, hΛKlow_nn, hKlow⟩ :=
    raisedKoszul_rfns_lowOrder_le (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨ΛS, FS, hΛS_nn, hFS_nn, hS⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨fun n => appCcGdiag (E := E) n *
      ((∑ i ∈ Finset.range (n + 1), ΛKlow) * (∑ l ∈ Finset.range (n + 1), ΛS l)),
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (CT q * (ΛS 0 * FK q + ΛK ^ 2 * FS q)),
    fun n => by
      apply mul_nonneg (appCcGdiag_nonneg (E := E) n)
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => hΛKlow_nn)
        (Finset.sum_nonneg fun l _ => hΛS_nn l),
    fun i => Finset.sum_nonneg fun q _ => by
      apply mul_nonneg (appCcGdiag_nonneg (E := E) q)
      apply mul_nonneg (hCT_nn q)
      exact add_nonneg (mul_nonneg (hΛS_nn 0) (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFS_nn q)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hSlow, hSsum⟩ := hS g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro n hn x
    rw [hid]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ n 1 1 2 (raisedKoszul (I := I) g₀ g₁)
      (sharpFlatEndoCc (I := I) g₀ g₁) x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) n)
    have hKn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 1 2 i' (raisedKoszul (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        ΛKlow * ∑ l ∈ Finset.range (n + 1), ΛS l := by
      intro i' hi'
      have hi'n : i' ≤ n := by have := Finset.mem_range.mp hi'; omega
      have hKfac := hKlow g₁ P htie hPball i' (by omega) x
      have hSfac : (∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
          ∑ l ∈ Finset.range (n + 1), ΛS l := by
        calc (∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
            ≤ ∑ l ∈ Finset.range (n + 1 - i'), ΛS l :=
              Finset.sum_le_sum (fun l hl => hSlow l (by
                have := Finset.mem_range.mp hl; omega) x)
          _ ≤ ∑ l ∈ Finset.range (n + 1), ΛS l :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun z hz => Finset.mem_range.mpr
                  (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
                (fun l _ _ => hΛS_nn l)
      exact mul_le_mul hKfac hSfac
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        hΛKlow_nn
    refine le_trans (Finset.sum_le_sum hKn) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          appCcGdiag (E := E) q * (CT q * (ΛS 0 * FK q + ΛK ^ 2 * FS q)) := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
          ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛS 0)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (hΛS_nn 0)]
        have h := hSlow 0 (by omega) x
        simpa only [iteratedCovGrad_zero] using h
      have hKs : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤ ΛK ^ 2 := hKsup
      obtain ⟨hgrid_int, hgrid_bound⟩ := hCT q (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) ΛK (Real.sqrt (ΛS 0)) hΛK_nn
        (Real.sqrt_nonneg _) hKs hS0
      rw [hid]
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (2 + q)
        (iteratedCovGrad (I := I) g₀ 1 2 q
          (appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
            (sharpFlatEndoCc (I := I) g₀ g₁)))
        (fun x => appCcGdiag (E := E) q *
          ∑ n ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (q + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l
                      (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
        (hgrid_int.const_mul (appCcGdiag (E := E) q))
        (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ q 1 1 2 (raisedKoszul (I := I) g₀ g₁)
          (sharpFlatEndoCc (I := I) g₀ g₁) x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
      refine le_trans hgrid_bound ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCT_nn q)
      have h1 : (Real.sqrt (ΛS 0)) ^ 2 = ΛS 0 := Real.sq_sqrt (hΛS_nn 0)
      rw [h1]
      have hKsq := hKsum q hq_le
      have hSsq := hSsum q hq_le
      have e1 : ΛS 0 * (∑ n ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛS 0 * FK q := mul_le_mul_of_nonneg_left hKsq (hΛS_nn 0)
      have e2 : ΛK ^ 2 * (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛK ^ 2 * FS q := mul_le_mul_of_nonneg_left hSsq (sq_nonneg ΛK)
      linarith [e1, e2]
    exact Finset.sum_le_sum hterm

private lemma connDiffSection_eq_cometricRaiseSlot0Field' (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [connDiffLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

private lemma rfns_iCG_connDiffLoweredCc_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [connDiffSection_eq_cometricRaiseSlot0Field']

private lemma norm_iCG_connDiffLoweredCc_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x

private lemma riemannianFiberNormSq_neg_local'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedVariables false in
private theorem wXi_lowOrder_jetL2_succ_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
              F i) := by
  classical
  obtain ⟨ΛC, FC, hΛC_nn, hFC_nn, hC⟩ :=
    connDiffSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hSBg_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) ≤
        K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (3 + n)
      (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg))
  choose SBg hSBg_nn hSBg using hSBg_ex
  set FBg : ℕ → ℝ :=
    fun q => ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g_bg)‖ ^ 2
    with hFBg_def
  have hFBg_nn : ∀ q, 0 ≤ FBg q := fun q => sq_nonneg _
  refine ⟨fun n => 2 * ΛC n + 2 * SBg n,
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * FC i + 2 * FBg q),
    fun n => add_nonneg (mul_nonneg (by norm_num) (hΛC_nn n))
      (mul_nonneg (by norm_num) (hSBg_nn n)),
    fun i => Finset.sum_nonneg (fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (hFC_nn i)) (mul_nonneg (by norm_num) (hFBg_nn q))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hClow, hCsum⟩ := hC g₁ P htie hδ_le hδ0 hδ hPball
  refine ⟨?_, ?_⟩
  · intro n hn x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) := by
      rw [wXi, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁) -
            iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x +
            -((iteratedCovGrad (I := I) g₀ 0 3 n
              (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) from by
        rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
          sub_eq_add_neg]]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + n) x _ _) ?_
      rw [riemannianFiberNormSq_neg_local']
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) ≤
        ΛC n := by
      rw [rfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x]
      exact hClow n hn x
    linarith [hsplit, h1, hSBg n x]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          2 * FC i + 2 * FBg q := by
      intro q hq
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤
          FC i := by
        rw [norm_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ q]
        refine le_trans ?_ (hCsum i hi)
        exact Finset.single_le_sum
          (f := fun q' => ‖iteratedCovGrad (I := I) g₀ 1 2 q'
            (connDiffSection (I := I) g₁ g₀)‖ ^ 2)
          (fun q' _ => sq_nonneg _) hq
      have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 q (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g_bg)‖ := by
        rw [wXi, iteratedCovGrad_sub]
        exact norm_sub_le _ _
      have hFBgq : FBg q =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g_bg)‖ ^ 2 := rfl
      nlinarith [htri, h1, hFBgq.ge,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g_bg)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (wXi (I := I) (M := M) g₀ g₁ g_bg)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g_bg)‖)]
    exact Finset.sum_le_sum hterm

set_option linter.unusedVariables false in
private theorem cometricCastG0_rfns_lowOrder_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 1 n
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤ Λ n := by
  classical
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  have hSΦ_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + n)
      (iteratedCovGrad (I := I) g₀ 3 1 n Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set Gw : ℕ → ℝ := fun n => (∑ m ∈ Finset.range (n + 1),
    ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n with hGw_def
  have hGw_nn : ∀ n, 0 ≤ Gw n := by
    intro n
    rw [hGw_def]
    apply mul_nonneg (Finset.sum_nonneg (fun m _ => Nat.cast_nonneg _))
    apply pow_nonneg
    exact le_trans zero_le_one (le_max_right _ _)
  refine ⟨fun n => 2 * SΦ n + 2 * (appCcGdiag (E := E) n *
      ((∑ i' ∈ Finset.range (n + 1), SΦ i') *
        (∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l)))),
    fun n => add_nonneg (mul_nonneg (by norm_num) (hSΦ_nn n))
      (mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) n)
        (mul_nonneg (Finset.sum_nonneg fun i' _ => hSΦ_nn i')
          (Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg fr)
            (mul_nonneg (hC_base_nn l) (hGw_nn l)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn x
  set W33 : SmoothCcTensor g₀ 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hW33_def
  have hwin_n : ∀ j : ℕ, j ≤ n → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
    fun j hj y => hΛw P hPball j (by omega) y
  have hW33_pt : ∀ l : ℕ, l ≤ n → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
        ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection y) ≤
      fr ^ 2 * (C_base l * Gw l) := by
    intro l hl y
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) l y
    rw [← hW33_def, ← hfr_def] at h1
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ l y
    have hwin_l : ∀ j : ℕ, j ≤ l → ∀ z : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) z
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection z) ≤ Λw ^ 2 :=
      fun j hj z => hwin_n j (by omega) z
    have hgrid := window_grid_le (I := I) (M := M) g₀ P l hwin_l y
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection y)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ 2 * (C_base l *
            (∑ m ∈ Finset.range (l + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m l,
              ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) y
                ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection y))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
      _ ≤ fr ^ 2 * (C_base l * Gw l) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg fr)
          rw [hGw_def]
          exact mul_le_mul_of_nonneg_left hgrid (hC_base_nn l)
  have hid : cometricCastG0 (I := I) g₀ g₁ =
      Φ + appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W33 := by
    have h := cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
    rw [← hΦ_def, ← hW33_def] at h
    exact h
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 1 n (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 1 n
            (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) := by
    rw [hid, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 3 1 n Φ +
          iteratedCovGrad (I := I) g₀ 3 1 n
            (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x +
          (iteratedCovGrad (I := I) g₀ 3 1 n
            (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (1 + n) x _ _
  have happ : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 1 n
        (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) ≤
      appCcGdiag (E := E) n *
        ((∑ i' ∈ Finset.range (n + 1), SΦ i') *
          (∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l))) := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ n 3 3 1 Φ W33 x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) n)
    have hkn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' Φ).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection x) ≤
        SΦ i' * ∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l) := by
      intro i' hi'
      refine mul_le_mul (hSΦ i' x) ?_
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn i')
      calc (∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection x))
          ≤ ∑ l ∈ Finset.range (n + 1 - i'), fr ^ 2 * (C_base l * Gw l) :=
            Finset.sum_le_sum (fun l hl => hW33_pt l (by
              have := Finset.mem_range.mp hl; omega) x)
        _ ≤ ∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun z hz => Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
              (fun l _ _ => mul_nonneg (sq_nonneg fr)
                (mul_nonneg (hC_base_nn l) (hGw_nn l)))
    refine le_trans (Finset.sum_le_sum hkn) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hΦn := hSΦ n x
  linarith [hsplit, happ, hΦn]

set_option linter.unusedVariables false in
private theorem wOmega_lowOrder_jetL2_succ_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 1 n
              (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 1 q (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
              F i) := by
  classical
  obtain ⟨ΛCsup, FC, hΛCsup_nn, hFC_nn, hCgen⟩ :=
    cometricCastG0_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛClow, hΛClow_nn, hClow⟩ :=
    cometricCastG0_rfns_lowOrder_le (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛX, FX, hΛX_nn, hFX_nn, hXgen⟩ :=
    wXi_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 3 1) (T : SmoothCcTensor g₀ 0 3)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 1 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 3 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 3 0 1 3 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨fun n => appCcGdiag (E := E) n *
      ((∑ i' ∈ Finset.range (n + 1), ΛClow i') * (∑ l ∈ Finset.range (n + 1), ΛX l)),
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (CT q * (ΛX 0 * FC q + ΛCsup ^ 2 * FX q)),
    fun n => mul_nonneg (appCcGdiag_nonneg (E := E) n)
      (mul_nonneg (Finset.sum_nonneg fun i' _ => hΛClow_nn i')
        (Finset.sum_nonneg fun l _ => hΛX_nn l)),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hCT_nn q) (add_nonneg (mul_nonneg (hΛX_nn 0) (hFC_nn q))
        (mul_nonneg (sq_nonneg _) (hFX_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hCsup, hCsum⟩ := hCgen g₁ P hδ_le hδ htie hPball
  obtain ⟨hXlow, hXsum⟩ := hXgen g₁ P htie hδ_le hδ0 hδ hPball
  have hform : wOmega (I := I) (M := M) g₀ g₁ g_bg =
      appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (wXi (I := I) (M := M) g₀ g₁ g_bg) := rfl
  refine ⟨?_, ?_⟩
  · intro n hn x
    rw [hform]
    refine le_trans (appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
      (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) n)
    have hkn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l
                  (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        ΛClow i' * ∑ l ∈ Finset.range (n + 1), ΛX l := by
      intro i' hi'
      have hi'n : i' ≤ n := by have := Finset.mem_range.mp hi'; omega
      refine mul_le_mul (hClow g₁ P htie hδ_le hδ0 hδ hPball i' (by omega) x) ?_
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _) (hΛClow_nn i')
      calc (∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
          ≤ ∑ l ∈ Finset.range (n + 1 - i'), ΛX l :=
            Finset.sum_le_sum (fun l hl => hXlow l (by
              have := Finset.mem_range.mp hl; omega) x)
        _ ≤ ∑ l ∈ Finset.range (n + 1), ΛX l :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun z hz => Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
              (fun l _ _ => hΛX_nn l)
    refine le_trans (Finset.sum_le_sum hkn) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 q (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          appCcGdiag (E := E) q * (CT q * (ΛX 0 * FC q + ΛCsup ^ 2 * FX q)) := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      have hX0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((wXi (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛX 0)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (hΛX_nn 0)]
        have h := hXlow 0 (by omega) x
        simpa only [iteratedCovGrad_zero] using h
      obtain ⟨hgrid_int, hgrid_bound⟩ := hCT q (cometricCastG0 (I := I) g₀ g₁)
        (wXi (I := I) (M := M) g₀ g₁ g_bg) ΛCsup (Real.sqrt (ΛX 0)) hΛCsup_nn
        (Real.sqrt_nonneg _) hCsup hX0
      rw [hform]
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        0 (1 + q)
        (iteratedCovGrad (I := I) g₀ 0 1 q
          (appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
            (wXi (I := I) (M := M) g₀ g₁ g_bg)))
        (fun x => appCcGdiag (E := E) q *
          ∑ n ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
                ((iteratedCovGrad (I := I) g₀ 3 1 n
                  (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (q + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        (hgrid_int.const_mul (appCcGdiag (E := E) q))
        (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
      refine le_trans hgrid_bound ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCT_nn q)
      have h1 : (Real.sqrt (ΛX 0)) ^ 2 = ΛX 0 := Real.sq_sqrt (hΛX_nn 0)
      rw [h1]
      have e1 : ΛX 0 * (∑ n ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 n (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛX 0 * FC q := mul_le_mul_of_nonneg_left (hCsum q hq_le) (hΛX_nn 0)
      have e2 : ΛCsup ^ 2 * (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 l (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
          ΛCsup ^ 2 * FX q := mul_le_mul_of_nonneg_left (hXsum q hq_le) (sq_nonneg ΛCsup)
      linarith [e1, e2]
    exact Finset.sum_le_sum hterm

private lemma rfns_iCG_wCA_eq_connDiffSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) := by
        rw [wCA]
        exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (Equiv.swap (1 : Fin 3) 2) (connDiffLoweredCc (I := I) g₀ g₁) n x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) :=
        rfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x

private lemma norm_iCG_wCA_eq_connDiffSection (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x

private lemma rfns_iCG_wAlphaA_eq_succ_wOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i
            (covGrad (I := I) (M := M) g₀ 0 1
              (wOmega (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
        rw [wAlphaA]
        exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (Equiv.swap (0 : Fin 2) 1)
          (covGrad (I := I) (M := M) g₀ 0 1 (wOmega (I := I) (M := M) g₀ g₁ g_bg)) i x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
            (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
          (wOmega (I := I) (M := M) g₀ g₁ g_bg) x

private lemma norm_iCG_wAlphaA_eq_succ_wOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 1 (i + 1) (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iCG_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg i x

set_option linter.unusedVariables false in
private theorem wAlpha_order0_jetL2_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ0 : ℝ) (F : ℕ → ℝ), 0 ≤ Λ0 ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((wAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ0) ∧
        (∀ i : ℕ, i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F i) := by
  classical
  obtain ⟨ΛO, FO, hΛO_nn, hFO_nn, hOgen⟩ :=
    wOmega_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛCd, FCd, hΛCd_nn, hFCd_nn, hCdgen⟩ :=
    connDiffSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 0 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 0 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * ΛO 1 + 2 * (appCcGdiag (E := E) 0 * (ΛCd 0 * ΛO 0)),
    fun i => 2 * FO (i + 1) +
      2 * (appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i))),
    add_nonneg (mul_nonneg (by norm_num) (hΛO_nn 1))
      (mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) 0)
        (mul_nonneg (hΛCd_nn 0) (hΛO_nn 0)))),
    fun i => add_nonneg (mul_nonneg (by norm_num) (hFO_nn (i + 1)))
      (mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hCT_nn i) (add_nonneg (mul_nonneg (hΛO_nn 0) (hFCd_nn i))
          (mul_nonneg (hΛCd_nn 0) (hFO_nn i)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hOlow, hOsum⟩ := hOgen g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hCdlow, hCdsum⟩ := hCdgen g₁ P htie hδ_le hδ0 hδ hPball
  have hwCAlow : ∀ n : ℕ, n ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ΛCd n := by
    intro n hn x
    rw [rfns_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x]
    exact hCdlow n hn x
  have hwCAsum : ∀ i : ℕ, i ≤ a + 1 →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ FCd i := by
    intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q _ => ?_))) (hCdsum i hi)
    rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ q]
  have hBform : wAlphaB (I := I) (M := M) g₀ g₁ g_bg =
      appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  have hBlow : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlphaB (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      appCcGdiag (E := E) 0 * (ΛCd 0 * ΛO 0) := by
    intro x
    have hg := appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
      (wCA (I := I) (M := M) g₀ g₁) (wOmega (I := I) (M := M) g₀ g₁ g_bg) 0 x
    have hgoal : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlphaB (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 2 0
            (appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
              (wOmega (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
      rw [hBform, iteratedCovGrad_zero]
    rw [hgoal]
    refine le_trans hg ?_
    have hsum0 : (∑ i ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (wCA (I := I) (M := M) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (0 + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 1 l
                  (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
        ΛCd 0 * ΛO 0 := by
      rw [Finset.sum_range_one, Finset.sum_range_one]
      exact mul_le_mul (hwCAlow 0 (by omega) x) (hOlow 0 (by omega) x)
        (riemannianFiberNormSq_nonneg _ _ _ _ _) (hΛCd_nn 0)
    exact mul_le_mul_of_nonneg_left hsum0 (appCcGdiag_nonneg (E := E) 0)
  have hBsum : ∀ i : ℕ, i ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i)) := by
    intro i hi
    have hO0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
        ((wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛO 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛO_nn 0)]
      have h := hOlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    have hCA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((wCA (I := I) (M := M) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛCd 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛCd_nn 0)]
      have h := hwCAlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    obtain ⟨hgrid_int, hgrid_bound⟩ := hCT i (wCA (I := I) (M := M) g₀ g₁)
      (wOmega (I := I) (M := M) g₀ g₁ g_bg) (Real.sqrt (ΛCd 0)) (Real.sqrt (ΛO 0))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCA0 hO0
    rw [hBform]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i
        (appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)))
      (fun x => appCcGdiag (E := E) i *
        ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 1 l
                    (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (hgrid_int.const_mul (appCcGdiag (E := E) i))
      (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
        (wCA (I := I) (M := M) g₀ g₁) (wOmega (I := I) (M := M) g₀ g₁ g_bg) i x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine le_trans hgrid_bound ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn i)
    rw [Real.sq_sqrt (hΛO_nn 0), Real.sq_sqrt (hΛCd_nn 0)]
    have e1 : ΛO 0 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
        ΛO 0 * FCd i := mul_le_mul_of_nonneg_left (hwCAsum i (by omega)) (hΛO_nn 0)
    have e2 : ΛCd 0 * (∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 l (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCd 0 * FO i := mul_le_mul_of_nonneg_left (hOsum i (by omega)) (hΛCd_nn 0)
    linarith [e1, e2]
  refine ⟨?_, ?_⟩
  · intro x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlphaA (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ ΛO 1 := by
      have h := rfns_iCG_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg 0 x
      have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((wAlphaA (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
        rw [iteratedCovGrad_zero]
      rw [h0, h]
      exact hOlow 1 (by omega) x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((wAlphaA (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((wAlphaB (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
      rw [wAlpha]
      rw [show ((wAlphaA (I := I) (M := M) g₀ g₁ g_bg +
            wAlphaB (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg).toSection x +
            (wAlphaB (I := I) (M := M) g₀ g₁ g_bg).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x _ _
    linarith [hsplit, hA0, hBlow x]
  · intro i hi
    have hAi : ‖iteratedCovGrad (I := I) g₀ 0 2 i
        (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ FO (i + 1) := by
      rw [norm_iCG_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg i]
      refine le_trans ?_ (hOsum (i + 1) (by omega))
      exact Finset.single_le_sum
        (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 1 q
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    have hBi := hBsum i hi
    have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ := by
      rw [wAlpha, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hAi, hBi,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ -
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖)]

private lemma rfns_iCG_wEndoInsert_eq_wAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  rw [deTurckLieWEndoInsert_eq_cometricRaise (I := I) (M := M) g₀ g₁ g_bg]
  exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (wAlpha (I := I) (M := M) g₀ g₁ g_bg) i x

private lemma norm_iCG_wEndoInsert_eq_wAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀ g₁ g_bg i x

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem deTurckLieWEndoInsert_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
              ((deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λ0, F, hΛ0_nn, hF_nn, hgen⟩ :=
    wAlpha_order0_jetL2_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Λ0, hΛ0_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x) := by
          have heq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
          rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x v v := g₀.pos x v hv
    have hbound := hδP x v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
        (convexPerturbation (I := I) g₀ T T' s) x v v| := abs_nonneg _
    by_contra hδc
    have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
    have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) *
        Real.sqrt (g₀.inner x v v) < 0 := by
      have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) < 0 :=
        mul_neg_of_neg_of_pos hδc' hsqrt_pos
      exact mul_neg_of_neg_of_pos h1 hsqrt_pos
    linarith [le_trans habs_nn hbound]
  have htr := rfns_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg 0 x
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 1 0
          (deTurckLieWEndoInsert (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) := by
    rw [iteratedCovGrad_zero]
  rw [h0, htr]
  have hval := (hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball).1 x
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
      ((iteratedCovGrad (I := I) g₀ 0 2 0
        (wAlpha (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlpha (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) := by
    rw [iteratedCovGrad_zero]
  rw [h1]
  exact hval

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨Λ0, F, hΛ0_nn, hF_nn, hgen⟩ :=
    wAlpha_order0_jetL2_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨F, hF_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
      linarith [e1, e2, e3]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
          (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδP x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
          (convexPerturbation (I := I) g₀ T T' s) x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) *
          Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    rw [norm_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i]
    exact (hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball).2 i hi
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckLieWEndoInsert (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have := hF_nn i
    nlinarith [hF_nn i]

/-! ### DLb top-separated tower (insert-level producer)

Top-separated `realizedFam` jetL2 producer for `deTurckLieWEndoInsert`, the DLb sibling of the DLa
kernel top separation.  The top order `∇^{i+2}T` enters only through `wAlphaA = ∇^{i+1}wOmega`; the
remainder currency is `antidiagonalTupleGridWindow` (integrated by the tame-window integrator).  See
`DeTurckVectorFieldL2JetBound.md`. -/
section DLbTopSeparated

/-- Pure `Finset` window-shift helper (copied verbatim from the sibling top-separated files). -/
private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

/-- Summation of a per-order top-separated jet bound with independent top offset `p` and low-window
offset `q` (copied from the sibling top-separated files). -/
private lemma jetL2_sum_lowShift
    (a p q : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ Ktop * w (i + p) + Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), Ktop * w (i + p)) ≤
      Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) hKtop
  have hA : (∑ i ∈ Finset.range (a + 1), Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) ≤
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_le_mul_of_nonneg_left ?_ (hKc i)
    have hsub : Finset.range (i + q) ⊆ Finset.range (a + q) := by
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]

/-- Reshape the connDiffSection top-separated engine remainder
`∑_{k<j} b(j-k)·antidiagonalTupleGrid b (k+1)` into `Cj·antidiagonalTupleGridWindow b (j+2)`
(public-grid analogue of the DLa `engineRem_le_dLaGridWin`). -/
private lemma engineRem_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j,
        b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hg_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
  have h1 : b (j - k) ≤ Combinatorics.antidiagonalTupleGrid b (j - k) := by
    have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (j - k) (by omega)
    rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one, Nat.zero_add] at hsf
  have h2 : Combinatorics.antidiagonalTupleGrid b (j - k) *
      Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (Combinatorics.antidiagonalTupleGridCount (j - k) *
        Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) :=
    Combinatorics.antidiagonalTupleGrid_mul_le b hb (j - k) (k + 1)
  have h3 : Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) ≤
      Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by
    rw [show (j - k) + (k + 1) = j + 1 from by omega]
    exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
  calc b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ Combinatorics.antidiagonalTupleGrid b (j - k) *
          Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        mul_le_mul_of_nonneg_right h1 hg_nn
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) := h2
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2) :=
        mul_le_mul_of_nonneg_left h3
          (mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _)
            (Combinatorics.antidiagonalTupleGridCount_nonneg _))

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **connDiffSection top-separated jet bound in `antidiagonalTupleGridWindow` currency.**  Top
coefficient `Ktop = 2·Kt0` (`R`-independent engine head); remainder is a single grid window (house
`R`-pattern).  Public-grid re-derivation of the DLa `exists_rfns_connDiffSection_topsep_dla`. -/
private theorem exists_rfns_connDiff_topsep
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) +
          Kc j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn,
    fun j => 2 * Kc0 j * (∑ k ∈ Finset.range j,
      Combinatorics.antidiagonalTupleGridCount (j - k) *
        Combinatorics.antidiagonalTupleGridCount (k + 1)),
    fun j => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn j))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _)
          (Combinatorics.antidiagonalTupleGridCount_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have heng := hbot g₁ P htie hδ_le hδ0 hbound j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) := heng.1
  have hrem := heng.2
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) := by
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
      (Hd.toSection x)
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x)
    have key :
        (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x =
          Hd.toSection x +
            (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x := by
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      abel
    rw [key]
    exact hadd
  have hrem2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 j * ((∑ k ∈ Finset.range j,
        Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 2)) :=
    le_trans hrem (mul_le_mul_of_nonneg_left (engineRem_le_grid b hb j) (hKc0_nn j))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x) := hsplit
    _ ≤ 2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x)) +
        2 * (Kc0 j * ((∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2))) := by
          linarith [hhead, hrem2]
    _ = (2 * Kt0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) +
        (2 * Kc0 j * (∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1))) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **connDiffSection L2 top-separated bound.**  Integrates `exists_rfns_connDiff_topsep`: the top
`‖∇^{n+1}P‖²` stays separated with the `R`-free coefficient `Ktop = 2·Kt0`; the grid-window remainder
integrates to a ball-uniform per-order constant `C n` (absorbed into `Kc·1` downstream via the
tame-window integrator + the `hPball` conversion `∑_{j≤k}‖∇^jP‖² ≤ (k+1)R²`). -/
private theorem connDiff_L2_topsep
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_pt, hKtop_pt_nn, Kc_pt, hKc_pt_nn, hpt⟩ :=
    exists_rfns_connDiff_topsep (I := I) (M := M) g₀ hδ₀
  obtain ⟨K, hK_nn, hKint⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Ktop_pt, hKtop_pt_nn,
    fun n => Kc_pt n * ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2),
    fun n => mul_nonneg (hKc_pt_nn n)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hK_nn k) (by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  -- per-index grid integrability + ball-uniform integral bound (via tame-window integrator)
  have hAG : ∀ k : ℕ, k ≤ a + 2 →
      MeasureTheory.Integrable (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
    intro k hk
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ m ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m k,
            ∏ i : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e i) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]
    obtain ⟨hint, hbd⟩ := hKint P hPball k
    refine ⟨hint, le_trans hbd ?_⟩
    have hsum : (∑ j ∈ Finset.range (k + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ ((k : ℝ) + 1) * R ^ 2 := by
      calc ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ ∑ j ∈ Finset.range (k + 1), R ^ 2 := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjk : j ≤ a + 2 :=
              le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hk
            have hb := hPball j hjk
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hb, hR]
        _ = ((k : ℝ) + 1) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by linarith [hsum]) (hK_nn k)
  -- window integrability + integral bound
  have hwin_int : MeasureTheory.Integrable (fun x => Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    refine MeasureTheory.integrable_finset_sum _ (fun k hk => (hAG k ?_).1)
    have := Finset.mem_range.mp hk; omega
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k hk => (hAG k (by
      have := Finset.mem_range.mp hk; omega)).1)]
    refine Finset.sum_le_sum (fun k hk => (hAG k ?_).2)
    have := Finset.mem_range.mp hk; omega
  -- top integrability
  have htop_int : MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P)
  -- pointwise top-separated bound, integrated
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀))
    (fun x => Ktop_pt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
      + Kc_pt n * Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
    ((htop_int.const_mul Ktop_pt).add (hwin_int.const_mul (Kc_pt n)))
    (fun x => hpt g₁ P htie hδ_le hδ0 hδ n x)
  rw [MeasureTheory.integral_add (htop_int.const_mul Ktop_pt) (hwin_int.const_mul (Kc_pt n)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hnormsq : ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  calc ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2
      ≤ Ktop_pt * (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hnormsq]
    _ ≤ Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hwin_bd (hKc_pt_nn n)
        linarith [hmul]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wXi L2 top-separated bound.**  `wXi = connDiffLoweredCc g₁ − connDiffLoweredCc g_bg`; the
`g₁` part carries the top `‖∇^{n+1}P‖²` (via `connDiff_L2_topsep`), the `g_bg` part is a `T`-free
constant folded into `C n`.  `Ktop = 2·(connDiff Ktop)`, `R`-free. -/
private theorem wXi_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_cd, hKtop_cd_nn, C_cd, hC_cd_nn, hcd⟩ :=
    connDiff_L2_topsep (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨2 * Ktop_cd, mul_nonneg (by norm_num) hKtop_cd_nn,
    fun n => 2 * C_cd n +
      2 * ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖ ^ 2,
    fun n => add_nonneg (mul_nonneg (by norm_num) (hC_cd_nn n))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  have hA : ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤
      Ktop_cd * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C_cd n := by
    rw [norm_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ n]
    exact hcd g₁ P htie hδ_le hδ0 hδ hPball n hn
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖ := by
    rw [wXi, iteratedCovGrad_sub]
    exact norm_sub_le _ _
  nlinarith [htri, hA,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wOmega L2 top-separated bound** (genuine corner peel).  `wOmega = appCc cometricCastG0 wXi`;
the argCorner Leibniz decomposition isolates the corner `appCcRS ψ_{n,n} (∇ⁿwXi)` — whose
coefficient fiber norm is the `R`-free order-`0` bound `ΛClow 0` (`rfns_appCcRS_appCcLeibnizPsi_diag_le`
carries no `appCcGdiag`), feeding `wXi_L2_topsep` for the top `‖∇^{n+1}P‖²` — from a top-free lower
sum bounded ball-uniformly by the two-arm grid integrator.  `Ktop = 2·ΛClow 0·Ktop_xi`, `R`-free. -/
private theorem wOmega_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_xi, hKtop_xi_nn, Cxi, hCxi_nn, hxi⟩ :=
    wXi_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛClow, hΛClow_nn, hClow⟩ :=
    cometricCastG0_rfns_lowOrder_le (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛCsup, FC, hΛCsup_nn, hFC_nn, hCgen⟩ :=
    cometricCastG0_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛX, FX, hΛX_nn, hFX_nn, hXgen⟩ :=
    wXi_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 3 1) (T : SmoothCcTensor g₀ 0 3)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 1 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 3 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 3 0 1 3 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * ΛClow 0 * Ktop_xi,
    mul_nonneg (mul_nonneg (by norm_num) (hΛClow_nn 0)) hKtop_xi_nn,
    fun n => 2 * ΛClow 0 * Cxi n +
      2 * ((n : ℝ) * appCcGdiag (E := E) n) *
        (CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n)),
    fun n => add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (hΛClow_nn 0)) (hCxi_nn n))
      (mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n)))
        (mul_nonneg (hCT_nn n) (add_nonneg (mul_nonneg (hΛX_nn 0) (hFC_nn n))
          (mul_nonneg (sq_nonneg _) (hFX_nn n))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨hCsup, hCsum⟩ := hCgen g₁ P hδ_le hδ htie hPball
  obtain ⟨hXlow, hXsum⟩ := hXgen g₁ P htie hδ_le hδ0 hδ hPball
  -- uniform `R`-free order-0 fiber bound on `cometricCastG0`
  have hc0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ ΛClow 0 := by
    intro x
    have h := hClow g₁ P htie hδ_le hδ0 hδ hPball 0 (by norm_num) x
    simpa only [iteratedCovGrad_zero] using h
  -- order-0 sup bound on `wXi` (`√(ΛX 0)`)
  have hX0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((wXi (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛX 0)) ^ 2 := by
    intro x
    rw [Real.sq_sqrt (hΛX_nn 0)]
    have h := hXlow 0 (by norm_num) x
    simpa only [iteratedCovGrad_zero] using h
  -- integrability of the two arms of the pointwise envelope
  have hwxi_int : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + n)
      (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg))
  obtain ⟨htri_int, htri_bd⟩ := hCT n (cometricCastG0 (I := I) g₀ g₁)
    (wXi (I := I) (M := M) g₀ g₁ g_bg) ΛCsup (Real.sqrt (ΛX 0)) hΛCsup_nn (Real.sqrt_nonneg _)
    hCsup hX0
  -- `wOmega = appCcRS 0 (cometricCastG0) (wXi)`
  have hwform : wOmega (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (wXi (I := I) (M := M) g₀ g₁ g_bg) := by
    rw [show wOmega (I := I) (M := M) g₀ g₁ g_bg =
        appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (wXi (I := I) (M := M) g₀ g₁ g_bg) from rfl]
    exact (appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
      (wXi (I := I) (M := M) g₀ g₁ g_bg)).symm
  -- pointwise top-separated envelope for `∇ⁿ wOmega`
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (2 * ΛClow 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          + (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
            ∑ i ∈ Finset.range (n + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
                * ∑ l ∈ Finset.range (n + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l
                        (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    intro x
    rw [hwform, iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 3 1
      (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) n]
    rw [show ((appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
            (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)) +
          ∑ k ∈ Finset.range n,
            appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
              (iteratedCovGrad (I := I) g₀ 0 3 k
                (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = (appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
            (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x +
          (∑ k ∈ Finset.range n,
            appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
              (iteratedCovGrad (I := I) g₀ 0 3 k
                (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (1 + n) x _ _) ?_
    -- corner: coefficient fiber norm `≤ ΛClow 0`, no `appCcGdiag`
    have hcorner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
        ((appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
          (iteratedCovGrad (I := I) g₀ 0 3 n
            (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        ΛClow 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) n
        (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)) x) ?_
      exact mul_le_mul_of_nonneg_right (hc0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x _)
    -- lower sum: top-free, bounded by the two-arm triangular grid
    have hlower : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
        ((∑ k ∈ Finset.range n,
          appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
            (iteratedCovGrad (I := I) g₀ 0 3 k
              (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        ((n : ℝ) * appCcGdiag (E := E) n) *
          ∑ i ∈ Finset.range (n + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (n + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n))
      -- antidiagonal ≤ triangular grid
      set A : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
        with hA_def
      set B : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        with hB_def
      have hA_nn : ∀ i, 0 ≤ A i := fun i => riemannianFiberNormSq_nonneg _ _ _ _ _
      have hB_nn : ∀ l, 0 ≤ B l := fun l => riemannianFiberNormSq_nonneg _ _ _ _ _
      have hstep1 : ∑ k ∈ Finset.range n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
                ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                  (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 3 k
                  (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        refine mul_le_mul_of_nonneg_left ?_ (hA_nn (n - k))
        exact Finset.single_le_sum (fun l _ => hB_nn l)
          (Finset.mem_range.mpr (by omega))
      have hstep2 : ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l =
          ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := by
        rw [← Finset.sum_range_reflect
          (fun k => A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l) n]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hk1 : n - 1 - k + 1 = n - k := by omega
        rw [hk1]
      have hstep3 : ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l ≤
          ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := by
        rw [Finset.sum_range_succ' (fun i => A i * ∑ l ∈ Finset.range (n + 1 - i), B l) n]
        have h0 : 0 ≤ A 0 * ∑ l ∈ Finset.range (n + 1 - 0), B l :=
          mul_nonneg (hA_nn 0) (Finset.sum_nonneg fun l _ => hB_nn l)
        linarith
      calc ∑ k ∈ Finset.range n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                    (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 k
                    (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
            ≤ ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := hstep1
          _ = ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := hstep2
          _ ≤ ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := hstep3
    nlinarith [hcorner, hlower,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)]
  -- integrate the envelope
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (1 + n)
    (iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => (2 * ΛClow 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        + (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
          ∑ i ∈ Finset.range (n + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (n + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
    ((hwxi_int.const_mul (2 * ΛClow 0)).add
      (htri_int.const_mul (2 * ((n : ℝ) * appCcGdiag (E := E) n))))
    hpt
  rw [MeasureTheory.integral_add (hwxi_int.const_mul (2 * ΛClow 0))
      (htri_int.const_mul (2 * ((n : ℝ) * appCcGdiag (E := E) n))),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  -- ∫ wxi = ‖∇ⁿ wXi‖²
  have hwxi_eq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  rw [hwxi_eq] at hbridge
  -- two-arm integral bound → ball-uniform constant
  have hgrid_ballU : (∫ x, (∑ i ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l
                  (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n) := by
    refine le_trans htri_bd ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn n)
    rw [Real.sq_sqrt (hΛX_nn 0)]
    have e1 : ΛX 0 * (∑ i ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
        ΛX 0 * FC n := mul_le_mul_of_nonneg_left (hCsum n hn) (hΛX_nn 0)
    have e2 : ΛCsup ^ 2 * (∑ l ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 l (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCsup ^ 2 * FX n := mul_le_mul_of_nonneg_left (hXsum n hn) (sq_nonneg ΛCsup)
    linarith [e1, e2]
  -- assemble
  have htop := hxi g₁ P htie hδ_le hδ0 hδ hPball n hn
  have hc1 : (2 * ΛClow 0) *
        ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      2 * ΛClow 0 * Ktop_xi *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + 2 * ΛClow 0 * Cxi n := by
    have h2Λ : 0 ≤ 2 * ΛClow 0 := mul_nonneg (by norm_num) (hΛClow_nn 0)
    calc (2 * ΛClow 0) *
            ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ (2 * ΛClow 0) * (Ktop_xi *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + Cxi n) :=
          mul_le_mul_of_nonneg_left htop h2Λ
      _ = 2 * ΛClow 0 * Ktop_xi *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + 2 * ΛClow 0 * Cxi n := by ring
  have hc2 : (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
        (∫ x, (∑ i ∈ Finset.range (n + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (n + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 l
                    (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      2 * ((n : ℝ) * appCcGdiag (E := E) n) * (CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n)) := by
    exact mul_le_mul_of_nonneg_left hgrid_ballU
      (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n)))
  linarith [hbridge, hc1, hc2]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wAlpha L2 top-separated bound.**  `wAlpha = wAlphaA + wAlphaB`; the `wAlphaA` arm is
`‖∇ⁱwAlphaA‖² = ‖∇^{i+1}wOmega‖²` (`norm_iCG_wAlphaA_eq_succ_wOmega`), top-separated by
`wOmega_L2_topsep` at `n = i+1` (top `‖∇^{i+2}P‖²`); the `wAlphaB` arm is a two-arm product
`appCc wCA wOmega`, bounded ball-uniformly (top-free, folded into `C`).  `Ktop = 2·Ktop_om`. -/
private theorem wAlpha_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ, i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 + C i := by
  classical
  obtain ⟨Ktop_om, hKtop_om_nn, Com, hCom_nn, hom⟩ :=
    wOmega_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛO, FO, hΛO_nn, hFO_nn, hOgen⟩ :=
    wOmega_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛCd, FCd, hΛCd_nn, hFCd_nn, hCdgen⟩ :=
    connDiffSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 0 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 0 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * Ktop_om, mul_nonneg (by norm_num) hKtop_om_nn,
    fun i => 2 * Com (i + 1) +
      2 * (appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i))),
    fun i => add_nonneg (mul_nonneg (by norm_num) (hCom_nn (i + 1)))
      (mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hCT_nn i) (add_nonneg (mul_nonneg (hΛO_nn 0) (hFCd_nn i))
          (mul_nonneg (hΛCd_nn 0) (hFO_nn i)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball i hi
  obtain ⟨hOlow, hOsum⟩ := hOgen g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hCdlow, hCdsum⟩ := hCdgen g₁ P htie hδ_le hδ0 hδ hPball
  have hwCAlow : ∀ n : ℕ, n ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ΛCd n := by
    intro n hn x
    rw [rfns_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x]
    exact hCdlow n hn x
  have hwCAsum : ∀ i : ℕ, i ≤ a + 1 →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ FCd i := by
    intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q _ => ?_))) (hCdsum i hi)
    rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ q]
  have hBform : wAlphaB (I := I) (M := M) g₀ g₁ g_bg =
      appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  -- wAlphaB ball-uniform (top-free)
  have hBi : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i)) := by
    have hO0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
        ((wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛO 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛO_nn 0)]
      have h := hOlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    have hCA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((wCA (I := I) (M := M) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛCd 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛCd_nn 0)]
      have h := hwCAlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    obtain ⟨hgrid_int, hgrid_bound⟩ := hCT i (wCA (I := I) (M := M) g₀ g₁)
      (wOmega (I := I) (M := M) g₀ g₁ g_bg) (Real.sqrt (ΛCd 0)) (Real.sqrt (ΛO 0))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCA0 hO0
    rw [hBform]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i
        (appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)))
      (fun x => appCcGdiag (E := E) i *
        ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 1 l
                    (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (hgrid_int.const_mul (appCcGdiag (E := E) i))
      (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
        (wCA (I := I) (M := M) g₀ g₁) (wOmega (I := I) (M := M) g₀ g₁ g_bg) i x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine le_trans hgrid_bound ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn i)
    rw [Real.sq_sqrt (hΛO_nn 0), Real.sq_sqrt (hΛCd_nn 0)]
    have e1 : ΛO 0 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
        ΛO 0 * FCd i := mul_le_mul_of_nonneg_left (hwCAsum i (by omega)) (hΛO_nn 0)
    have e2 : ΛCd 0 * (∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 l (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCd 0 * FO i := mul_le_mul_of_nonneg_left (hOsum i (by omega)) (hΛCd_nn 0)
    linarith [e1, e2]
  -- wAlphaA top-separated (top `‖∇^{i+2}P‖²`)
  have hAi : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      Ktop_om * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 + Com (i + 1) := by
    rw [norm_iCG_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg i]
    exact hom g₁ P htie hδ_le hδ0 hδ hPball (i + 1) (by omega)
  -- wAlpha = wAlphaA + wAlphaB, triangle
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ := by
    rw [wAlpha, iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, hAi, hBi,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖)]

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the insert-level `deTurckLieWEndoInsert`.
Top `Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²)` with `R`-free `Ktop` (from `wAlpha_L2_topsep` via
`norm_iCG_wEndoInsert_eq_wAlpha`); the ball-uniform remainder is absorbed into `Kc i·(1+∑…)`.  The
DLb sibling of `deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated`. -/
theorem deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Ktop_a, hKtop_a_nn, C_a, hC_a_nn, ha⟩ :=
    wAlpha_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop_a, hKtop_a_nn, C_a, hC_a_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    add_nonneg zero_le_one
      (Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
      linarith [e1, e2, e3]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
          (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hwin : ∀ j : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
      intro j
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
        add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
      have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤
          (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
        rw [heq]
        calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
                + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
            ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
                + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
          _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
                + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg h1ms, abs_of_nonneg hs0]
      nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
          (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
        mul_nonneg (mul_nonneg hs0 h1ms)
          (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
        mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
        mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
    have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδP x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
          (convexPerturbation (I := I) g₀ T T' s) x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) *
          Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    rw [norm_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i]
    have hbase := ha (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i hi
    have htop_le : Ktop_a *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        Ktop_a * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hwin (i + 2)) hKtop_a_nn
    have hrem_le : C_a i ≤ C_a i * (1 + ∑ j ∈ Finset.range (i + 3),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
      nlinarith [hC_a_nn i, hsum_nn,
        Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 3)) =>
          add_nonneg (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖))
            (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)))]
    linarith [hbase, htop_le, hrem_le]
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckLieWEndoInsert (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hrhs : (0 : ℝ) ≤ Ktop_a * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
        C_a i * (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      add_nonneg (mul_nonneg hKtop_a_nn (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (hC_a_nn i) hsum_nn)
    nlinarith [hrhs]

set_option linter.unusedVariables false in
/-- **Summed** `realizedFam` top-separated jet-L2 bound for `deTurckLieWEndoInsert`.  Both windows
`a+3` (via `jetL2_sum_lowShift a 2 3`), `Ktop` `R`-free, single `Kc = ∑_{i≤a} Kc_perOrder i`.  The
DLb sibling of `deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated`. -/
theorem deTurckLieWEndoInsert_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 1 i
                (deTurckLieWEndoInsert (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 2 3 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DLbTopSeparated

end DifferentialGeometry.Integral.Connection

end
