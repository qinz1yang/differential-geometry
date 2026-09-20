import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimTerminalFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalTrichotomyReductionTopology : TopologicalSpace F.M := F.topology
local instance terminalTrichotomyReductionCharted : ChartedSpace H F.M := F.charted
local instance terminalTrichotomyReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalTrichotomyReductionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalTrichotomyReductionT2 : T2Space F.M := F.t2
local instance terminalTrichotomyReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalTrichotomyReductionInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance terminalTrichotomyReductionLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance terminalTrichotomyReductionSemilocallySimplyConnected : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem exists_null_plane_of_terminalSurfaceProduct
    (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
          ((F.S.base.metric 0).inner x a b) ^ 2 ∧
        F.S.base.rm04 0 x (vec4 (I := I) a b b a) = 0 := by
  let _ : TopologicalSpace P.S := P.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P.S := P.charted
  let _ : IsManifold (𝓡 2) ∞ P.S := P.smooth
  let _ : IsManifold (𝓡 2) 1 P.S :=
    IsManifold.of_le (I := 𝓡 2) (M := P.S) (n := ∞) (by decide)
  let _ : T2Space P.S := P.t2
  let _ : SigmaCompactSpace P.S := P.sigmaCompact
  let _ : ConnectedSpace P.S := P.connected
  let y : P.S := Classical.choice inferInstance
  have hfin : 0 < Module.finrank ℝ (TangentSpace (𝓡 2) y) := by
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) y) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := rfl
    rw [hdim]
    simp
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hfin
  let p : P.S × ℝ := (y, 0)
  let x : F.M := UniversalCover.proj (P.Phi p)
  let a : TangentSpace I x := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi p (v, (0 : ℝ))
  let b : TangentSpace I x :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi p ((0 : TangentSpace (𝓡 2) y), (1 : ℝ))
  have hAA : (F.S.base.metric 0).inner x a a = P.h.inner y v v := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) a a).trans ?_
    have hh := P.product y 0 v v 0 0
    simpa only [a, p, mul_zero, add_zero] using hh
  have hBB : (F.S.base.metric 0).inner x b b = 1 := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) b b).trans ?_
    have hh := P.product y 0 0 0 1 1
    simpa only [b, p, map_zero, mul_zero, zero_mul, one_mul, add_zero, zero_add] using hh
  have hAB : (F.S.base.metric 0).inner x a b = 0 := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) a b).trans ?_
    have hh := P.product y 0 v 0 0 1
    simpa only [a, b, p, map_zero, mul_zero, zero_mul, add_zero] using hh
  refine ⟨x, a, b, ?_, ?_⟩
  · rw [hAA, hBB, hAB, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
    exact (P.h).pos y v hv
  · let gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (P.S × ℝ) :=
      Diffeomorph.pullbackMetricCross
        (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi
    have hgP : ∀ (y' : P.S) (s' : ℝ) (v' w' : TangentSpace (𝓡 2) y') (a' c' : ℝ),
        gP.inner (y', s') (v', a') (w', c') = P.h.inner y' v' w' + a' * c' := by
      intro y' s' v' w' a' c'
      exact (Diffeomorph.pullbackMetricCross_inner
        (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi
        (y', s') (v', a') (w', c')).trans (P.product y' s' v' w' a' c')
    have hprodRm := metricRm04At_product_real_of_inner_eq P.h gP hgP y 0
      (vec4 (I := 𝓡 2) (M := P.S) (x := y) v 0 0 v) (![0, 1, 1, 0] : Fin 4 → ℝ)
    have hslots : (fun i : Fin 4 =>
        ((vec4 (I := 𝓡 2) (M := P.S) (x := y) v 0 0 v) i,
          (![0, 1, 1, 0] : Fin 4 → ℝ) i)) =
        vec4 (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := P.S × ℝ) (x := p)
          (v, 0) (0, 1) (0, 1) (v, 0) := by
      funext i
      fin_cases i <;> rfl
    have hzero : metricRm04StandardAt (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
        (v, 0) (0, 1) (0, 1) (v, 0) = 0 :=
      (congrArg (metricRm04At gP p) hslots.symm).trans
        (hprodRm.trans
          ((metricRm04At (P.h) y).map_coord_zero (1 : Fin 4) (by rfl)))
    have hpull := metricRm04Standard_pullbackCross
      (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi p
      (v, 0) (0, 1) (0, 1) (v, 0)
    have hlift := UniversalCover.metricRm_lifted (I := I) (F.S.base.metric 0) (P.Phi p)
      a b b a
    simpa only [metricRm04StandardAt_apply, SolutionOn.family, SolutionFamily.rm04,
      metricRm04_apply] using hlift.symm.trans (hpull.symm.trans hzero)

theorem exists_positive_curvature_plane_of_terminalSurfaceProduct
    (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
          ((F.S.base.metric 0).inner x a b) ^ 2 ∧
        0 < F.S.base.rm04 0 x (vec4 (I := I) a b b a) := by
  let _ : TopologicalSpace P.S := P.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P.S := P.charted
  let _ : IsManifold (𝓡 2) ∞ P.S := P.smooth
  let _ : IsManifold (𝓡 2) 1 P.S :=
    IsManifold.of_le (I := 𝓡 2) (M := P.S) (n := ∞) (by decide)
  let _ : T2Space P.S := P.t2
  let _ : SigmaCompactSpace P.S := P.sigmaCompact
  let _ : ConnectedSpace P.S := P.connected
  let y : P.S := Classical.choice inferInstance
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℝ)
    (M := TangentSpace (𝓡 2) y) (n := 2) (by
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) y) =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := rfl
      rw [hdim]
      simp)
  have hfli : LinearIndependent ℝ ![f 0, f 1] := by
    have hcast : ![f 0, f 1] = f := by
      funext i
      fin_cases i <;> rfl
    rw [hcast]
    exact hf
  let v : TangentSpace (𝓡 2) y := f 0
  let w : TangentSpace (𝓡 2) y := f 1
  let p : P.S × ℝ := (y, 0)
  let x : F.M := UniversalCover.proj (P.Phi p)
  let a : TangentSpace I x := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi p (v, (0 : ℝ))
  let b : TangentSpace I x := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi p (w, (0 : ℝ))
  have hAA : (F.S.base.metric 0).inner x a a = P.h.inner y v v := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) a a).trans ?_
    have hh := P.product y 0 v v 0 0
    simpa only [a, p, mul_zero, add_zero] using hh
  have hBB : (F.S.base.metric 0).inner x b b = P.h.inner y w w := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) b b).trans ?_
    have hh := P.product y 0 w w 0 0
    simpa only [b, p, mul_zero, add_zero] using hh
  have hAB : (F.S.base.metric 0).inner x a b = P.h.inner y v w := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.base.metric 0)
      (P.Phi p) a b).trans ?_
    have hh := P.product y 0 v w 0 0
    simpa only [a, b, p, mul_zero, add_zero] using hh
  refine ⟨x, a, b, ?_, ?_⟩
  · rw [hAA, hBB, hAB]
    simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
      Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
        (I := 𝓡 2) (M := P.S) P.h y v w hfli
  · let gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (P.S × ℝ) :=
      Diffeomorph.pullbackMetricCross
        (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi
    have hgP : ∀ (y' : P.S) (s' : ℝ) (v' w' : TangentSpace (𝓡 2) y') (a' c' : ℝ),
        gP.inner (y', s') (v', a') (w', c') = P.h.inner y' v' w' + a' * c' := by
      intro y' s' v' w' a' c'
      exact (Diffeomorph.pullbackMetricCross_inner
        (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi
        (y', s') (v', a') (w', c')).trans (P.product y' s' v' w' a' c')
    have hprodRm := metricRm04At_product_real_of_inner_eq P.h gP hgP y 0
      (vec4 (I := 𝓡 2) (M := P.S) (x := y) v w w v) (0 : Fin 4 → ℝ)
    have hslots : (fun i : Fin 4 =>
        ((vec4 (I := 𝓡 2) (M := P.S) (x := y) v w w v) i, (0 : ℝ))) =
        vec4 (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := P.S × ℝ) (x := p)
          (v, 0) (w, 0) (w, 0) (v, 0) := by
      funext i
      fin_cases i <;> rfl
    have hprodval : metricRm04StandardAt (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
        (v, 0) (w, 0) (w, 0) (v, 0) =
        metricRm04StandardAt (I := 𝓡 2) (M := P.S) P.h y v w w v := by
      calc metricRm04StandardAt (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
            (v, 0) (w, 0) (w, 0) (v, 0)
          = metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
              (vec4 (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := P.S × ℝ) (x := p)
                (v, 0) (w, 0) (w, 0) (v, 0)) :=
            metricRm04StandardAt_apply (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
              (v, 0) (w, 0) (w, 0) (v, 0)
        _ = metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
              (fun i : Fin 4 =>
                ((vec4 (I := 𝓡 2) (M := P.S) (x := y) v w w v) i, (0 : ℝ))) :=
            congrArg (metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p) hslots.symm
        _ = metricRm04At (I := 𝓡 2) (M := P.S) P.h y
              (vec4 (I := 𝓡 2) (M := P.S) (x := y) v w w v) := hprodRm
        _ = metricRm04StandardAt (I := 𝓡 2) (M := P.S) P.h y v w w v :=
            (metricRm04StandardAt_apply (I := 𝓡 2) (M := P.S) P.h y v w w v).symm
    have hpull := metricRm04Standard_pullbackCross
      (UniversalCover.liftedMetric (I := I) (F.S.base.metric 0)) P.Phi p
      (v, 0) (w, 0) (w, 0) (v, 0)
    have hlift := UniversalCover.metricRm_lifted (I := I) (F.S.base.metric 0) (P.Phi p)
      a b b a
    have hbridge : metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a =
        metricRm04StandardAt (I := 𝓡 2) (M := P.S) P.h y v w w v :=
      hlift.symm.trans (hpull.symm.trans hprodval)
    have hgoal : F.S.base.rm04 0 x (vec4 (I := I) a b b a) =
        metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a := by
      rw [show F.S.base.rm04 0 x =
          metricRm04 (I := I) (M := F.M) (F.S.base.metric 0) x from rfl]
      rw [metricRm04_apply, metricRm04StandardAt_apply]
    rw [hgoal, hbridge]
    exact P.positive y v w hfli

theorem not_hasPositiveSectionalCurvature_of_terminalSurfaceProduct
    (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0) := by
  intro hpos
  obtain ⟨x, a, b, hgram, hnull⟩ := exists_null_plane_of_terminalSurfaceProduct F P
  have hpair : LinearIndependent ℝ ![a, b] :=
    Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := I) (M := F.M) (F.S.base.metric 0) x a b
      (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram)
  exact (ne_of_gt (hpos x a b hpair)) hnull

theorem not_hasPositiveSectionalCurvature_of_nonempty_terminalSurfaceProduct
    (h : Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0) :=
  h.elim (not_hasPositiveSectionalCurvature_of_terminalSurfaceProduct F)

theorem not_terminal_flat_of_terminalSurfaceProduct
    (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    ¬ ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0 := by
  intro hflat
  obtain ⟨x, a, b, _, hpos⟩ := exists_positive_curvature_plane_of_terminalSurfaceProduct F P
  have hrm : F.S.base.rm04 0 x = 0 := by
    have h := hflat x
    rw [PointedFlowData.rmNormSq, SolutionOn.family_metric] at h
    exact (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) (F.S.base.metric 0) x 4
      (F.S.base.rm04 0 x)).mp h
  rw [hrm] at hpos
  simp at hpos

omit [I.Boundaryless] in
theorem not_hasPositiveSectionalCurvature_of_terminal_flat
    (hdim : Module.finrank ℝ E = 3)
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) :
    ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0) := by
  intro hpos
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℝ)
    (M := TangentSpace I F.basepoint) (n := 2) (by
      rw [show Module.finrank ℝ (TangentSpace I F.basepoint) = Module.finrank ℝ E from rfl,
        hdim]
      norm_num)
  have hfli : LinearIndependent ℝ ![f 0, f 1] := by
    have hcast : ![f 0, f 1] = f := by
      funext i
      fin_cases i <;> rfl
    rw [hcast]
    exact hf
  have hzero : metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) F.basepoint
      (f 0) (f 1) (f 1) (f 0) = 0 := by
    have hrm : F.S.base.rm04 0 F.basepoint = 0 := by
      have h := hflat F.basepoint
      rw [PointedFlowData.rmNormSq, SolutionOn.family_metric] at h
      exact (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) (F.S.base.metric 0) F.basepoint 4
        (F.S.base.rm04 0 F.basepoint)).mp h
    rw [metricRm04StandardAt_apply]
    rw [show metricRm04At (I := I) (M := F.M) (F.S.base.metric 0) F.basepoint =
        F.S.base.rm04 0 F.basepoint from (show F.S.base.rm04 0 F.basepoint =
          metricRm04 (I := I) (M := F.M) (F.S.base.metric 0) F.basepoint from rfl).symm.trans
            (metricRm04_apply (I := I) (M := F.M) (F.S.base.metric 0) F.basepoint).symm]
    rw [hrm]
    rfl
  exact (ne_of_gt (hpos F.basepoint (f 0) (f 1) hfli)) hzero

omit [I.Boundaryless] in
theorem not_kLim_of_forall_rmNormSq_eq_zero {kappa : ℝ}
    (hflat : ∀ t ∈ D.carrier, ∀ x : F.M, F.rmNormSq (I := I) t x = 0) :
    ¬ KLim (I := I) kappa F := by
  intro hK
  obtain ⟨t, ht, x, hx⟩ := hK.notFlat
  exact hx (hflat t ht x)

theorem terminal_curvature_trichotomy_alternatives_pairwise_exclusive
    (hdim : Module.finrank ℝ E = 3) :
    ¬ (DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
          (F.S.base.metric 0) ∧
        Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) ∧
      ¬ (DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
          (F.S.base.metric 0) ∧
        (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0)) ∧
      ¬ ((∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∧
        Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :=
  ⟨fun h => not_hasPositiveSectionalCurvature_of_nonempty_terminalSurfaceProduct F h.2 h.1,
    fun h => not_hasPositiveSectionalCurvature_of_terminal_flat F hdim h.2 h.1,
    fun h => h.2.elim (fun P => not_terminal_flat_of_terminalSurfaceProduct F P h.1)⟩

def TerminalCurvatureDichotomy (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) →
    (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem terminalCurvatureDichotomy_of_terminal_flat
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) :
    TerminalCurvatureDichotomy (I := I) F :=
  fun _ => Or.inl hflat

theorem terminalCurvatureDichotomy_of_terminalSurfaceProduct
    (hprod : Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalCurvatureDichotomy (I := I) F :=
  fun _ => Or.inr hprod

theorem terminal_curvature_trichotomy_of_terminalCurvatureDichotomy
    (hdichotomy : TerminalCurvatureDichotomy (I := I) F) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  by_cases hpos : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
    (F.S.base.metric 0)
  · exact Or.inl hpos
  · rcases hdichotomy hpos with hflat | hprod
    · exact Or.inr (Or.inl hflat)
    · exact Or.inr (Or.inr hprod)

theorem terminalCurvatureDichotomy_of_terminalNullPlaneSplitting {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hsplit : TerminalNullPlaneSplitting (I := I) F) :
    TerminalCurvatureDichotomy (I := I) F := by
  intro hnotpos
  have hnotAll : ¬ ∀ x : F.M,
      CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
    fun h => hnotpos
      ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (I := I) (M := F.M) (F.S.base.metric 0) hdim).mpr h)
  have hnonneg : ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h0 : (0 : ℝ) ∈ D.carrier := by
      simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
    have h := hK.nonnegativeCurvatureOperator 0 h0 x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  obtain ⟨x, a, b, hgram, hsec⟩ :=
    exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt (I := I) (M := F.M)
      (F.S.base.metric 0) hdim hnonneg hnotAll
  exact hsplit x a b hgram hsec

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
