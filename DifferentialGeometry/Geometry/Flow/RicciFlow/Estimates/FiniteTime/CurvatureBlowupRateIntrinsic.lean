import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.CurvatureBlowupRate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Time
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor.Coordinates

open Bundle
open scoped Manifold ContDiff BigOperators

section Cost

theorem rmTowerCost_zero (d : Nat) :
    rmTowerCost d 0 = 32 * (d : Real) ^ 4 := by
  have hcard : (Fintype.card (Fin (4 + 0) -> Fin d) : Real) = (d : Real) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have hsq : Real.sqrt ((d : Real) ^ 4) = (d : Real) ^ 2 := by
    rw [show ((d : Real) ^ 4) = ((d : Real) ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hres : rmResidualCost d 0 = 12 * (d : Real) ^ 2 := rfl
  unfold rmTowerCost
  rw [hcard, hsq, hres]
  push_cast
  ring


theorem rmTowerCost_zero_pos {d : Nat} (hd : d ≠ 0) :
    0 < rmTowerCost d 0 := by
  have hdpos : (0 : Real) < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  rw [rmTowerCost_zero]
  positivity

end Cost

section IntrinsicSubsolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
theorem nablaKNormLap_eq_laplacianAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (k : Nat)
    (t : Real) (x : M) :
    nablaKNormLap (I := I) S k t x =
      laplacianAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S k t) x := rfl

omit [SigmaCompactSpace M] in
theorem isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution
    {alpha omega t1 : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    (halphat1 : alpha < t1) (ht1omega : t1 < omega) :
    IsHeatPotSubsolutionOn (RealTimeInterval.closedOpen t1 omega ht1omega)
      (flowG (I := I) S)
      (fun t x => rmTowerCost (Module.finrank Real E) 0 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x))
      (nablaKRm04NormSqIntrinsic (I := I) S 0) := by
  have hregsub :
      (RealTimeInterval.closedOpen t1 omega ht1omega).regular ×ˢ (Set.univ : Set M) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular ×ˢ
          (Set.univ : Set M) := by
    intro q hq
    exact ⟨⟨lt_trans halphat1 hq.1.1, hq.1.2⟩, trivial⟩
  have hcarsub :
      (RealTimeInterval.closedOpen t1 omega ht1omega).carrier ×ˢ (Set.univ : Set M) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular ×ˢ
          (Set.univ : Set M) := by
    intro q hq
    exact ⟨⟨lt_of_lt_of_le halphat1 hq.1.1, hq.1.2⟩, trivial⟩
  have hjoint := towerNorm_joint (I := I) hS 0
  have hkey : ∀ t : Real,
      t ∈ (RealTimeInterval.closedOpen t1 omega ht1omega).regular -> ∀ x : M,
      DifferentiableAt Real
          (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S 0 s x) t ∧
        deriv (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S 0 s x) t ≤
          laplacianAt (I := I) (flowG (I := I) S) t
              (nablaKRm04NormSqIntrinsic (I := I) S 0 t) x +
            rmTowerCost (Module.finrank Real E) 0 *
              Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
              nablaKRm04NormSqIntrinsic (I := I) S 0 t x := by
    intro t ht x
    have htreg : t ∈ (RealTimeInterval.closedOpen alpha omega halphaomega).regular :=
      ⟨lt_trans halphat1 ht.1, ht.2⟩
    obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution (I := I) S hS 0 ⟨t, htreg⟩ x
    have hnhds :
        (RealTimeInterval.closedOpen alpha omega halphaomega).carrier ∈ nhds t :=
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular_mem_nhds htreg
    have hd' : HasDerivAt
        (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S 0 s x) d t :=
      hd.hasDerivAt hnhds
    have hnn0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
      nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
    have hnn1 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
      nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
    have hsqrt :
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) =
          nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
      Real.mul_self_sqrt hnn0
    have hsum :
        towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
            (rmTowerCost (Module.finrank Real E) 0) 0 t x =
          rmTowerCost (Module.finrank Real E) 0 *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) := by
      simp [towerReactionSum]
    have hcube :
        rmTowerCost (Module.finrank Real E) 0 *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) =
          rmTowerCost (Module.finrank Real E) 0 *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            nablaKRm04NormSqIntrinsic (I := I) S 0 t x := by
      linear_combination (rmTowerCost (Module.finrank Real E) 0 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x)) * hsqrt
    rw [hsum] at hle
    rw [nablaKNormLap_eq_laplacianAt (I := I) S 0 t x] at hle
    refine ⟨hd'.differentiableAt, ?_⟩
    rw [hd'.deriv]
    linarith
  exact
    { jointSmooth := hjoint.mono hregsub
      jointCont := hjoint.continuousOn.mono hcarsub
      sliceSmooth := fun t _ => nablaKNorm_smooth (I := I) S t 0
      timeDiff := fun t ht x => (hkey t ht x).1
      equation_le := fun t ht x => (hkey t ht x).2 }

end IntrinsicSubsolution

section DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [T2Space M]
variable [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem curvatureNormSq_eq_nablaKRm04NormSqIntrinsic
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {Rm04 : Real -> Tensor04Section (I := I) (M := M)}
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    {t : Real} (ht : t ∈ D.carrier) (x : M) :
    curvatureNormSq (I := I) S Rm04 t x =
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x := by
  have heq : Rm04 t x = S.base.rm04 t x :=
    rm04_eq_of_realizes (I := I) (S.family.metric t) (S.family.connection t)
      (hRm ⟨t, ht⟩) (rm04Realizes_metric (I := I) S ⟨t, ht⟩) x
  change Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 (Rm04 t x) = _
  rw [heq]
  rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem rm04NormSqUnboundedAt_iff_rm04NormSqUnboundedOn
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    {Rm04 : Real -> Tensor04Section (I := I) (M := M)}
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    Rm04NormSqUnboundedAt (I := I) S Rm04 ↔ Rm04NormSqUnboundedOn (I := I) S := by
  constructor
  · intro h K
    obtain ⟨t, x, h1, h2, h3⟩ := h K
    have hmem : t ∈ (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
      ⟨h1, h2⟩
    rw [curvatureNormSq_eq_nablaKRm04NormSqIntrinsic (I := I) S hRm hmem x] at h3
    exact ⟨t, x, hmem, h3⟩
  · intro h K
    obtain ⟨t, x, hmem, h3⟩ := h K
    have hmem' : t ∈ Set.Ico alpha omega := hmem
    refine ⟨t, x, hmem'.1, hmem'.2, ?_⟩
    rwa [curvatureNormSq_eq_nablaKRm04NormSqIntrinsic (I := I) S hRm hmem x]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem formsSingularityAt_iff_rm04NormSqUnboundedOn
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) :
    FormsSingularityAt (I := I) S ↔ Rm04NormSqUnboundedOn (I := I) S := by
  constructor
  · rintro ⟨Rm04, hRm, hunb⟩
    exact (rm04NormSqUnboundedAt_iff_rm04NormSqUnboundedOn (I := I) S hRm).mp hunb
  · intro h
    exact ⟨S.base.rm04, rm04Realizes_metric (I := I) S,
      (rm04NormSqUnboundedAt_iff_rm04NormSqUnboundedOn (I := I) S
        (rm04Realizes_metric (I := I) S)).mpr h⟩

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [VectorBundle Real E (TangentSpace I : M -> Type _)] in
private theorem rm04NormSqIntrinsic_zero_continuousOn_carrier
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) :
    ContinuousOn (fun q : Real × M => nablaKRm04NormSqIntrinsic (I := I) S 0 q.1 q.2)
      (Set.Ico alpha omega ×ˢ (Set.univ : Set M)) := by
  classical
  rintro ⟨s0, y0⟩ hq0
  have haB : y0 ∈ (trivializationAt E (TangentSpace I) y0).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) y0
  have hnb : ((Set.univ : Set Real) ×ˢ (trivializationAt E (TangentSpace I) y0).baseSet)
      ∈ nhds ((s0, y0) : Real × M) :=
    (isOpen_univ.prod (trivializationAt E (TangentSpace I) y0).open_baseSet).mem_nhds
      ⟨trivial, haB⟩
  rw [← continuousWithinAt_inter hnb]
  have hinter : (Set.Ico alpha omega ×ˢ (Set.univ : Set M)) ∩
      ((Set.univ : Set Real) ×ˢ (trivializationAt E (TangentSpace I) y0).baseSet) =
      Set.Ico alpha omega ×ˢ (trivializationAt E (TangentSpace I) y0).baseSet := by
    ext q
    exact ⟨fun hq => ⟨hq.1.1, hq.2.2⟩, fun hq => ⟨⟨hq.1, trivial⟩, ⟨trivial, hq.2⟩⟩⟩
  rw [hinter]
  refine ContinuousOn.continuousWithinAt ?_ ⟨hq0.1, haB⟩
  rw [continuousOn_iff_continuous_domRestrict]
  set W : Set (Real × M) :=
    Set.Ico alpha omega ×ˢ (trivializationAt E (TangentSpace I) y0).baseSet with hW
  have hbmem : ∀ p : ↥W, p.1.2 ∈ (trivializationAt E (TangentSpace I) y0).baseSet := by
    intro p
    have hp : p.1 ∈ Set.Ico alpha omega ×ˢ
        (trivializationAt E (TangentSpace I) y0).baseSet := by
      rw [← hW]
      exact p.2
    exact hp.2
  have htmem : ∀ p : ↥W,
      p.1.1 ∈ (RealTimeInterval.closedOpen alpha omega halphaomega).carrier := by
    intro p
    have hp : p.1 ∈ Set.Ico alpha omega ×ˢ
        (trivializationAt E (TangentSpace I) y0).baseSet := by
      rw [← hW]
      exact p.2
    exact hp.1
  have htcont : Continuous (fun p : ↥W => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hbcont : Continuous (fun p : ↥W => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hgramEnt : ∀ i j : Fin (Module.finrank Real E),
      Continuous (fun p : ↥W =>
        chartGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2 i j) := by
    intro i j
    have h := chartGram_cont_of_solution (I := I) hS y0 i j
    rw [continuousOn_iff_continuous_domRestrict, ← hW] at h
    exact h
  have hGm : Continuous (fun p : ↥W =>
      chartGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2) :=
    continuous_matrix fun i j => hgramEnt i j
  have hdetne : ∀ p : ↥W,
      (chartGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2).det ≠ 0 := fun p =>
    ne_of_gt (chartGramMatrix_det_pos (I := I) (S.base.metric p.1.1) y0 (hbmem p))
  have hGinv : Continuous (fun p : ↥W =>
      chartInvGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2) := by
    have hexp : (fun p : ↥W =>
        chartInvGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2) =
        fun p : ↥W =>
          ((chartGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2).det)⁻¹ •
            (chartGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2).adjugate := by
      funext p
      rw [chartInvGramMatrix, Matrix.inv_def, Ring.inverse_eq_inv]
    rw [hexp]
    exact (hGm.matrix_det.inv₀ hdetne).smul hGm.matrix_adjugate
  have hGinvEnt : ∀ i j : Fin (Module.finrank Real E),
      Continuous (fun p : ↥W =>
        chartInvGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2 i j) := fun i j =>
    hGinv.matrix_elem i j
  have hcomp : ∀ idx : Fin 4 -> Fin (Module.finrank Real E),
      Continuous (fun p : ↥W => S.base.rm04 p.1.1 p.1.2
        (fun k : Fin 4 => chartBasisVecFiber (I := I) y0 (idx k) p.1.2)) := by
    intro idx
    refine hS.rm04Cont.eval_continuous (P := ↥W)
      (v := fun k p => chartBasisVecFiber (I := I) y0 (idx k) p.1.2)
      htcont htmem hbcont ?_
    intro k
    exact (chartBasisVec_contMDiffOn (I := I) y0 (idx k)).continuousOn.comp_continuous
      hbcont hbmem
  have hsum : Continuous (fun p : ↥W =>
      ∑ I0 : Fin 4 -> Fin (Module.finrank Real E),
        ∑ J0 : Fin 4 -> Fin (Module.finrank Real E),
          (∏ k : Fin 4,
              chartInvGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2 (I0 k) (J0 k)) *
            S.base.rm04 p.1.1 p.1.2
              (fun k : Fin 4 => chartBasisVecFiber (I := I) y0 (I0 k) p.1.2) *
            S.base.rm04 p.1.1 p.1.2
              (fun k : Fin 4 => chartBasisVecFiber (I := I) y0 (J0 k) p.1.2)) := by
    refine continuous_finsetSum _ fun I0 _ => continuous_finsetSum _ fun J0 _ => ?_
    exact ((continuous_finsetProd _ fun k _ => hGinvEnt (I0 k) (J0 k)).mul
      (hcomp I0)).mul (hcomp J0)
  refine hsum.congr ?_
  intro p
  have hx : p.1.2 ∈ (trivializationAt E (TangentSpace I) y0).baseSet := hbmem p
  change _ = normSq0S (I := I) (S.base.metric p.1.1) p.1.2 4 (S.base.rm04 p.1.1 p.1.2)
  rw [normSq0S_eq_coord (I := I) (S.base.metric p.1.1) p.1.2 4
    (chartBasisFamily (I := I) y0 hx)
    (fun i j => chartInvGramMatrix (I := I) (S.base.metric p.1.1) y0 p.1.2 i j)
    (chartInvGram_inverse (I := I) (S.base.metric p.1.1) y0 hx)
    (S.base.rm04 p.1.1 p.1.2)]
  simp only [coordInner0S, tensor0SComponent_apply, chartBasisFamily_apply]

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem exists_bound_nablaKRm04NormSqIntrinsic_zero_on_initial_Icc
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    {t0 : Real} (ht0 : t0 < omega) :
    ∃ B : Real, ∀ t : Real, ∀ x : M, alpha ≤ t -> t ≤ t0 ->
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ B := by
  have hsub : Set.Icc alpha t0 ×ˢ (Set.univ : Set M) ⊆
      Set.Ico alpha omega ×ˢ (Set.univ : Set M) := by
    intro q hq
    exact ⟨⟨hq.1.1, lt_of_le_of_lt hq.1.2 ht0⟩, trivial⟩
  have hcont := (rm04NormSqIntrinsic_zero_continuousOn_carrier (I := I) hS).mono hsub
  have hcompact : IsCompact (Set.Icc alpha t0 ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨B, hB⟩ := (hcompact.image_of_continuousOn hcont).bddAbove
  exact ⟨B, fun t x h1 h2 => hB ⟨(t, x), ⟨⟨h1, h2⟩, trivial⟩, rfl⟩⟩

theorem curvatureDoublingSpan_le_of_maximal_of_bddOn_initial
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    {Rm04 : Real -> Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) halphaomega S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    {t0 Q0 : Real} (hQ0 : 0 < Q0)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (hQ : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t0 x ≤ Q0 ^ 2)
    (hearly : ∃ B : Real, ∀ t : Real, ∀ x : M, alpha ≤ t -> t ≤ t0 ->
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ B) :
    curvatureDoublingSpan (rmTowerCost (Module.finrank Real E) 0) Q0 ≤ omega - t0 := by
  classical
  have hne : Module.finrank Real E ≠ 0 := by
    rw [hdim]
    norm_num
  have hc0 : 0 < rmTowerCost (Module.finrank Real E) 0 := rmTowerCost_zero_pos hne
  set t1 : Real := (alpha + t0) / 2 with ht1def
  have halphat1 : alpha < t1 := by
    rw [ht1def]
    linarith
  have ht1t0 : t1 < t0 := by
    rw [ht1def]
    linarith
  have ht1omega : t1 < omega := lt_trans ht1t0 ht0omega
  let S1 : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen t1 omega ht1omega) := { base := S.base }
  have hsub1 : IsHeatPotSubsolutionOn (RealTimeInterval.closedOpen t1 omega ht1omega)
      (flowG (I := I) S1)
      (fun t x => rmTowerCost (Module.finrank Real E) 0 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S1 0 t x))
      (nablaKRm04NormSqIntrinsic (I := I) S1 0) :=
    isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution (I := I) hS
      halphat1 ht1omega
  have hunbAt : Rm04NormSqUnboundedAt (I := I) S Rm04 :=
    rmUnbounded_of_maximal (I := I) hdim hS hmax hRm
  have hunb1 : Rm04NormSqUnboundedOn (I := I) S1 := by
    intro K
    obtain ⟨B, hB⟩ := hearly
    obtain ⟨t, x, h1, h2, h3⟩ := hunbAt (max K B)
    have hmem : t ∈ (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
      ⟨h1, h2⟩
    rw [curvatureNormSq_eq_nablaKRm04NormSqIntrinsic (I := I) S hRm hmem x] at h3
    have hBlt : B < nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
      lt_of_le_of_lt (le_max_right K B) h3
    have ht1lt : t1 < t := by
      by_contra hcon
      have hle : t ≤ t0 := le_trans (not_lt.mp hcon) (le_of_lt ht1t0)
      exact absurd (hB t x h1 hle) (not_le.mpr hBlt)
    refine ⟨t, x, ⟨le_of_lt ht1lt, h2⟩, ?_⟩
    exact lt_of_le_of_lt (le_max_left K B) h3
  have ht0mem : t0 ∈ Set.Ico t1 omega := ⟨le_of_lt ht1t0, ht0omega⟩
  have hQ1 : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S1 0 t0 x ≤ Q0 ^ 2 := hQ
  exact curvatureDoublingSpan_le_of_rm04NormSqUnbounded (I := I) S1 hc0 hQ0 hsub1
    hunb1 ht0mem hQ1

theorem curvatureDoublingSpan_le_of_maximal_dim_three
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    {Rm04 : Real -> Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) halphaomega S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    {t0 Q0 : Real} (hQ0 : 0 < Q0)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (hQ : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t0 x ≤ Q0 ^ 2) :
    curvatureDoublingSpan (rmTowerCost (Module.finrank Real E) 0) Q0 ≤ omega - t0 :=
  curvatureDoublingSpan_le_of_maximal_of_bddOn_initial (I := I) hdim hS hmax hRm hQ0
    halphat0 ht0omega hQ
    (exists_bound_nablaKRm04NormSqIntrinsic_zero_on_initial_Icc (I := I) hS ht0omega)

theorem one_div_le_endpoint_sub_of_maximal_dim_three
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    {Rm04 : Real -> Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) halphaomega S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    {t0 Q0 : Real} (hQ0 : 0 < Q0)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (hQ : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t0 x ≤ Q0 ^ 2) :
    1 / (2592 * Q0) ≤ omega - t0 := by
  have h := curvatureDoublingSpan_le_of_maximal_dim_three (I := I) hdim hS hmax hRm hQ0
    halphat0 ht0omega hQ
  have hc : rmTowerCost (Module.finrank Real E) 0 = 2592 := by
    rw [rmTowerCost_zero, hdim]
    norm_num
  rw [hc] at h
  unfold curvatureDoublingSpan at h
  exact h

end DimensionThree

end DifferentialGeometry.PDE.RicciFlow
