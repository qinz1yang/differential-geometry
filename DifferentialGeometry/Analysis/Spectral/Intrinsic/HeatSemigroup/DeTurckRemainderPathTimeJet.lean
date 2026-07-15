import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_smoothCcTensor_of_allOrder_spectralMass
    (g₀ : SmoothRiemannianMetric I M)
    (d : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i) :
    ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = d i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨B0, hB0s, hB0le⟩ := hmass 0 le_rfl
  set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
    tensorHs_of_spectralMass_majorant (I := I) (M := M) d B0 hB0s hB0le with hv0_def
  set u : TensorL2 0 2 g₀ :=
    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = d i := by
    intro i
    rw [hu_def, tensorHsToL2_tensorL2Coeff]
    simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff]
  have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hBs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hu_coeff i]; exact hBle i
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
    allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
  obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
  refine ⟨S, fun i => ?_⟩
  have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
        = (S : TensorL2 0 2 g₀) from rfl, hS]
  rw [hSL2, hu_coeff i]

private def deTurckRHSReconSection (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }

section RealizePathJointSmoothness

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

private instance tensor0SModelNormedAddCommGroup_local {nn : ℕ} :
    NormedAddCommGroup (Tensor0SBundle.Tensor0SModel nn ℝ E) := inferInstance

private instance tensor0SModelNormedSpace_local {nn : ℕ} :
    NormedSpace ℝ (Tensor0SBundle.Tensor0SModel nn ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace nn

private theorem contMDiffWithinAt_curriedSection_prod_full {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (n + 1) I p.1)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace (n + 1) I x) p.1 (T p)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p.1
        (tensor0S_curry (I := I) (M := M) n p.1 (T p))) s p₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E) (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p) p₀.1 p.1 hb
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p.1, tensor0S_curry (I := I) (M := M) n p.1 (T p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p⟩).2)
    exact hpt
  · have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p₀) p₀.1 p₀.1 (mem_baseSet_trivializationAt _ _ _)
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀⟩).2)
    exact hpt

private theorem contMDiffWithinAt_section_apply_prod_full : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace n I p.1)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1 (T p)) s p₀)
    (v : Fin n → ∀ p : M × ℝ, TangentSpace I p.1)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (T p) (fun i => v i p)) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p) p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p₀) p₀.1 p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀) 0)) = (T p₀) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀) 0)) 0 = (T p₀) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p₀) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_prod_full (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1
            ((tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => tensor0S_curry (I := I) (M := M) n p.1 (T p))
        (v := fun p : M × ℝ => v 0 p)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod_full n
      (s := s) (p₀ := p₀)
      (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : M × ℝ) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · change Tensor0SBundle.Tensor0SSpace.toModel (T p₀) (fun i : Fin (n + 1) => v i p₀) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)) (v 0 p₀))
          (fun i : Fin n => v i.succ p₀)
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

private theorem deTurckRHSField_realizePath_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ}
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) q.2
        (deTurckRHSField (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ (F q.1) hδ_lt (hδ q.1)) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨s₀, x₀⟩ ⟨hs₀, _⟩
  refine ⟨(Set.univ : Set ℝ) ×ˢ (chartAt H x₀).source,
    isOpen_univ.prod (chartAt H x₀).open_source,
    ⟨Set.mem_univ _, mem_chart_source H x₀⟩, ?_⟩
  have hinter : (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) ∩
      ((Set.univ : Set ℝ) ×ˢ (chartAt H x₀).source) =
      Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.univ_inter]
  rw [hinter]
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  set α : M := p₀.2 with hα
  set Bb := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBb
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  have hgood : Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α ∈
      nhdsWithin p₀ (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) := by
    have hp₀_good : p₀ ∈ Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α := by
      refine ⟨hp₀.1, ?_⟩
      exact self_mem_chartLeviCivitaGoodSet (I := I) α
    have h := inter_mem_nhdsWithin
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source)
      ((isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α)).mem_nhds
        (⟨Set.mem_univ _, by
            exact self_mem_chartLeviCivitaGoodSet (I := I) α⟩ :
          p₀ ∈ (Set.univ : Set ℝ) ×ˢ chartLeviCivitaGoodSet (I := I) α))
    refine Filter.mem_of_superset h ?_
    rintro q ⟨hq1, hq2⟩
    exact ⟨hq1.1, hq2.2⟩
  have hcoord : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => Bb.repr
          (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 σ)
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) p₀ := by
    intro σ
    have hP1 := jointChartDeTurckRicciRHS_alongChart_contMDiffOn (I := I) g_bg T gfam hJ
      α (σ 0) (σ 1)
    refine ((hP1 p₀ ⟨hp₀.1, self_mem_chartLeviCivitaGoodSet (I := I) α⟩).mono_of_mem_nhdsWithin hgood).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hgood] with q hq
      obtain ⟨hqt, hqgood⟩ := hq
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam q.1) q.2)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ q.2
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      have hframe : ∀ i : Fin 2,
          (trivializationAt E (TangentSpace I) α).symmL ℝ q.2 ((chartModelBasis E) (σ i)) =
            chartBasisVecFiber (I := I) α (σ i) q.2 :=
        fun i => by rw [chartBasisVecFiber, Trivialization.symmL_apply]
      rw [hframe 0, hframe 1]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (gfam q.1) g_bg α (σ 0) (σ 1) hqgood]
    · have hp₀good : p₀.2 ∈ chartLeviCivitaGoodSet (I := I) α := by
        exact self_mem_chartLeviCivitaGoodSet (I := I) α
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.2
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      have hframe : ∀ i : Fin 2,
          (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.2 ((chartModelBasis E) (σ i)) =
            chartBasisVecFiber (I := I) α (σ i) p₀.2 :=
        fun i => by rw [chartBasisVecFiber, Trivialization.symmL_apply]
      rw [hframe 0, hframe 1]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (gfam p₀.1) g_bg α (σ 0) (σ 1) hp₀good]
  have hpi : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun q : ℝ × M => (Bb.repr
        (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) p₀ :=
    contMDiffWithinAt_pi_space.2 (fun σ => hcoord σ)
  have hsymm : ContMDiff 𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ)
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun c : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ => Bb.equivFun.symm c) :=
    (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  refine (hsymm.contMDiffAt.comp_contMDiffWithinAt p₀ hpi).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q _
    simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm
  · simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p₀.2, deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p₀.2, deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm

private theorem contMDiff_constOfIsEmpty_tensor0S_section :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffAt_fst, ?_⟩
  have hconst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) ∞
      (fun _ : M × ℝ =>
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) :
          Tensor0SBundle.Tensor0SModel 0 ℝ E)) p₀ :=
    contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards with p
  rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M)
    (fun _ : M => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) p₀.1 p.1]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [show ((Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
        Tensor0SBundle.Tensor0SSpace 0 I p.1) 0) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
              Tensor0SBundle.Tensor0SSpace 0 I p.1) 0 from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

private theorem chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ} :
    ∀ (n : ℕ)
    (TT SS : M × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (_hT : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => (TT p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (_hS : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => (SS p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1 (TT p) (SS p))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ((TT p) (fun i => Fin.elim0 i)) * ((SS p) (fun i => Fin.elim0 i)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i; exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => (TT p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (TT p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (TT p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hT0
      have hS_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => (SS p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (SS p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (SS p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hS0
      exact hT_smooth.mul hS_smooth
  | succ n ih =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (n + 1) g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix (I := I) g α p.1)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1
                    ((TT p).curryLeft ((chartModelBasis E) i))
                    ((SS p).curryLeft ((chartModelBasis E) j)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · have hinv := chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
        have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
          trivializationAt_baseSet_eq_chartAt_source (I := I) α
        rw [hbase_eq] at hinv
        exact hinv.comp contMDiffOn_fst (fun p hp => hp.1)
      · refine ih
            (fun p : M × ℝ => (TT p).curryLeft ((chartModelBasis E) i))
            (fun p : M × ℝ => (SS p).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((TT p).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (TT p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((SS p).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (SS p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hS ψ'

private theorem loweredCompose_zero_basis_eval_jointContMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (Tval : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (arm : M × ℝ → TensorRSModel 0 2 ℝ E)
    (harm : ∀ p : M × ℝ,
      arm p (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p))
    (hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Tval p))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (φ : Fin (0 + 2) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  have heval : ∀ p : M × ℝ,
      (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p)
          (fun j : Fin 2 => chartBasisVecFiber (I := I) α
            (φ (Fin.natAdd 0 j)) p.1) := by
    intro p
    rw [loweredCompose_apply, lowerAllUpperIndices_apply, separableFormAt_zero, harm p]
    congr 1
  refine ContMDiffOn.congr ?_ (fun p _ => heval p)
  have hv : ∀ j : Fin 2, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro j
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartBasisVec_jointContMDiffOn (I := I) α (φ (Fin.natAdd 0 j))
    exact h.mono (Set.prod_mono (subset_refl _) (Set.subset_univ _))
  intro p hp
  exact contMDiffWithinAt_section_apply_prod_full 2 (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
    (p₀ := p) Tval (hTval p hp)
    (fun j p => chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1)
    (fun j => hv j p hp)

private theorem deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i).toFun
            p.1)
          ((deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  have hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T gfam :=
    jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
      g₀ hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hRHS_swap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hbase := deTurckRHSField_realizePath_jointContMDiffOn (I := I) g₀ g_bg F hδ_lt hδ hJ
    have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_snd.prodMk contMDiffOn_fst
    have hmaps : Set.MapsTo (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
      rintro ⟨x, t⟩ ⟨_, ht⟩; exact ⟨ht, Set.mem_univ _⟩
    exact hbase.comp hswap hmaps
  set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
    with heig_def
  set recon : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t) with hrecon_def
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  rw [hinter]
  set α : M := x₀ with hα
  have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          (eig.toFun p.1) ((recon p.2).toFun p.1) =
        chartTensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have harm_eig : ∀ p : M × ℝ,
      eig.toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro p
    rfl
  have hTval_eig : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
      (I := I) (M := M) g₀ 0 2 i
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
          (E := fun z : M => TensorRSSpace 0 2 I z) p.1 (eig.toSection p.1)) :=
      heigM.comp contMDiff_fst
    have happ := ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => (eig.toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      heigP hconst
    refine (happ.contMDiffOn).congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have hcoeff_eig : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => eig.toFun p.1) harm_eig hTval_eig φ
  have harm_recon : ∀ p : M × ℝ,
      (recon p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam p.2) p.1) := by
    intro p
    have hl : (recon p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((deTurckRHSSection (I := I) g_bg (gfam p.2)).toSection p.1
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := rfl
    rw [hl]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [deTurckRHSSection_toModel_apply, ← deTurckRHSField_toModel_apply]
  have hcoeff_recon : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro φ
    refine loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => deTurckRHSField (I := I) g_bg (gfam p.2) p.1)
      (fun p => (recon p.2).toFun p.1) harm_recon ?_ φ
    exact hRHS_swap.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args (I := I) (M := M) g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1))
    hcoeff_eig hcoeff_recon

end RealizePathJointSmoothness

private theorem deTurckRemainder_pathCoeff_timeContDiff
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T) := by
  classical
  intro i
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hsplit : ∀ t : ℝ,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i
          - tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i := by
    intro t
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
          = deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
            - rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := by
      rfl
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  refine ContDiffOn.congr ?_ (fun t _ => hsplit t)
  refine ContDiffOn.sub ?_ ?_
  · have hbridge : ∀ t : ℝ,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
          (inner ℝ (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
            (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) : ℝ) := by
      intro t
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2]
    refine ContDiffOn.congr ?_ (fun t _ => hbridge t)
    exact DifferentialGeometry.Integral.L2.contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
      (I := I) (M := M) g₀
      (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
      (fun t => deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))
      (deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i)
  · have hraw : ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -i.lambda * φ i t := by
      intro t ht
      rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i,
        hcoeff t ht i]
    refine ContDiffOn.congr ?_ (fun t ht => hraw t ht)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn

private theorem iteratedPartialSnd_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ∀ j : ℕ, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  intro j
  induction j generalizing f with
  | zero =>
      refine hf.congr ?_
      intro p _
      rw [iteratedDerivWithin_zero]
  | succ n ih =>
      have hderiv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ =>
            derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        DifferentialGeometry.partialSnd_contMDiffOn_Icc f hf
      have hih := ih (fun x s => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) s) hderiv
      refine hih.congr ?_
      intro p _
      rw [iteratedDerivWithin_succ']

private theorem clm_comm_iteratedDerivWithin {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (γ : ℝ → F) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hγ : ContDiffWithinAt ℝ ∞ γ (Set.Icc (0 : ℝ) T) t) (j : ℕ) :
    iteratedDerivWithin j (fun s => L (γ s)) (Set.Icc (0 : ℝ) T) t =
      L (iteratedDerivWithin j γ (Set.Icc (0 : ℝ) T) t) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hcomp : (fun s => L (γ s)) = L ∘ γ := rfl
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hcomp,
    L.iteratedFDerivWithin_comp_left hγ hUD ht (by exact_mod_cast le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedDerivWithin_eq_iteratedFDerivWithin]
  rfl

private theorem reconChartRepr_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M =>
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  have hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T gfam :=
    jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
      g₀ hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hRHS_swap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hbase := deTurckRHSField_realizePath_jointContMDiffOn (I := I) g₀ g_bg F hδ_lt hδ hJ
    have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_snd.prodMk contMDiffOn_fst
    have hmaps : Set.MapsTo (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
      rintro ⟨x, t⟩ ⟨_, ht⟩; exact ⟨ht, Set.mem_univ _⟩
    exact hbase.comp hswap hmaps
  have hFieldRepr : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) 2 α
          (fun z : M => deTurckRHSField (I := I) g_bg (gfam p.2) z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hbase : p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet := by
      change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
      rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
        TangentBundle.trivializationAt_baseSet (I := I) α]
      exact hx
    have hsub : ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) ⊆
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun q hq => ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
          TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p :=
      (hRHS_swap p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
        TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hbase
    have hrepr := ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
        TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p)
      (e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α) hsource).mp hFwithin).2
    refine hrepr.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      obtain ⟨hqx, _⟩ := hq
      have hqbase : q.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet := by
        change q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        exact hqx
      rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hqbase]
    · rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbase]
  set Lconst : Tensor0SBundle.Tensor0SModel 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    ContinuousLinearMap.smulRightL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      with hLconst
  have hLsmooth : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞ (fun v => Lconst v) :=
    Lconst.contMDiff
  refine (hLsmooth.comp_contMDiffOn hFieldRepr).congr ?_
  intro p hp
  obtain ⟨hx, _⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
      TangentBundle.trivializationAt_baseSet (I := I) α]
    exact hx
  apply ContinuousLinearMap.ext
  intro D
  have hsec : (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).symmL ℝ p.1 D) =
      ((continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap D) •
        deTurckRHSField (I := I) g_bg (gfam p.2) p.1 := by
    have hsymm0 := Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) α p.1 hxbase D
    have hcurry : ((continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap D)
        = D 0 := by
      change continuousMultilinearCurryFin0 ℝ E ℝ D = D 0
      rw [continuousMultilinearCurryFin0_apply]
    rw [hcurry]
    change (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) p.1).smulRight
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).symmL ℝ p.1 D) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply]
    exact congrArg (· • deTurckRHSField (I := I) g_bg (gfam p.2) p.1) hsymm0
  rw [Function.comp_apply,
    DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply_model
      (I := I) 0 2 α
      (fun z : M => (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z)
      hxbase D,
    hsec, map_smul, hLconst,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    tensor0SChartE_section_repr_apply]

private theorem reconSec_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  have hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T gfam :=
    jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
      g₀ hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hRHS_swap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hbase := deTurckRHSField_realizePath_jointContMDiffOn (I := I) g₀ g_bg F hδ_lt hδ hJ
    have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_snd.prodMk contMDiffOn_fst
    have hmaps : Set.MapsTo (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
      rintro ⟨x, t⟩ ⟨_, ht⟩; exact ⟨ht, Set.mem_univ _⟩
    exact hbase.comp hswap hmaps
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M =>
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass α
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1,
      (deTurckRHSReconSection (I := I) g₀ g_bg (F p₀.2) hδ_lt (hδ p₀.2)).toSection p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1,
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1⟩).2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
    refine (hCR p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hpx
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

private theorem vec_iteratedPartialSnd_contMDiffOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Vf : M → ℝ → V) {T : ℝ} (hT : 0 < T)
    (hVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞ (fun p : M × ℝ => Vf p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set A : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv with hA
  have hAVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
      (fun p : M × ℝ => A (Vf p.1 p.2)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    (A.toContinuousLinearMap.contMDiff.comp_contMDiffOn hVf)
  have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex ℝ V,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have hfi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => A (Vf p.1 p.2) i) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.1 hAVf i
    exact iteratedPartialSnd_contMDiffOn_Icc (fun x s => A (Vf x s) i) hfi j
  have hkey : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => A.symm
        (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hpi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
        (fun p : M × ℝ => (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.2 hcoord
    exact A.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  refine hkey.congr ?_
  intro p hp
  obtain ⟨_, hs⟩ := hp
  have hfiber : ContDiffWithinAt ℝ ∞ (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2 := by
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (p.1, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := p.1)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
    have hcomp := hVf.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp p.2 hs
  have hcomm : (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2)
      = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) := by
    have hAcomm : iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2
        = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin A.toContinuousLinearMap (fun s => Vf p.1 s) hT hs hfiber j
    funext i
    have hfiberA : ContDiffWithinAt ℝ ∞ (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2 :=
      A.toContinuousLinearMap.contDiff.comp_contDiffWithinAt hfiber
    have hproj : iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2
        = (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
            (iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
        (fun s => A (Vf p.1 s)) hT hs hfiberA j
    rw [hproj, hAcomm]
    rfl
  rw [hcomm]
  exact (A.symm_apply_apply _).symm

private theorem fiber_contDiffOn_Icc_recon
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (x : M) :
    ContDiffOn ℝ ∞ (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have hcomp := hf.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

private theorem hasDerivWithinAt_integral_param_Icc_recon
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => ∫ x, f x t ∂μ)
      (∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ) (Set.Icc (0 : ℝ) T) t₀ := by
  set s : Set ℝ := Set.Icc (0 : ℝ) T with hs_def
  have hconv : Convex ℝ s := convex_Icc 0 T
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hT
  set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) s t with hFd
  have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hf.continuousOn
  have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := partialSnd_contMDiffOn_Icc f hf
  have hFd_cont : ContinuousOn (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hFd_joint.continuousOn
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ s) :=
    isCompact_univ.prod (isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont
  have hfiber_deriv : ∀ x : M, ∀ y ∈ s, HasDerivWithinAt (fun u => f x u) (Fd x y) s y := by
    intro x y hy
    have hcd : ContDiffOn ℝ ∞ (fun u : ℝ => f x u) s := fiber_contDiffOn_Icc_recon f hf x
    exact ((hcd.differentiableOn (by simp) y hy)).hasDerivWithinAt
  have hfiber : ∀ x : M, HasDerivWithinAt (fun u => f x u) (Fd x t₀) s t₀ :=
    fun x => hfiber_deriv x t₀ ht₀
  have hbound : ∀ x : M, ∀ t ∈ s, ‖f x t - f x t₀‖ ≤ C * ‖t - t₀‖ := by
    intro x t ht
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => hfiber_deriv x y hy) (fun y hy => ?_) hconv ht₀ ht
    exact hC (x, y) ⟨Set.mem_univ _, hy⟩
  have hf_slice_cont : ∀ t ∈ s, Continuous (fun x : M => f x t) := by
    intro t ht
    have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ s) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have := (hf_cont.comp harg hmaps)
    rw [continuousOn_univ] at this
    exact this
  have hf_int : ∀ t ∈ s, Integrable (fun x : M => f x t) μ := by
    intro t ht
    exact integrableOn_univ.mp
      ((hf_slice_cont t ht).continuousOn.integrableOn_compact isCompact_univ)
  set G : ℝ → ℝ := fun t => ∫ x, f x t ∂μ with hG
  set G' : ℝ := ∫ x, Fd x t₀ ∂μ with hG'
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope_eq : ∀ t : ℝ, t ∈ s \ {t₀} →
      slope G t₀ t = ∫ x, slope (fun u => f x u) t₀ t ∂μ := by
    intro t ht
    have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
    rw [slope_def_field, hG]
    simp only []
    rw [show (∫ x, f x t ∂μ) - ∫ x, f x t₀ ∂μ
        = ∫ x, (f x t - f x t₀) ∂μ from
      (integral_sub (hf_int t ht.1) (hf_int t₀ ht₀)).symm]
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [slope_def_field, div_eq_inv_mul]
  have heq : (fun t => ∫ x, slope (fun u => f x u) t₀ t ∂μ) =ᶠ[𝓝[s \ {t₀}] t₀]
      slope G t₀ := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨s \ {t₀}, self_mem_nhdsWithin, fun t ht => (hslope_eq t ht).symm⟩
  refine Filter.Tendsto.congr' heq ?_
  · have hmeas : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        AEStronglyMeasurable (fun x : M => slope (fun u => f x u) t₀ t) μ := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      have : Continuous (fun x : M => slope (fun u => f x u) t₀ t) := by
        simp only [slope_def_field]
        exact ((hf_slice_cont t ht.1).sub (hf_slice_cont t₀ ht₀)).div_const _
      exact this.aestronglyMeasurable
    have hbnd : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        ∀ᵐ x ∂μ, ‖slope (fun u => f x u) t₀ t‖ ≤ C := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      refine Filter.Eventually.of_forall (fun x => ?_)
      have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
      have hpos : 0 < ‖t - t₀‖ := by
        rw [norm_pos_iff]; exact sub_ne_zero.mpr htne
      rw [slope_def_field, norm_div, div_le_iff₀ hpos]
      exact hbound x t ht.1
    have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
        (fun t => slope (fun u => f x u) t₀ t) (𝓝[s \ {t₀}] t₀)
        (𝓝 (Fd x t₀)) :=
      Filter.Eventually.of_forall (fun x => (hasDerivWithinAt_iff_tendsto_slope.mp (hfiber x)))
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : M => C)
      (F := fun t x => slope (fun u => f x u) t₀ t)
      (f := fun x => Fd x t₀)
      hmeas hbnd (integrable_const C) hlim
    simpa [hG'] using this

private theorem iteratedDerivWithin_integral_param_Icc
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (j : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) t₀ =
          ∫ x, iteratedDerivWithin j (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro j
  induction j with
  | zero =>
      intro f _ t₀ _
      simp only [iteratedDerivWithin_zero]
  | succ n ih =>
      intro f hf t₀ ht₀
      rw [iteratedDerivWithin_succ']
      set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) t
        with hFd
      have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := partialSnd_contMDiffOn_Icc f hf
      have hderiv_eqOn : Set.EqOn (derivWithin (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
          (fun t => ∫ x, Fd x t ∂μ) (Set.Icc (0 : ℝ) T) := by
        intro t ht
        exact (hasDerivWithinAt_integral_param_Icc_recon μ f hT hf ht).derivWithin (hUD t ht)
      rw [iteratedDerivWithin_congr hderiv_eqOn ht₀]
      rw [ih Fd hFd_joint t₀ ht₀]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (iteratedDerivWithin_succ').symm

set_option linter.unusedVariables false in
private theorem partialSnd_set_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ} (U : Set M)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt T 0 with hT0 | hT0
  · have hzero : Set.EqOn
        (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (fun _ : M × ℝ => (0 : ℝ)) (U ×ˢ Set.Icc (0 : ℝ) T) := by
      intro p hp
      have hnacc : ¬ AccPt p.2 (Filter.principal (Set.Icc (0 : ℝ) T)) := by
        rw [accPt_principal_iff_nhdsWithin]
        have hempty : Set.Icc (0 : ℝ) T \ {p.2} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hy.2 (Set.mem_singleton_iff.mpr
            ((Set.subsingleton_Icc_of_ge hT0) hy.1 hp.2))
        rw [hempty, nhdsWithin_empty]
        exact not_neBot.mpr rfl
      exact derivWithin_zero_of_not_accPt hnacc
    exact (contMDiffOn_const (c := (0 : ℝ))).congr hzero
  have hUM : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) T) :=
    (uniqueDiffOn_Icc hT0).uniqueMDiffOn
  have hrw : (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) =
      fun p : M × ℝ =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact (fderivWithin_derivWithin (𝕜 := ℝ) (f := fun s => f p.1 s)
      (s := Set.Icc (0 : ℝ) T) (x := p.2)).symm
  rw [hrw, contMDiffOn_infty]
  intro n p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n + 1 : WithTop ℕ∞)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨hq.1.1, hq.2⟩
    have hcomp := (hf (p₀.1, p₀.2) ⟨hp₀.1, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
    exact hcomp.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞))
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := U ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := U ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (n : WithTop ℕ∞) + 1) (m := (n : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

private theorem iteratedPartialSnd_set_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ} (U : Set M)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ∀ j : ℕ, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  intro j
  induction j generalizing f with
  | zero =>
      refine hf.congr ?_
      intro p _
      rw [iteratedDerivWithin_zero]
  | succ n ih =>
      have hderiv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
          (U ×ˢ Set.Icc (0 : ℝ) T) :=
        partialSnd_set_contMDiffOn_Icc f U hf
      have hih := ih (fun x s => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) s) hderiv
      refine hih.congr ?_
      intro p _
      rw [iteratedDerivWithin_succ']

private theorem vec_iteratedPartialSnd_set_contMDiffOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {T : ℝ} (U : Set M)
    (Vf : M → ℝ → V)
    (hT : 0 < T)
    (hVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞ (fun p : M × ℝ => Vf p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set A : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv with hA
  have hAVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
      (fun p : M × ℝ => A (Vf p.1 p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
    (A.toContinuousLinearMap.contMDiff.comp_contMDiffOn hVf)
  have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex ℝ V,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)
        (U ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have hfi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => A (Vf p.1 p.2) i) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.1 hAVf i
    exact iteratedPartialSnd_set_contMDiffOn_Icc (fun x s => A (Vf x s) i) U hfi j
  have hkey : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => A.symm
        (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2))
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
    have hpi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
        (fun p : M × ℝ => (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.2 hcoord
    exact A.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  refine hkey.congr ?_
  intro p hp
  obtain ⟨hpU, hs⟩ := hp
  have hfiber : ContDiffWithinAt ℝ ∞ (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2 := by
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (p.1, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := p.1)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hpU, hu⟩
    have hcomp := hVf.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp p.2 hs
  have hcomm : (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2)
      = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) := by
    have hAcomm : iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2
        = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin A.toContinuousLinearMap (fun s => Vf p.1 s) hT hs hfiber j
    funext i
    have hfiberA : ContDiffWithinAt ℝ ∞ (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2 :=
      A.toContinuousLinearMap.contDiff.comp_contDiffWithinAt hfiber
    have hproj : iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2
        = (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
            (iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
        (fun s => A (Vf p.1 s)) hT hs hfiberA j
    rw [hproj, hAcomm]
    rfl
  rw [hcomm]
  exact (A.symm_apply_apply _).symm

private theorem deTurckRHSReconSection_timeJet_jointSmooth_section
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (j : ℕ) :
    ∃ Rjt : ℝ → SmoothCcTensor g₀ 0 2,
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
          iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t =
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Rjt p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set Rec : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun s => deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s) with hRec
  have hReconSec := reconSec_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
    φ hφ_smooth hcoeff hmodemass
  set jetD : M → ℝ → Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    fun x t => iteratedDerivWithin j (fun s => (Rec s).toFun x) (Set.Icc (0 : ℝ) T) t
      with hjetD

  have hfiberRepr : ∀ (α : M) (x : M), x ∈ (chartAt H α).source →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContDiffWithinAt ℝ ∞
        (fun s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x)
        (Set.Icc (0 : ℝ) T) t := by
    intro α x hx t ht
    have hCR := reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
      φ hφ_smooth hcoeff hmodemass α
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hx, hu⟩
    have hcomp := hCR.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp t ht
  have hfiberSec : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContDiffWithinAt ℝ ∞ (fun s => (Rec s).toFun x) (Set.Icc (0 : ℝ) T) t := by
    intro x t ht
    set α : M := x with hα
    have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
    have hxRSbase : x ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hxsrc
    have hrepr := hfiberRepr α x hxsrc t ht
    set L : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
      (Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) 0 2 x).comp
        (DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel (I := I) 0 2 α x)
      with hL
    have hLeq : ∀ s : ℝ, L
        (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x) = (Rec s).toFun x := by
      intro s
      rw [hL, ContinuousLinearMap.comp_apply,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
      have hfib : DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel
            (I := I) 0 2 α x
            ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt ℝ x
              ((Rec s).toSection x)) = (Rec s).toSection x := by
        rw [DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel]
        exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hxRSbase ((Rec s).toSection x)
      rw [hfib]
      rfl
    refine (L.contDiff.comp_contDiffWithinAt hrepr).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s _
      simp only [Function.comp_apply]
      exact (hLeq s).symm
    · simp only [Function.comp_apply]
      exact (hLeq t).symm

  have hChartCommute : ∀ (α : M) (x : M), x ∈ (chartAt H α).source → ∀ t ∈ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        iteratedDerivWithin j
          (fun s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x)
          (Set.Icc (0 : ℝ) T) t := by
    intro α x hx t ht
    have hxRSbase : x ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hx
    set Φ : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt ℝ x).comp
        ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
      with hΦ
    have hΦeq : ∀ s : ℝ, Φ ((Rec s).toFun x) =
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x := by
      intro s
      rw [hΦ, ContinuousLinearMap.comp_apply,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
      have hsymm : ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
          ((Rec s).toFun x) = (Rec s).toSection x := by
        change (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
            ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x)
              ((Rec s).toSection x)) = (Rec s).toSection x
        exact (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
          (I := I) 0 2 x).symm_apply_apply _
      rw [hsymm]
    have hΦLHS : DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        Φ (jetD x t) := by
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hΦ,
        ContinuousLinearMap.comp_apply]
      rfl
    rw [hΦLHS]
    have hcomm := clm_comm_iteratedDerivWithin Φ (fun s => (Rec s).toFun x) hT ht
      (hfiberSec x t ht) j
    rw [hjetD]
    rw [← hcomm]
    refine iteratedDerivWithin_congr ?_ ht
    intro s _
    exact hΦeq s

  have hChartJet : ∀ α : M, ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z p.2)) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro α
    have hCR := reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
      φ hφ_smooth hcoeff hmodemass α
    have hvecjet := vec_iteratedPartialSnd_set_contMDiffOn_Icc
      (V := Tensor0SBundle.TensorRSModel 0 2 ℝ E) (U := (chartAt H α).source)
      (fun x s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x) hT hCR j
    refine hvecjet.congr ?_
    intro p hp
    obtain ⟨hx, ht⟩ := hp
    exact hChartCommute α p.1 hx p.2 ht

  have hJet : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_of_locally_contMDiffOn ?_
    rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
    refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
      (chartAt H x₀).open_source.prod isOpen_univ,
      ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
    set α : M := x₀ with hα
    have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
        ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
        (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
      ext ⟨y, u⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
      tauto
    rw [hsub_eq]
    intro p₀ hp₀
    obtain ⟨hx₀src, hs₀'⟩ := hp₀
    have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          rw [hα]; exact hx₀src
    have hsource : (⟨p₀.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p₀.1 p₀.2)⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hbaseSet
    have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
            ⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩).2)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
      refine ((hChartJet α) p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with p hp
        obtain ⟨hpx, _⟩ := hp
        have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
          change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
              ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
          refine ⟨?_, ?_⟩ <;>
            · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
              rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
                TangentBundle.trivializationAt_baseSet (I := I) α]
              exact hpx
        rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
          Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
      · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
          Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
    refine ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
      ⟨contMDiffWithinAt_fst, hfib⟩)

  have hSlice : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x
          (Tensor0SBundle.TensorRSSpace.ofModel (jetD x t))) := by
    intro t ht
    have harg : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun x : M => (x, t)) (Set.univ : Set M) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have hcomp := hJet.comp harg hmaps
    rw [contMDiffOn_univ] at hcomp
    exact hcomp

  set Rjt : ℝ → SmoothCcTensor g₀ 0 2 := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then
      { toSection := ⟨fun x => Tensor0SBundle.TensorRSSpace.ofModel (jetD x t), hSlice t ht⟩
        hasCompactSupport := HasCompactSupport.of_compactSpace _ }
    else 0 with hRjtDef
  have hRjtEq : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (0 : ℝ) T, Rjt t =
      { toSection := ⟨fun x => Tensor0SBundle.TensorRSSpace.ofModel (jetD x t), hSlice t ht⟩
        hasCompactSupport := HasCompactSupport.of_compactSpace _ } := by
    intro t ht
    rw [hRjtDef]; exact dif_pos ht
  have hRjtSection : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      (Rjt t).toSection x = Tensor0SBundle.TensorRSSpace.ofModel (jetD x t) := by
    intro t ht x
    rw [hRjtEq t ht]
    rfl
  have hRjtToFun : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      (Rjt t).toFun x = jetD x t := by
    intro t ht x
    have : (Rjt t).toFun x = Tensor0SBundle.TensorRSSpace.toModel ((Rjt t).toSection x) := rfl
    rw [this, hRjtSection t ht x, Tensor0SBundle.TensorRSSpace.toModel_ofModel]
  refine ⟨Rjt, ?_, ?_⟩
  ·
    intro i t ht
    haveI : IsFiniteMeasure
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
    set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
      with hμ
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig

    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl

    set fInt : M → ℝ → ℝ := fun x s =>
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (eig.toFun x) ((Rec s).toFun x) with hfInt
    have hfInt_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => fInt p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i

    have hLHS_eq : (fun s => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
        = fun s => ∫ x, fInt x s ∂μ := by
      funext s
      rw [hcoeffInt (Rec s)]
    rw [hLHS_eq]

    rw [iteratedDerivWithin_integral_param_Icc μ hT j fInt hfInt_joint t ht]

    have hfiberJet : ∀ x : M, iteratedDerivWithin j (fun s => fInt x s) (Set.Icc (0 : ℝ) T) t =
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (eig.toFun x) (jetD x t) := by
      intro x
      have hL := clm_comm_iteratedDerivWithin
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x))
        (fun s => (Rec s).toFun x) hT ht (hfiberSec x t ht) j
      simp only [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply] at hL
      rw [hfInt]
      rw [hjetD]
      exact hL

    have hRHS_eq : (∫ x, iteratedDerivWithin j (fun s => fInt x s) (Set.Icc (0 : ℝ) T) t ∂μ)
        = ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) ((Rjt t).toFun x) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      rw [hfiberJet x, hRjtToFun t ht x]
    rw [hRHS_eq, ← hcoeffInt (Rjt t)]
  ·
    refine hJet.congr ?_
    intro p hp
    obtain ⟨_, ht⟩ := hp
    rw [hRjtSection p.2 ht p.1]

section OneMinusConnLapNormSqContinuity

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

private theorem jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem oneMinusConnLapSmooth_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (Sfam : ℝ → SmoothCcTensor g₀ 0 2) (S : Set ℝ)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  have hraw := MetricRealization.rawTensorConnLapSmooth_jointContMDiffOn (I := I) (M := M)
    g₀ Sfam S hSfam
  have hsub := jointTotalSpaceRS_sub (I := I) (r := 0) (s := 2) (S := S)
    (fun p => (Sfam p.2).toSection p.1)
    (fun p => (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1)
    hSfam hraw
  refine hsub.congr ?_
  intro p _
  have hsec : (oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1
      = (Sfam p.2).toSection p.1
        - (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1 := by
    rw [show oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)
          = Sfam p.2 - rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2) from rfl,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsec]

private theorem oneMinusConnLapSmoothIter_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (Sfam : ℝ → SmoothCcTensor g₀ 0 2) (S : Set ℝ) (k : ℕ)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Sfam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction k with
  | zero => simpa using hSfam
  | succ k ih =>
      have hstep := oneMinusConnLapSmooth_section_jointContMDiffOn (I := I) (M := M) g₀
        (fun u => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Sfam u)) S ih
      refine hstep.congr ?_
      intro p _
      rfl

private theorem tensorInnerPointwise_diag_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Sfam p.2).toFun p.1) ((Sfam p.2).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  rw [hinter]
  set α : M := x₀ with hα
  have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Sfam p.2).toFun p.1) ((Sfam p.2).toFun p.1) =
        chartTensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have harm : ∀ p : M × ℝ,
      (Sfam p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro p
    rfl
  have hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        ((Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have hSfamP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
          Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
            Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      hSfam.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
    have happ := ContMDiffOn.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => ((Sfam p.2).toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      hSfamP (hconst.contMDiffOn)
    refine happ.congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have hcoeff_S : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => (Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (Sfam p.2).toFun p.1) harm hTval φ
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args (I := I) (M := M) g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
    hcoeff_S hcoeff_S

set_option linter.unusedVariables false in
private theorem deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (Rjt : ℝ → SmoothCcTensor g₀ 0 2) (k : ℕ)
    (hRjt : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Rjt p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContinuousOn
      (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))‖ ^ 2)
      (Set.Icc (0 : ℝ) T) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set Sfam : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t) with hSfam
  have hSfam_joint :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    oneMinusConnLapSmoothIter_section_jointContMDiffOn (I := I) (M := M) g₀ Rjt
      (Set.Icc (0 : ℝ) T) k hRjt
  have hdiag := tensorInnerPointwise_diag_section_jointContMDiffOn (I := I) (M := M) g₀ Sfam
    hSfam_joint
  have hnormeq : (fun t : ℝ => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
      = fun t : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x) ∂μ := by
    funext t
    rw [SmoothCcTensor.norm_toL2,
      Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self]
    rfl
  rw [hnormeq]
  have hcd := contDiffOn_integral_of_jointContMDiffOn_Icc (I := I) (M := M) μ
    (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise
      (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x)) hdiag
  exact hcd.continuousOn

end OneMinusConnLapNormSqContinuity

private theorem deTurckRHSReconCoeff_pathCoeff_timeJet_evenMass_uniformConst
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j k : ℕ), ∃ C : ℝ, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
          (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ C := by
  classical
  intro j k
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨Rjt, hRjt_coeff, hRjt_smooth⟩ :=
    deTurckRHSReconSection_timeJet_jointSmooth_section (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass j
  have hcont := deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn (I := I) (M := M)
    g₀ g_bg hT Rjt k hRjt_smooth
  obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT.le) hcont
  refine ⟨‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t₀))‖ ^ 2, ?_⟩
  intro i t ht
  rw [hRjt_coeff i t ht]
  have hweq : tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 =
      (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i) ^ 2 := by
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ hc (Rjt t) i k,
      mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [hweq]
  have hsummable := tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) hc
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t)))
  have hle_tsum : (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i) ^ 2 ≤
      ∑' i' : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i') ^ 2 :=
    hsummable.le_tsum i (fun i' _ => sq_nonneg _)
  rw [tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t)))] at hle_tsum
  refine le_trans hle_tsum ?_
  exact ht₀_max ht

private theorem deTurckRHSReconCoeff_pathCoeff_timeJet_allOrderMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i := by
  classical
  set jet : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hjet_def
  have huniform := deTurckRHSReconCoeff_pathCoeff_timeJet_evenMass_uniformConst
    (I := I) (M := M) g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  intro j σ _hσ
  set s : ℝ := (weylSobolevExp (E := E) : ℝ) + 1 with hs_def
  have hs : (weylSobolevExp (E := E) : ℝ) < s := by rw [hs_def]; linarith
  obtain ⟨k, hk⟩ := exists_nat_ge ((σ + s) / 2)
  have hk2 : σ + s ≤ ((2 * k : ℕ) : ℝ) := by
    push_cast
    have : (σ + s) / 2 ≤ (k : ℝ) := hk
    linarith
  obtain ⟨C, hC⟩ := huniform j k
  refine ⟨fun i => C * tensorSobolevWeight (I := I) (M := M) i (-s),
    (tensorEigen_summable_negpow (I := I) (M := M) g₀ s hs).mul_left C, ?_⟩
  intro i t ht
  have hnegnn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-s) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (-s)
  have hjsq : 0 ≤ (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 := sq_nonneg _
  have hmono : tensorSobolevWeight (I := I) (M := M) i (σ + s) ≤
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) :=
    tensorSobolevWeight_mono (I := I) (M := M) i hk2
  have hstep : tensorSobolevWeight (I := I) (M := M) i (σ + s) *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 :=
    mul_le_mul_of_nonneg_right hmono hjsq
  have hCbound : tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
      (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ C := hC i t ht
  have hadd : tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (-s) *
        tensorSobolevWeight (I := I) (M := M) i (σ + s) := by
    rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-s) (σ + s)]
    ring_nf
  calc tensorSobolevWeight (I := I) (M := M) i σ *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2
      = tensorSobolevWeight (I := I) (M := M) i (-s) *
          (tensorSobolevWeight (I := I) (M := M) i (σ + s) *
            (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2) := by
        rw [hadd]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (-s) * C := by
        refine mul_le_mul_of_nonneg_left ?_ hnegnn
        exact le_trans hstep hCbound
    _ = C * tensorSobolevWeight (I := I) (M := M) i (-s) := by ring

private theorem deTurckRemainder_pathCoeff_timeJet_allOrderMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set reconRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hreconRaw_def
  set rawRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F s))) i with hrawRaw_def
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hcpath_def
  have hsplit : ∀ i s, cpath i s = reconRaw i s - rawRaw i s := by
    intro i s
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
          = deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
            - rawTensorConnLapSmooth (I := I) g₀ 0 2 (F s) := rfl
    simp only [hcpath_def, hreconRaw_def, hrawRaw_def]
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  have hrecon_smooth : ∀ i, ContDiffOn ℝ ∞ (reconRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    have hbridge : ∀ s : ℝ, reconRaw i s =
        (inner ℝ (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
            (I := I) (M := M) g₀ 0 2 i)
          (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s)) : ℝ) := by
      intro s
      simp only [hreconRaw_def]
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2]
    refine ContDiffOn.congr ?_ (fun s _ => hbridge s)
    exact DifferentialGeometry.Integral.L2.contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
      (I := I) (M := M) g₀
      (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
      (fun s => deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      (deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i)
  have hraw_eqOn : ∀ i, Set.EqOn (rawRaw i)
      (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) := by
    intro i s hs
    simp only [hrawRaw_def]
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F s) i,
      hcoeff s hs i]
  have hraw_smooth : ∀ i, ContDiffOn ℝ ∞ (rawRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContDiffOn.congr ?_ (hraw_eqOn i)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn
  intro j σ hσ
  obtain ⟨Brecon, hBrecon_sum, hBrecon_le⟩ :=
    deTurckRHSReconCoeff_pathCoeff_timeJet_allOrderMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass j σ hσ
  obtain ⟨Braw, hBraw_sum, hBraw_le⟩ := hmodemass j (σ + 2) (by linarith)
  refine ⟨fun i => 2 * Brecon i + 2 * Braw i,
    (hBrecon_sum.mul_left 2).add (hBraw_sum.mul_left 2), ?_⟩
  · intro i t ht
    have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hcds : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (reconRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hrecon_smooth i) t ht).of_le (mod_cast le_top)
    have hcdr : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (rawRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hraw_smooth i) t ht).of_le (mod_cast le_top)
    have hderivEq : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
        iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t -
          iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t := by
      have hcongr : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => reconRaw i s - rawRaw i s)
            (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (fun s _ => hsplit i s) ht
      rw [hcongr]
      have hsub := iteratedDerivWithin_sub (f := reconRaw i) (g := rawRaw i)
        (n := j) ht hUDO hcds hcdr
      simpa only [Pi.sub_apply] using hsub
    have hrawDerivEq : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
        -i.lambda * iteratedDeriv j (φ i) t := by
      have hcongr : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (hraw_eqOn i) ht
      rw [hcongr,
        iteratedDerivWithin_const_mul ht hUDO (-i.lambda)
          ((hφ_smooth i).contDiffOn.of_le (mod_cast le_top) t ht),
        iteratedDerivWithin_eq_iteratedDeriv hUDO
          ((hφ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht]
    rw [hderivEq]
    set a : ℝ := iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t with ha_def
    set b : ℝ := iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t with hb_def
    have hwσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    have hsq : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
    have hweighted : tensorSobolevWeight (I := I) (M := M) i σ * (a - b) ^ 2 ≤
        2 * (tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hwσ_nn
      nlinarith [this]
    refine le_trans hweighted ?_
    have hterm_recon : tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2 ≤ Brecon i :=
      hBrecon_le i t ht
    have hterm_raw : tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2 ≤ Braw i := by
      have hbsq : b ^ 2 = i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2 := by
        rw [hrawDerivEq]; ring
      have hlam_sq_le : i.lambda ^ 2 ≤ tensorSobolevWeight (I := I) (M := M) i 2 := by
        have hw2 : tensorSobolevWeight (I := I) (M := M) i 2 =
            (1 + i.lambda) ^ 2 := by
          unfold tensorSobolevWeight
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hw2]
        have hlam_nn : 0 ≤ i.lambda := tensor_lambda_nonneg (I := I) (M := M) i
        nlinarith [hlam_nn]
      have hmm : tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          (iteratedDeriv j (φ i) t) ^ 2 ≤ Braw i := hBraw_le i t ht
      have hsplitw : tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
          tensorSobolevWeight (I := I) (M := M) i σ *
            tensorSobolevWeight (I := I) (M := M) i 2 :=
        tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2
      have hdjsq_nn : 0 ≤ (iteratedDeriv j (φ i) t) ^ 2 := sq_nonneg _
      calc tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ *
              (i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2) := by rw [hbsq]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (tensorSobolevWeight (I := I) (M := M) i 2 *
                (iteratedDeriv j (φ i) t) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hwσ_nn
            exact mul_le_mul_of_nonneg_right hlam_sq_le hdjsq_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv j (φ i) t) ^ 2 := by rw [hsplitw]; ring
        _ ≤ Braw i := hmm
    nlinarith [hterm_recon, hterm_raw]

theorem deTurckRemainder_path_coeff_timeJet_withMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
            (Set.Icc (0 : ℝ) T)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
              tensorSobolevWeight (I := I) (M := M) i σ *
                  (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i with hcpath_def
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (cpath i) (Set.Icc (0 : ℝ) T) :=
    deTurckRemainder_pathCoeff_timeContDiff (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hmass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i :=
    deTurckRemainder_pathCoeff_timeJet_allOrderMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hconstruct : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht
    refine exists_smoothCcTensor_of_allOrder_spectralMass (I := I) (M := M)
      g₀ (fun i => iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) (fun σ hσ => ?_)
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    exact ⟨B, hBs, fun i => hBle i t ht⟩
  choose! Rjet hRjet using hconstruct
  have hR_coeff : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i =
        iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht i
    exact hRjet j t ht i
  refine ⟨Rjet, hsmooth, ?_, ?_⟩
  · intro j i t ht
    rw [hR_coeff j t ht i]
  · intro j σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    rw [hR_coeff j t ht i]
    exact hBle i t ht

section FiniteOrderPairing

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

private theorem contMDiffWithinAt_curriedSection_prod_ofOrder {N : WithTop ℕ∞} {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (n + 1) I p.1)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace (n + 1) I x) p.1 (T p)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p.1
        (tensor0S_curry (I := I) (M := M) n p.1 (T p))) s p₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E) N
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p) p₀.1 p.1 hb
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p.1, tensor0S_curry (I := I) (M := M) n p.1 (T p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p⟩).2)
    exact hpt
  · have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p₀) p₀.1 p₀.1 (mem_baseSet_trivializationAt _ _ _)
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀⟩).2)
    exact hpt

private theorem contMDiffWithinAt_section_apply_prod_ofOrder {N : WithTop ℕ∞} : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace n I p.1)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1 (T p)) s p₀)
    (v : Fin n → ∀ p : M × ℝ, TangentSpace I p.1)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) N
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (T p) (fun i => v i p)) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) N
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p) p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p₀) p₀.1 p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀) 0)) = (T p₀) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀) 0)) 0 = (T p₀) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p₀) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_prod_ofOrder (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1
            ((tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := N)
        (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => tensor0S_curry (I := I) (M := M) n p.1 (T p))
        (v := fun p : M × ℝ => v 0 p)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod_ofOrder n
      (s := s) (p₀ := p₀)
      (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : M × ℝ) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · change Tensor0SBundle.Tensor0SSpace.toModel (T p₀) (fun i : Fin (n + 1) => v i p₀) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)) (v 0 p₀))
          (fun i : Fin n => v i.succ p₀)
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

private theorem chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ} :
    ∀ (n : ℕ)
    (TT SS : M × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (_hT : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (TT p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (_hS : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (SS p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1 (TT p) (SS p))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ((TT p) (fun i => Fin.elim0 i)) * ((SS p) (fun i => Fin.elim0 i)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i; exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (TT p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (TT p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (TT p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hT0
      have hS_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (SS p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (SS p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (SS p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hS0
      exact hT_smooth.mul hS_smooth
  | succ n ih =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (n + 1) g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix (I := I) g α p.1)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1
                    ((TT p).curryLeft ((chartModelBasis E) i))
                    ((SS p).curryLeft ((chartModelBasis E) j)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · have hinv := chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
        have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
          trivializationAt_baseSet_eq_chartAt_source (I := I) α
        rw [hbase_eq] at hinv
        exact (hinv.of_le hN).comp contMDiffOn_fst (fun p hp => hp.1)
      · refine ih
            (fun p : M × ℝ => (TT p).curryLeft ((chartModelBasis E) i))
            (fun p : M × ℝ => (SS p).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((TT p).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (TT p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((SS p).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (SS p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hS ψ'

private theorem loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (Tval : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (arm : M × ℝ → TensorRSModel 0 2 ℝ E)
    (harm : ∀ p : M × ℝ,
      arm p (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p))
    (hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Tval p))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (φ : Fin (0 + 2) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ =>
        (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  have heval : ∀ p : M × ℝ,
      (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p)
          (fun j : Fin 2 => chartBasisVecFiber (I := I) α
            (φ (Fin.natAdd 0 j)) p.1) := by
    intro p
    rw [loweredCompose_apply, lowerAllUpperIndices_apply, separableFormAt_zero, harm p]
    congr 1
  refine ContMDiffOn.congr ?_ (fun p _ => heval p)
  have hv : ∀ j : Fin 2, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro j
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartBasisVec_jointContMDiffOn (I := I) α (φ (Fin.natAdd 0 j))
    exact h.mono (Set.prod_mono (subset_refl _) (Set.subset_univ _))
  intro p hp
  exact contMDiffWithinAt_section_apply_prod_ofOrder 2
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
    (p₀ := p) Tval (hTval p hp)
    (fun j p => chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1)
    (fun j => (hv j p hp).of_le hN)

theorem tensorInnerPointwise_pair_section_jointContMDiffOn
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (A B : ℝ → SmoothCcTensor g₀ 0 2)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((B p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((A p.2).toFun p.1) ((B p.2).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  rw [hinter]
  set α : M := x₀ with hα
  have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((A p.2).toFun p.1) ((B p.2).toFun p.1) =
        chartTensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have hTvalOf : ∀ (C : ℝ → SmoothCcTensor g₀ 0 2),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((C p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
          ((C p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro C hC
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have hCP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
          Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
            Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((C p.2).toSection p.1))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      hC.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
    have happ := ContMDiffOn.clm_bundle_apply (𝕜 := ℝ) (n := N)
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => ((C p.2).toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      hCP ((hconst.contMDiffOn).of_le hN)
    refine happ.congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have harmOf : ∀ (C : ℝ → SmoothCcTensor g₀ 0 2) (p : M × ℝ),
      (C p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((C p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro C p
    rfl
  have hcoeff_A : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder (I := I) (M := M) hN g₀ α
      (fun p => (A p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (A p.2).toFun p.1) (harmOf A) (hTvalOf A hA) φ
  have hcoeff_B : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder (I := I) (M := M) hN g₀ α
      (fun p => (B p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (B p.2).toFun p.1) (harmOf B) (hTvalOf B hB) φ
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder (I := I) (M := M) hN g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1))
    hcoeff_A hcoeff_B

end FiniteOrderPairing

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
