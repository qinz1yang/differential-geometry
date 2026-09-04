import DifferentialGeometry.Analysis.Sobolev.Tensor.Fine.Projection
import DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Wkp.HigherOrderBounds
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem canonChi_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    HasCompactSupport
      (((canonicalFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (isClosed_tsupport _).isCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem canonChi_source
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    tsupport
        (((canonicalFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source := by
  intro x hx
  change x ∈ tsupport
      ((((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).chi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  change x ∈ (chartAt H z.1.1).source
  rw [← extChartAt_source (I := I)]
  exact ((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).chi_support z.2 hx).1

omit [NeZero (Module.finrank ℝ E)] in
theorem canonPsi_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    HasCompactSupport
      (((canonicalFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (isClosed_tsupport _).isCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem canonPsi_source
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    tsupport
        (((canonicalFlatPsi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source := by
  intro x hx
  change x ∈ tsupport
      ((((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).psi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  change x ∈ (chartAt H z.1.1).source
  rw [← extChartAt_source (I := I)]
  exact ((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).psi_support z.2 hx).1

omit [NeZero (Module.finrank ℝ E)] in
theorem canonPsi_one
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    {x : M}
    (hx : x ∈ tsupport
      (((canonicalFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ))) :
    ((canonicalFlatPsi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  change x ∈ tsupport
      ((((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).chi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  exact ((canonicalFineChartData (I := I) (M := M) rFine hr z.1.1).psi_one z.2)
    |>.self_of_nhdsSet x hx

def canonicalCutE
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) : EuclN → ℝ :=
  chartCutoffEuclidean (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (((canonicalFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalCut_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    ContDiff ℝ (⊤ : ℕ∞)
      (canonicalCutE (I := I) (M := M) rFine hr z) := by
  exact contDiff_etaEuclid (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (((canonicalFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonicalFlatChi (I := I) (M := M) rFine hr z).contMDiff
    (canonChi_compact (I := I) (M := M) rFine hr z)
    (canonChi_source (I := I) (M := M) rFine hr z)

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalCut_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    HasCompactSupport (canonicalCutE (I := I) (M := M) rFine hr z) := by
  exact hasCompactSupport_etaEuclid (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (((canonicalFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonChi_compact (I := I) (M := M) rFine hr z)
    (canonChi_source (I := I) (M := M) rFine hr z)

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalCut_support
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) :
    tsupport (canonicalCutE (I := I) (M := M) rFine hr z) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonicalFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  exact tsupport_etaEuclid_subset_chartImage (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (((canonicalFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonChi_compact (I := I) (M := M) rFine hr z)
    (canonChi_source (I := I) (M := M) rFine hr z)

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalCut_coord
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    {x : M}
    (hx : x ∈
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source) :
    canonicalCutE (I := I) (M := M) rFine hr z
        (toEuclidean (E := E)
          (extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) =
      ((canonicalFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x := by
  rw [canonicalCutE, etaEuclid_apply_of_mem (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    _ (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z) hx),
    symm_toEuclidean_symm_toEuclidean_extChartAt
      (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z) hx]

def canonicalCutMul
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (u : EuclN → ℝ) : EuclN → ℝ :=
  fun y => canonicalCutE (I := I) (M := M) rFine hr z y * u y

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalCutMul_support
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (u : EuclN → ℝ) :
    tsupport (canonicalCutMul (I := I) (M := M) rFine hr z u) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonicalFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (tsupport_mul_subset_left
    (f := canonicalCutE (I := I) (M := M) rFine hr z) (g := u)).trans
      (canonicalCut_support (I := I) (M := M) rFine hr z)

theorem canonicalCut_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p u Set.univ →
      MemWkp (d := Module.finrank ℝ E) k p
          (canonicalCutMul (I := I) (M := M) rFine hr z u) Set.univ ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
            (canonicalCutMul (I := I) (M := M) rFine hr z u) Set.univ ≤
          ENNReal.ofReal K *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p u Set.univ := by
  have hsmooth := canonicalCut_smooth (I := I) (M := M) rFine hr z
  have hcpt := canonicalCut_compact (I := I) (M := M) rFine hr z
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hsmooth hcpt k
  obtain ⟨K, hK, hKbound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E)
      k hp hp_top isOpen_univ hsmooth hC
      (fun j hj y _ => hCbound y j hj)
  refine ⟨K, hK, ?_⟩
  intro u hu
  refine ⟨?_, ?_⟩
  · exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E)
      k hp isOpen_univ hsmooth (fun j hj y _ => hCbound y j hj) hu
  · exact hKbound hu

omit [NeZero (Module.finrank ℝ E)] in
theorem modelRepack_mul
    (r s : ℕ) (c : EuclN → ℝ)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ) (y : EuclN) :
    modelRepack (E := E) r s (fun P y => c y * u P y) y =
      c y • modelRepack (E := E) r s u y := by
  classical
  unfold modelRepack
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro Idx _
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  rw [smul_smul]

noncomputable def canonicalEuclideanRepack
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ)
    (u : FineCompArray (E := E)
      (CanonicalFineFlatIndex (I := I) (M := M) rFine hr) r s) :
    RSTensorSection I M r s :=
  fun x =>
    ∑ a : CanonicalChartIndex (I := I) (M := M),
      ∑ z : CanonicalFineIndex (I := I) (M := M) rFine hr a.1,
        chartRepack (I := I) (M := M) r s a.1
          (fun P => canonicalCutMul (I := I) (M := M) rFine hr ⟨a, z⟩
            (u ⟨a, z⟩ P)) x

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRepack_cut
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ) :
    chartRepack (I := I) (M := M) r s
        (canonicalFlatBase (I := I) (M := M) rFine hr z)
        (fun P => canonicalCutMul (I := I) (M := M) rFine hr z (u P)) =
      fun x =>
        ((canonicalFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
          chartRepack (I := I) (M := M) r s
            (canonicalFlatBase (I := I) (M := M) rFine hr z) u x := by
  funext x
  by_cases hx : x ∈
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source
  · unfold chartRepack secModelPull
    simp only [dif_pos hx]
    unfold canonicalCutMul
    rw [modelRepack_mul (E := E) r s
      (canonicalCutE (I := I) (M := M) rFine hr z) u,
      canonicalCut_coord (I := I) (M := M) rFine hr z hx,
      ContinuousLinearMap.map_smul]
  · unfold chartRepack secModelPull
    simp only [dif_neg hx, smul_zero]

omit [NeZero (Module.finrank ℝ E)] in
theorem canonERepack_eq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ)
    (u : FineCompArray (E := E)
      (CanonicalFineFlatIndex (I := I) (M := M) rFine hr) r s) :
    canonicalEuclideanRepack (I := I) (M := M) rFine hr r s u =
      canonicalCutRepack (I := I) (M := M) rFine hr r s u := by
  classical
  funext x
  unfold canonicalEuclideanRepack canonicalCutRepack
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro z _
  exact congrFun
    (chartRepack_cut (I := I) (M := M) rFine hr r s ⟨a, z⟩ (u ⟨a, z⟩)) x

omit [NeZero (Module.finrank ℝ E)] in
theorem canonicalEuclidean_retract
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (S : RSTensorSection I M r s) :
    canonicalEuclideanRepack (I := I) (M := M) rFine hr r s
        (canonicalFineRaw (I := I) (M := M) rFine hr r s S) =
      S := by
  rw [canonERepack_eq (I := I) (M := M)]
  exact canonicalCut_retract (I := I) (M := M) rFine hr r s S

def fineTransCoeff
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) : M → ℝ :=
  fun x =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x *
      ((canonicalFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        transitionCoeff (E := E) (I := I) (M := M) r s
          (canonicalFlatBase (I := I) (M := M) rFine hr z) α P Q x

private def fineTransSupport
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) (α : M) : Set M :=
  tsupport
      (((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) ∩
    tsupport
      (((canonicalFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ))

omit [NeZero (Module.finrank ℝ E)] in
private theorem fineTransSupport_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) (α : M) :
    IsCompact (fineTransSupport (I := I) (M := M) rFine hr z α) :=
  (chartKernelCutoff_hasCompactSupport (I := I) (M := M) α).inter_right
    (isClosed_tsupport _)

omit [NeZero (Module.finrank ℝ E)] in
private theorem fineTransSupport_source
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) (α : M) :
    fineTransSupport (I := I) (M := M) rFine hr z α ⊆
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source :=
  fun _ hx => canonPsi_source (I := I) (M := M) rFine hr z hx.2

omit [NeZero (Module.finrank ℝ E)] in
private theorem fineTransSupport_target
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr) (α : M) :
    fineTransSupport (I := I) (M := M) rFine hr z α ⊆
      (chartAt H α).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source
    (I := I) (M := M) α hx.1

omit [NeZero (Module.finrank ℝ E)] in
private theorem fineTrans_zero_left
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) α :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x = 0 := by
  simp only [fineTransCoeff, hx, zero_mul]

omit [NeZero (Module.finrank ℝ E)] in
private theorem fineTrans_zero_right
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((canonicalFlatPsi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x = 0 := by
  rw [fineTransCoeff, hx, mul_zero, zero_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem fineTrans_support
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    tsupport (fineTransCoeff (I := I) (M := M)
        rFine hr r s z α P Q) ⊆
      fineTransSupport (I := I) (M := M) rFine hr z α := by
  refine closure_minimal ?_
    ((isClosed_tsupport _).inter (isClosed_tsupport _))
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨?_, ?_⟩
  · by_contra hleft
    exact hx (fineTrans_zero_left (I := I) (M := M)
      rFine hr r s z α P Q (image_eq_zero_of_notMem_tsupport hleft))
  · by_contra hright
    exact hx (fineTrans_zero_right (I := I) (M := M)
      rFine hr r s z α P Q (image_eq_zero_of_notMem_tsupport hright))

omit [NeZero (Module.finrank ℝ E)] in
theorem fineTrans_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport
      (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) :=
  HasCompactSupport.of_support_subset_isCompact
    (fineTransSupport_compact (I := I) (M := M) rFine hr z α)
    (fun _ hx => fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q (subset_tsupport _ hx))

omit [NeZero (Module.finrank ℝ E)] in
theorem fineTrans_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) := by
  classical
  intro x
  by_cases hx : x ∈
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source ∩
        (chartAt H α).source
  · have htarget :=
      ((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt (x := x)
    have hsource :=
      ((canonicalFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt (x := x)
    have hopen : IsOpen
        ((chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source ∩
          (chartAt H α).source) :=
      (chartAt H _).open_source.inter (chartAt H α).open_source
    have hcoeff :=
      (contMDiffOn_transitionCoeff (E := E) (I := I) (M := M)
        r s (canonicalFlatBase (I := I) (M := M) rFine hr z) α P Q x hx)
        |>.contMDiffAt (hopen.mem_nhds hx)
    unfold fineTransCoeff
    exact (htarget.mul hsource).mul hcoeff
  · have hxoff : x ∉ tsupport
        (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) := by
      intro hs
      have hcarrier := fineTrans_support (I := I) (M := M)
        rFine hr r s z α P Q hs
      exact hx ⟨fineTransSupport_source (I := I) (M := M)
        rFine hr z α hcarrier,
        fineTransSupport_target (I := I) (M := M) rFine hr z α hcarrier⟩
    refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const ?_
    filter_upwards [((isClosed_tsupport _).isOpen_compl.mem_nhds hxoff)] with y hy
    have hyoff : y ∉ Function.support
        (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) :=
      fun h => hy (subset_tsupport _ h)
    by_contra hne
    exact hyoff hne

def fineCoeffE
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  chartCutoffEuclidean (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)

omit [NeZero (Module.finrank ℝ E)] in
theorem fineCoeff_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fineCoeffE (I := I) (M := M) rFine hr r s z α P Q) := by
  apply contDiff_etaEuclid (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)
  · exact fineTrans_smooth (I := I) (M := M) rFine hr r s z α P Q
  · exact fineTrans_compact (I := I) (M := M) rFine hr r s z α P Q
  · exact (fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q).trans
        (fineTransSupport_source (I := I) (M := M) rFine hr z α)

omit [NeZero (Module.finrank ℝ E)] in
theorem fineCoeff_compact
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport
      (fineCoeffE (I := I) (M := M) rFine hr r s z α P Q) := by
  apply hasCompactSupport_etaEuclid (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)
  · exact fineTrans_compact (I := I) (M := M) rFine hr r s z α P Q
  · exact (fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q).trans
        (fineTransSupport_source (I := I) (M := M) rFine hr z α)

omit [NeZero (Module.finrank ℝ E)] in
theorem fineCoeff_apply
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {x : M}
    (hx : x ∈
      (chartAt H (canonicalFlatBase (I := I) (M := M) rFine hr z)).source) :
    fineCoeffE (I := I) (M := M) rFine hr r s z α P Q
        (toEuclidean (E := E)
          (extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) =
      fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x := by
  rw [fineCoeffE, etaEuclid_apply_of_mem (I := I) (M := M)
    (canonicalFlatBase (I := I) (M := M) rFine hr z) _
    (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z) hx),
    symm_toEuclidean_symm_toEuclidean_extChartAt
      (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z) hx]

theorem fineCoeff_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s k : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonicalFlatBase (I := I) (M := M) rFine hr z)) →
      MemWkp (d := Module.finrank ℝ E) k p
          (fun y => fineCoeffE (I := I) (M := M)
            rFine hr r s z α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M)
            (canonicalFlatBase (I := I) (M := M) rFine hr z)) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
            (fun y => fineCoeffE (I := I) (M := M)
              rFine hr r s z α P Q y * v y)
            (chartTargetEuclid (I := I) (M := M)
              (canonicalFlatBase (I := I) (M := M) rFine hr z)) ≤
          ENNReal.ofReal K *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M)
                (canonicalFlatBase (I := I) (M := M) rFine hr z)) := by
  classical
  have hsmooth := fineCoeff_smooth (I := I) (M := M)
    rFine hr r s z α P Q
  have hcpt := fineCoeff_compact (I := I) (M := M)
    rFine hr r s z α P Q
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hsmooth hcpt k
  obtain ⟨K, hK, hKbound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E)
      k hp hp_top
      (chartTargetEuclid_isOpen (I := I) (M := M)
        (canonicalFlatBase (I := I) (M := M) rFine hr z))
      hsmooth hC (fun j hj y _ => hCbound y j hj)
  refine ⟨K, hK, ?_⟩
  intro v hv
  refine ⟨?_, hKbound hv⟩
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E)
    k hp
    (chartTargetEuclid_isOpen (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z))
    hsmooth (fun j hj y _ => hCbound y j hj) hv

def fineSecTerm
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    (v : EuclN → ℝ) : EuclN → ℝ :=
  chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
    (chartPullback I
      (canonicalFlatBase (I := I) (M := M) rFine hr z)
      (fun y => fineCoeffE (I := I) (M := M)
        rFine hr r s z α P Q y * v y))

theorem fineTerm_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonicalFlatBase (I := I) (M := M) rFine hr z)) →
      tsupport v ⊆
          (fun x : M => toEuclidean (E := E)
            (extChartAt I
              (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
            tsupport
              (((canonicalFlatChi (I := I) (M := M) rFine hr z :
                C^∞⟮I, M; ℝ⟯) : M → ℝ)) →
      MemWkp (d := Module.finrank ℝ E) k p
          (fineSecTerm (I := I) (M := M)
            rFine hr r s z α P Q v)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
            (fineSecTerm (I := I) (M := M)
              rFine hr r s z α P Q v)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M)
                (canonicalFlatBase (I := I) (M := M) rFine hr z)) := by
  classical
  obtain ⟨K_mul, hK_mul, hmul⟩ :=
    fineCoeff_joint (I := I) (M := M)
      rFine hr r s k z α P Q hp hp_top
  obtain ⟨K_cross, hK_cross, hcross⟩ :=
    crossChartJointK (I := I) (M := M) k hp hp_top α
      (canonicalFlatBase (I := I) (M := M) rFine hr z)
      (K_α := tsupport
        (((canonicalFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (canonChi_compact (I := I) (M := M) rFine hr z)
      (canonChi_source (I := I) (M := M) rFine hr z)
  refine ⟨K_cross * K_mul, mul_pos hK_cross hK_mul, ?_⟩
  intro v hv hv_support
  have hv_mul := hmul hv
  have hprod_support :
      tsupport (fun y => fineCoeffE (I := I) (M := M)
          rFine hr r s z α P Q y * v y) ⊆
        (fun x : M => toEuclidean (E := E)
          (extChartAt I
            (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonicalFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    (tsupport_mul_subset_right
      (f := fineCoeffE (I := I) (M := M)
        rFine hr r s z α P Q) (g := v)).trans hv_support
  have hout := hcross hv_mul.1 hprod_support
  refine ⟨hout.1, ?_⟩
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
        (fineSecTerm (I := I) (M := M)
          rFine hr r s z α P Q v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal K_cross *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
          (fun y => fineCoeffE (I := I) (M := M)
            rFine hr r s z α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M)
            (canonicalFlatBase (I := I) (M := M) rFine hr z)) := hout.2
    _ ≤ ENNReal.ofReal K_cross *
        (ENNReal.ofReal K_mul *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M)
              (canonicalFlatBase (I := I) (M := M) rFine hr z))) :=
      mul_le_mul_right hv_mul.2 _
    _ = ENNReal.ofReal (K_cross * K_mul) *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonicalFlatBase (I := I) (M := M) rFine hr z)) := by
      rw [ENNReal.ofReal_mul hK_cross.le]
      simp only [mul_assoc]

omit [NeZero (Module.finrank ℝ E)] in
theorem fineCoeffEq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {v : EuclN → ℝ}
    (hv : tsupport v ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I
          (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
        tsupport
          (((canonicalFlatChi (I := I) (M := M) rFine hr z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ)))
    {x : M}
    (hx : x ∈
      (chartAt H
        (canonicalFlatBase (I := I) (M := M) rFine hr z)).source) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (transitionCoeff (E := E) (I := I) (M := M) r s
          (canonicalFlatBase (I := I) (M := M) rFine hr z) α P Q x *
          v (toEuclidean (E := E)
            (extChartAt I
              (canonicalFlatBase (I := I) (M := M) rFine hr z) x))) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (fineTransCoeff (I := I) (M := M)
          rFine hr r s z α P Q x *
          v (toEuclidean (E := E)
            (extChartAt I
              (canonicalFlatBase (I := I) (M := M) rFine hr z) x))) := by
  classical
  by_cases hρ :
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, zero_mul, zero_mul]
  by_cases hvx : v (toEuclidean (E := E)
      (extChartAt I
        (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) = 0
  · simp only [hvx, mul_zero]
  have hxα_support : x ∈ tsupport
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    subset_tsupport _ hρ
  have hcut :
      ((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 :=
    chartKernelCutoff_eqOn_one (I := I) (M := M) α hxα_support
  have hy_support := hv (subset_tsupport _ hvx)
  obtain ⟨w, hwχ, hcoord⟩ := hy_support
  have hw : w ∈
      (chartAt H
        (canonicalFlatBase (I := I) (M := M) rFine hr z)).source :=
    canonChi_source (I := I) (M := M) rFine hr z hwχ
  have hw_ext : w ∈
      (extChartAt I
        (canonicalFlatBase (I := I) (M := M) rFine hr z)).source := by
    rw [extChartAt_source]
    exact hw
  have hx_ext : x ∈
      (extChartAt I
        (canonicalFlatBase (I := I) (M := M) rFine hr z)).source := by
    rw [extChartAt_source]
    exact hx
  have hext :
      extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) w =
        extChartAt I (canonicalFlatBase (I := I) (M := M) rFine hr z) x :=
    (toEuclidean (E := E)).injective hcoord
  have hwx : w = x :=
    (extChartAt I
      (canonicalFlatBase (I := I) (M := M) rFine hr z)).injOn
        hw_ext hx_ext hext
  have hψ :
      ((canonicalFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
    rw [← hwx]
    exact canonPsi_one (I := I) (M := M) rFine hr z hwχ
  rw [fineTransCoeff, hcut, hψ]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem finePullEq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonicalFineFlatIndex (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ Q, tsupport (u Q) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I
          (canonicalFlatBase (I := I) (M := M) rFine hr z) x)) ''
        tsupport
          (((canonicalFlatChi (I := I) (M := M) rFine hr z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s
        (chartRepack (I := I) (M := M) r s
          (canonicalFlatBase (I := I) (M := M) rFine hr z) u)
        α P.1 P.2 =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        fineSecTerm (I := I) (M := M)
          rFine hr r s z α P Q (u Q) y) := by
  classical
  have hmem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ae_restrict_mem
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)
  filter_upwards [hmem] with y hy
  set x : M :=
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hxα : x ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [secComp_apply_mem (I := I) (M := M) r s _ α P.1 P.2 hy]
  unfold secCompPou
  by_cases hx : x ∈
      (chartAt H
        (canonicalFlatBase (I := I) (M := M) rFine hr z)).source
  · rw [chartRepack,
      secPull_raw_trans (E := E) (I := I) (M := M) r s
        (canonicalFlatBase (I := I) (M := M) rFine hr z) α
        (modelRepack (E := E) r s u) P ⟨hx, hxα⟩,
      Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Q _
    rw [modelRepack_proj (E := E) r s u Q]
    unfold fineSecTerm chartPushed
    rw [chartPullback_apply_of_mem (I := I) (M := M)
        (canonicalFlatBase (I := I) (M := M) rFine hr z) _ hx,
      fineCoeff_apply (I := I) (M := M)
        rFine hr r s z α P Q hx]
    exact fineCoeffEq (I := I) (M := M)
      rFine hr r s z α P Q (hu Q) hx
  · have hpull :
        chartRepack (I := I) (M := M) r s
          (canonicalFlatBase (I := I) (M := M) rFine hr z) u x = 0 := by
      unfold chartRepack secModelPull
      rw [dif_neg hx]
    unfold secCompRaw secTriv
    rw [hpull, ContinuousLinearMap.map_zero,
      ContinuousLinearMap.map_zero, mul_zero]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold fineSecTerm chartPushed
    rw [chartPullback_apply_of_notMem (I := I) (M := M)
      (canonicalFlatBase (I := I) (M := M) rFine hr z) _ hx, mul_zero]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
