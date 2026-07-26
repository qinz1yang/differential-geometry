import DifferentialGeometry.Analysis.Sobolev.Tensor.FineTensorProject
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpBoundK

/-!
# Sobolev reassembly from fine tensor blocks

This file supplies the analytic form of the exact fine-chart retraction.  A
local heat output is first multiplied by the middle cutoff `chi` in its source
Euclidean chart and then pulled back as a genuine tensor.  The outer cutoff
`psi`, which is one on `tsupport chi`, produces a globally smooth compactly
supported extension of every tensor transition coefficient.  Consequently
the transition formula is both exact and bounded without assuming that a heat
output remains in the smaller canonical POU support.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The middle and outer cutoff geometry -/

/-- The middle fine cutoff has compact support on the closed manifold. -/
theorem canonChi_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    HasCompactSupport
      (((canonFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (isClosed_tsupport _).isCompact

/-- The middle fine cutoff is supported inside its source chart. -/
theorem canonChi_src
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    tsupport
        (((canonFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source := by
  intro x hx
  change x ∈ tsupport
      ((((canonFineData (I := I) (M := M) rFine hr z.1.1).chi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  change x ∈ (chartAt H z.1.1).source
  rw [← extChartAt_source]
  exact ((canonFineData (I := I) (M := M) rFine hr z.1.1).chi_supp z.2 hx).1

/-- The outer fine cutoff has compact support on the closed manifold. -/
theorem canonPsi_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    HasCompactSupport
      (((canonFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (isClosed_tsupport _).isCompact

/-- The outer fine cutoff is supported inside its source chart. -/
theorem canonPsi_src
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    tsupport
        (((canonFlatPsi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source := by
  intro x hx
  change x ∈ tsupport
      ((((canonFineData (I := I) (M := M) rFine hr z.1.1).psi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  change x ∈ (chartAt H z.1.1).source
  rw [← extChartAt_source]
  exact ((canonFineData (I := I) (M := M) rFine hr z.1.1).psi_supp z.2 hx).1

/-- The outer cutoff is one on the topological support of the middle cutoff. -/
theorem canonPsi_one
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    {x : M}
    (hx : x ∈ tsupport
      (((canonFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ))) :
    ((canonFlatPsi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  change x ∈ tsupport
      ((((canonFineData (I := I) (M := M) rFine hr z.1.1).chi z.2 :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) at hx
  exact ((canonFineData (I := I) (M := M) rFine hr z.1.1).psi_one z.2)
    .self_of_nhdsSet x hx

/-! ## Euclidean middle-cutoff multiplication -/

/-- The middle cutoff pushed to its whole Euclidean source chart and extended
by zero. -/
def canonCutE
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) : EuclN → ℝ :=
  etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (((canonFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))

/-- The Euclidean middle cutoff is globally smooth. -/
theorem canonCut_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    ContDiff ℝ (⊤ : ℕ∞)
      (canonCutE (I := I) (M := M) rFine hr z) := by
  exact contDiff_etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (((canonFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonFlatChi (I := I) (M := M) rFine hr z).contMDiff
    (canonChi_cpt (I := I) (M := M) rFine hr z)
    (canonChi_src (I := I) (M := M) rFine hr z)

/-- The Euclidean middle cutoff has compact support. -/
theorem canonCut_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    HasCompactSupport (canonCutE (I := I) (M := M) rFine hr z) := by
  exact hasCompactSupport_etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (((canonFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonChi_cpt (I := I) (M := M) rFine hr z)
    (canonChi_src (I := I) (M := M) rFine hr z)

/-- The Euclidean middle cutoff is supported in the coordinate image of the
manifold middle support. -/
theorem canonCut_support
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    tsupport (canonCutE (I := I) (M := M) rFine hr z) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  exact tsupport_etaEuclid_subset_chartImage (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (((canonFlatChi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (canonChi_cpt (I := I) (M := M) rFine hr z)
    (canonChi_src (I := I) (M := M) rFine hr z)

/-- Evaluation of the Euclidean middle cutoff at the coordinate of a source
point. -/
theorem canonCut_coord
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    {x : M}
    (hx : x ∈
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source) :
    canonCutE (I := I) (M := M) rFine hr z
        (toEuclidean (E := E)
          (extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) x)) =
      ((canonFlatChi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x := by
  rw [canonCutE, etaEuclid_apply_of_mem (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    _ (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z) hx),
    symm_toEuclidean_symm_toEuclidean_extChartAt
      (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z) hx]

/-- Multiplication by the Euclidean middle cutoff. -/
def canonCutMul
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : EuclN → ℝ) : EuclN → ℝ :=
  fun y => canonCutE (I := I) (M := M) rFine hr z y * u y

/-- Middle-cutoff multiplication localizes every input into the coordinate
image of `tsupport chi`. -/
theorem canonCutMul_supp
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : EuclN → ℝ) :
    tsupport (canonCutMul (I := I) (M := M) rFine hr z u) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  (tsupport_mul_subset_left
    (f := canonCutE (I := I) (M := M) rFine hr z) (g := u)).trans
      (canonCut_support (I := I) (M := M) rFine hr z)

/-- Middle-cutoff multiplication is bounded on every `W^{k,p}(ℝⁿ)`. -/
theorem canonCut_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p u Set.univ →
      MemWkp (d := Module.finrank ℝ E) k p
          (canonCutMul (I := I) (M := M) rFine hr z u) Set.univ ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (canonCutMul (I := I) (M := M) rFine hr z u) Set.univ ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p u Set.univ := by
  have hsmooth := canonCut_smooth (I := I) (M := M) rFine hr z
  have hcpt := canonCut_cpt (I := I) (M := M) rFine hr z
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

/-! ## Euclidean-cutoff reassembly and the exact retraction -/

/-- Scalar multiplication can be moved through model-fibre repacking. -/
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
  rfl

/-- Reassemble a flat fine array by applying the Euclidean middle cutoff
before each chart pullback. -/
noncomputable def canonERepack
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ)
    (u : FineCompArray (E := E)
      (CanonFineFlat (I := I) (M := M) rFine hr) r s) :
    RSTensorSection I M r s :=
  fun x =>
    ∑ a : CanonChartIdx (I := I) (M := M),
      ∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
        chartRepack (I := I) (M := M) r s a.1
          (fun P => canonCutMul (I := I) (M := M) rFine hr ⟨a, z⟩
            (u ⟨a, z⟩ P)) x

/-- One Euclidean-cutoff chart pullback equals multiplication by the same
middle cutoff after pullback. -/
theorem chartRepack_cut
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ) :
    chartRepack (I := I) (M := M) r s
        (canonFlatBase (I := I) (M := M) rFine hr z)
        (fun P => canonCutMul (I := I) (M := M) rFine hr z (u P)) =
      fun x =>
        ((canonFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
          chartRepack (I := I) (M := M) r s
            (canonFlatBase (I := I) (M := M) rFine hr z) u x := by
  funext x
  by_cases hx : x ∈
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source
  · unfold chartRepack secModelPull
    simp only [dif_pos hx]
    rw [modelRepack_mul (E := E) r s
      (canonCutE (I := I) (M := M) rFine hr z) u,
      canonCut_coord (I := I) (M := M) rFine hr z hx, map_smul]
  · unfold chartRepack secModelPull
    simp only [dif_neg hx, smul_zero]

/-- Euclidean-cutoff reassembly agrees pointwise with the manifold-side
middle-cutoff reassembly. -/
theorem canonERepack_eq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ)
    (u : FineCompArray (E := E)
      (CanonFineFlat (I := I) (M := M) rFine hr) r s) :
    canonERepack (I := I) (M := M) rFine hr r s u =
      canonCutRepack (I := I) (M := M) rFine hr r s u := by
  classical
  funext x
  unfold canonERepack canonCutRepack
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro z _
  exact congrFun
    (chartRepack_cut (I := I) (M := M) rFine hr r s ⟨a, z⟩ (u ⟨a, z⟩)) x

/-- The Euclidean-cutoff reassembly is an exact left inverse of canonical
fine extraction on genuine tensor sections. -/
theorem canonE_retract
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (S : RSTensorSection I M r s) :
    canonERepack (I := I) (M := M) rFine hr r s
        (canonFineRaw (I := I) (M := M) rFine hr r s S) =
      S := by
  rw [canonERepack_eq (I := I) (M := M)]
  exact canonCut_retract (I := I) (M := M) rFine hr r s S

/-! ## The outer-cutoff transition coefficient -/

/-- The tensor transition coefficient localized by the target canonical
kernel and the source fine outer cutoff. -/
def fineTransCoeff
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) : M → ℝ :=
  fun x =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x *
      ((canonFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        transitionCoeff (E := E) (I := I) (M := M) r s
          (canonFlatBase (I := I) (M := M) rFine hr z) α P Q x

/-- The compact carrier used to globalize one fine transition coefficient. -/
private def fineTransSupport
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) (α : M) : Set M :=
  tsupport
      (((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯) : M → ℝ)) ∩
    tsupport
      (((canonFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ))

private theorem fineTransSupport_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) (α : M) :
    IsCompact (fineTransSupport (I := I) (M := M) rFine hr z α) :=
  (chartKernelCutoff_hasCompactSupport (I := I) (M := M) α).inter_right
    (isClosed_tsupport _)

private theorem fineTransSupport_src
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) (α : M) :
    fineTransSupport (I := I) (M := M) rFine hr z α ⊆
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source :=
  fun _ hx => canonPsi_src (I := I) (M := M) rFine hr z hx.2

private theorem fineTransSupport_tgt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) (α : M) :
    fineTransSupport (I := I) (M := M) rFine hr z α ⊆
      (chartAt H α).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source
    (I := I) (M := M) α hx.1

private theorem fineTrans_zero_left
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) α :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x = 0 := by
  rw [fineTransCoeff, hx, zero_mul]

private theorem fineTrans_zero_right
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((canonFlatPsi (I := I) (M := M) rFine hr z :
      C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x = 0 := by
  rw [fineTransCoeff, hx, mul_zero, zero_mul]

/-- The fine transition coefficient is supported in the compact intersection
of the target kernel support and source outer-cutoff support. -/
theorem fineTrans_support
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
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

/-- The fine transition coefficient has compact support. -/
theorem fineTrans_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport
      (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) :=
  HasCompactSupport.of_support_subset_isCompact
    (fineTransSupport_cpt (I := I) (M := M) rFine hr z α)
    (fun _ hx => fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q (subset_tsupport _ hx))

/-- The fine transition coefficient is globally smooth. -/
theorem fineTrans_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ContMDiff I (𝑐(ℝ, ℝ)) ∞
      (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) := by
  classical
  intro x
  by_cases hx : x ∈
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source ∩
        (chartAt H α).source
  · have htarget :=
      ((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have hsource :=
      ((canonFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have hopen : IsOpen
        ((chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source ∩
          (chartAt H α).source) :=
      (chartAt H _).open_source.inter (chartAt H α).open_source
    have hcoeff :=
      (contMDiffOn_transitionCoeff (E := E) (I := I) (M := M)
        r s (canonFlatBase (I := I) (M := M) rFine hr z) α P Q)
        .contMDiffAt (hopen.mem_nhds hx)
    simpa only [fineTransCoeff] using (htarget.mul hsource).mul hcoeff
  · have hxoff : x ∉ tsupport
        (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) := by
      intro hs
      have hcarrier := fineTrans_support (I := I) (M := M)
        rFine hr r s z α P Q hs
      exact hx ⟨fineTransSupport_src (I := I) (M := M)
        rFine hr z α hcarrier,
        fineTransSupport_tgt (I := I) (M := M) rFine hr z α hcarrier⟩
    refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const ?_
    filter_upwards [((isClosed_tsupport _).isOpen_compl.mem_nhds hxoff)] with y hy
    have hyoff : y ∉ Function.support
        (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q) :=
      fun h => hy (subset_tsupport _ h)
    by_contra hne
    exact hyoff hne

/-- The fine transition coefficient written in source Euclidean coordinates
and extended by zero. -/
def fineCoeffE
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)

/-- The source-Euclidean fine transition coefficient is globally smooth. -/
theorem fineCoeff_smooth
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fineCoeffE (I := I) (M := M) rFine hr r s z α P Q) := by
  apply contDiff_etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)
  · exact fineTrans_smooth (I := I) (M := M) rFine hr r s z α P Q
  · exact fineTrans_cpt (I := I) (M := M) rFine hr r s z α P Q
  · exact (fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q).trans
        (fineTransSupport_src (I := I) (M := M) rFine hr z α)

/-- The source-Euclidean fine transition coefficient has compact support. -/
theorem fineCoeff_cpt
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport
      (fineCoeffE (I := I) (M := M) rFine hr r s z α P Q) := by
  apply hasCompactSupport_etaEuclid (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q)
  · exact fineTrans_cpt (I := I) (M := M) rFine hr r s z α P Q
  · exact (fineTrans_support (I := I) (M := M)
      rFine hr r s z α P Q).trans
        (fineTransSupport_src (I := I) (M := M) rFine hr z α)

/-- On the source chart, the Euclidean fine coefficient evaluates to its
manifold counterpart. -/
theorem fineCoeff_apply
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {x : M}
    (hx : x ∈
      (chartAt H (canonFlatBase (I := I) (M := M) rFine hr z)).source) :
    fineCoeffE (I := I) (M := M) rFine hr r s z α P Q
        (toEuclidean (E := E)
          (extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) x)) =
      fineTransCoeff (I := I) (M := M) rFine hr r s z α P Q x := by
  rw [fineCoeffE, etaEuclid_apply_of_mem (I := I) (M := M)
    (canonFlatBase (I := I) (M := M) rFine hr z) _
    (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z) hx),
    symm_toEuclidean_symm_toEuclidean_extChartAt
      (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z) hx]

/-- Multiplication by one fixed outer-cutoff transition coefficient is
bounded on `W^{k,p}` of the source chart. -/
theorem fineCoeff_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s k : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) →
      MemWkp (d := Module.finrank ℝ E) k p
          (fun y => fineCoeffE (I := I) (M := M)
            rFine hr r s z α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (fun y => fineCoeffE (I := I) (M := M)
              rFine hr r s z α P Q y * v y)
            (chartTargetEuclid (I := I) (M := M)
              (canonFlatBase (I := I) (M := M) rFine hr z)) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M)
                (canonFlatBase (I := I) (M := M) rFine hr z)) := by
  classical
  have hsmooth := fineCoeff_smooth (I := I) (M := M)
    rFine hr r s z α P Q
  have hcpt := fineCoeff_cpt (I := I) (M := M)
    rFine hr r s z α P Q
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hsmooth hcpt k
  obtain ⟨K, hK, hKbound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E)
      k hp hp_top
      (chartTargetEuclid_isOpen (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z))
      hsmooth hC (fun j hj y _ => hCbound y j hj)
  refine ⟨K, hK, ?_⟩
  intro v hv
  refine ⟨?_, hKbound hv⟩
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E)
    k hp
    (chartTargetEuclid_isOpen (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z))
    hsmooth (fun j hj y _ => hCbound y j hj) hv

/-- The contribution of source component `Q` in one fine block to target
component `P`, using the source outer cutoff and the target chart kernel. -/
def fineSecTerm
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    (v : EuclN → ℝ) : EuclN → ℝ :=
  chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
    (chartPullback I
      (canonFlatBase (I := I) (M := M) rFine hr z)
      (fun y => fineCoeffE (I := I) (M := M)
        rFine hr r s z α P Q y * v y))

/-- A source component supported in the coordinate image of the middle
fine cutoff contributes a quantitatively controlled `W^{k,p}` function in
every target chart. -/
theorem fineTerm_joint
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) →
      tsupport v ⊆
          (fun x : M => toEuclidean (E := E)
            (extChartAt I
              (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
            tsupport
              (((canonFlatChi (I := I) (M := M) rFine hr z :
                C^∞⟮I, M; ℝ⟯) : M → ℝ)) →
      MemWkp (d := Module.finrank ℝ E) k p
          (fineSecTerm (I := I) (M := M)
            rFine hr r s z α P Q v)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (fineSecTerm (I := I) (M := M)
              rFine hr r s z α P Q v)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M)
                (canonFlatBase (I := I) (M := M) rFine hr z)) := by
  classical
  obtain ⟨K_mul, hK_mul, hmul⟩ :=
    fineCoeff_joint (I := I) (M := M)
      rFine hr r s k z α P Q hp hp_top
  obtain ⟨K_cross, hK_cross, hcross⟩ :=
    crossChartJointK (I := I) (M := M) g k hp hp_top α
      (canonFlatBase (I := I) (M := M) rFine hr z)
      (K_α := tsupport
        (((canonFlatChi (I := I) (M := M) rFine hr z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (canonChi_cpt (I := I) (M := M) rFine hr z)
      (canonChi_src (I := I) (M := M) rFine hr z)
  refine ⟨K_cross * K_mul, mul_pos hK_cross hK_mul, ?_⟩
  intro v hv hv_supp
  have hv_mul := hmul hv
  have hprod_supp :
      tsupport (fun y => fineCoeffE (I := I) (M := M)
          rFine hr r s z α P Q y * v y) ⊆
        (fun x : M => toEuclidean (E := E)
          (extChartAt I
            (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
          tsupport
            (((canonFlatChi (I := I) (M := M) rFine hr z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    (tsupport_mul_subset_right
      (f := fineCoeffE (I := I) (M := M)
        rFine hr r s z α P Q) (g := v)).trans hv_supp
  have hout := hcross hv_mul.1 hprod_supp
  refine ⟨hout.1, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) k p
        (fineSecTerm (I := I) (M := M)
          rFine hr r s z α P Q v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal K_cross *
        wkpNorm (d := Module.finrank ℝ E) k p
          (fun y => fineCoeffE (I := I) (M := M)
            rFine hr r s z α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) := hout.2
    _ ≤ ENNReal.ofReal K_cross *
        (ENNReal.ofReal K_mul *
          wkpNorm (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M)
              (canonFlatBase (I := I) (M := M) rFine hr z))) :=
      mul_le_mul_left' hv_mul.2 _
    _ = ENNReal.ofReal (K_cross * K_mul) *
        wkpNorm (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) := by
      rw [ENNReal.ofReal_mul hK_cross.le]
      simp only [mul_assoc]

/-- On a middle-cutoff-supported source component, the outer-cutoff
coefficient is exactly the raw transition coefficient after multiplication
by the target POU weight. -/
theorem fineCoeffEq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P Q : TensorCompIdx (E := E) r s)
    {v : EuclN → ℝ}
    (hv : tsupport v ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I
          (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
        tsupport
          (((canonFlatChi (I := I) (M := M) rFine hr z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ)))
    {x : M}
    (hx : x ∈
      (chartAt H
        (canonFlatBase (I := I) (M := M) rFine hr z)).source) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (transitionCoeff (E := E) (I := I) (M := M) r s
          (canonFlatBase (I := I) (M := M) rFine hr z) α P Q x *
          v (toEuclidean (E := E)
            (extChartAt I
              (canonFlatBase (I := I) (M := M) rFine hr z) x))) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (fineTransCoeff (I := I) (M := M)
          rFine hr r s z α P Q x *
          v (toEuclidean (E := E)
            (extChartAt I
              (canonFlatBase (I := I) (M := M) rFine hr z) x))) := by
  classical
  by_cases hρ :
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, zero_mul, zero_mul]
  by_cases hvx : v (toEuclidean (E := E)
      (extChartAt I
        (canonFlatBase (I := I) (M := M) rFine hr z) x)) = 0
  · rw [hvx, mul_zero, mul_zero]
  have hxα_supp : x ∈ tsupport
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    subset_tsupport _ hρ
  have hcut :
      ((chartKernelCutoff (I := I) (M := M) α :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 :=
    chartKernelCutoff_eqOn_one (I := I) (M := M) α hxα_supp
  have hy_supp := hv (subset_tsupport _ hvx)
  obtain ⟨w, hwχ, hcoord⟩ := hy_supp
  have hw : w ∈
      (chartAt H
        (canonFlatBase (I := I) (M := M) rFine hr z)).source :=
    canonChi_src (I := I) (M := M) rFine hr z hwχ
  have hw_ext : w ∈
      (extChartAt I
        (canonFlatBase (I := I) (M := M) rFine hr z)).source := by
    rw [extChartAt_source]
    exact hw
  have hx_ext : x ∈
      (extChartAt I
        (canonFlatBase (I := I) (M := M) rFine hr z)).source := by
    rw [extChartAt_source]
    exact hx
  have hext :
      extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) w =
        extChartAt I (canonFlatBase (I := I) (M := M) rFine hr z) x :=
    (toEuclidean (E := E)).injective hcoord
  have hwx : w = x :=
    (extChartAt I
      (canonFlatBase (I := I) (M := M) rFine hr z)).injOn
        hw_ext hx_ext hext
  have hψ :
      ((canonFlatPsi (I := I) (M := M) rFine hr z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
    rw [← hwx]
    exact canonPsi_one (I := I) (M := M) rFine hr z hwχ
  rw [fineTransCoeff, hcut, hψ]
  ring

/-- Every target-chart component of one middle-localized repacked fine block
is the finite sum of its outer-cutoff transition terms. -/
theorem finePullEq
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ Q, tsupport (u Q) ⊆
      (fun x : M => toEuclidean (E := E)
        (extChartAt I
          (canonFlatBase (I := I) (M := M) rFine hr z) x)) ''
        tsupport
          (((canonFlatChi (I := I) (M := M) rFine hr z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s
        (chartRepack (I := I) (M := M) r s
          (canonFlatBase (I := I) (M := M) rFine hr z) u)
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
        (canonFlatBase (I := I) (M := M) rFine hr z)).source
  · rw [chartRepack,
      secPull_raw_trans (E := E) (I := I) (M := M) r s
        (canonFlatBase (I := I) (M := M) rFine hr z) α
        (modelRepack (E := E) r s u) P ⟨hx, hxα⟩,
      Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Q _
    rw [modelRepack_proj (E := E) r s u Q]
    unfold fineSecTerm chartPushed
    rw [chartPullback_apply_of_mem (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z) _ hx,
      fineCoeff_apply (I := I) (M := M)
        rFine hr r s z α P Q hx]
    exact fineCoeffEq (I := I) (M := M)
      rFine hr r s z α P Q (hu Q) hx
  · have hpull :
        chartRepack (I := I) (M := M) r s
          (canonFlatBase (I := I) (M := M) rFine hr z) u x = 0 := by
      unfold chartRepack secModelPull
      rw [dif_neg hx]
    unfold secCompRaw secTriv
    rw [hpull, map_zero, map_zero, mul_zero]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold fineSecTerm chartPushed
    rw [chartPullback_apply_of_notMem (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z) _ hx, mul_zero]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
