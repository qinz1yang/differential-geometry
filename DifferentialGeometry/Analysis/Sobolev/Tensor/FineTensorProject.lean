import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpCompat
import DifferentialGeometry.Analysis.Sobolev.Tensor.FineTensorWkp
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.FineChartCover
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

private local instance : Fact (IsOpen (Set.univ : Set EuclN)) :=
  ⟨isOpen_univ⟩

abbrev FineCompArray (ι : Type*) (r s : ℕ) :=
  ι → TensorCompIdx (E := E) r s → EuclN → ℝ

noncomputable def modelRepack (r s : ℕ)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (y : EuclN) : TensorRSModel r s ℝ E :=
  ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      u (Idx, Jdx) y •
        tensorChartBasisElement (E := E) r s Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem modelRepack_proj (r s : ℕ)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (P : TensorCompIdx (E := E) r s) (y : EuclN) :
    tensorChartComponentProjection (E := E) r s P.1 P.2
        (modelRepack (E := E) r s u y) =
      u P y := by
  classical
  rw [modelRepack, map_sum, Finset.sum_eq_single P.1]
  · rw [map_sum, Finset.sum_eq_single P.2]
    · rw [map_smul, smul_eq_mul,
        tensorChartComponentProjection_basisElement (E := E)
          r s P.1 P.1 P.2 P.2]
      simp
    · intro Jdx _ hJdx
      rw [map_smul, smul_eq_mul,
        tensorChartComponentProjection_basisElement (E := E)
          r s P.1 P.1 P.2 Jdx, if_pos rfl, if_neg hJdx,
        mul_zero, mul_zero]
    · simp
  · intro Idx _ hIdx
    rw [map_sum]
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E)
        r s P.1 Idx P.2 Jdx, if_neg (Ne.symm hIdx),
      zero_mul, mul_zero]
  · simp

omit [NeZero (Module.finrank ℝ E)] in
theorem modelRepack_eq (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (y : EuclN) :
    modelRepack (E := E) r s
        (fun P _ =>
          tensorChartComponentProjection (E := E) r s P.1 P.2 T) y =
      T := by
  change (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx T •
          tensorChartBasisElement (E := E) r s Idx Jdx) = T
  exact (tensorRSModel_eq_sum_basis (E := E) r s T).symm

noncomputable def chartExtract (r s : ℕ) (α : M)
    (S : RSTensorSection I M r s) :
    TensorCompIdx (E := E) r s → EuclN → ℝ :=
  fun P => chartPushedRaw (I := I) (M := M) α
    (secCompRaw (I := I) (M := M) r s S α P.1 P.2)

noncomputable def chartRepack (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ) :
    RSTensorSection I M r s :=
  secModelPull (I := I) (M := M) r s α
    (modelRepack (E := E) r s u)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem chartRepack_raw (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    secCompRaw (I := I) (M := M) r s
        (chartRepack (I := I) (M := M) r s α u) α P.1 P.2 x =
      u P (toEuclidean (E := E) (extChartAt I α x)) := by
  rw [chartRepack,
    secPull_raw_eq (E := E) (I := I) (M := M) r s α
      (modelRepack (E := E) r s u) P.1 P.2 hx,
    modelRepack_proj (E := E) r s u P]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartExtract_coord (r s : ℕ) (α : M)
    (S : RSTensorSection I M r s)
    (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartExtract (I := I) (M := M) r s α S P
        (toEuclidean (E := E) (extChartAt I α x)) =
      secCompRaw (I := I) (M := M) r s S α P.1 P.2 x := by
  unfold chartExtract
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid
        (I := I) (M := M) α hx),
    symm_toEuclidean_symm_toEuclidean_extChartAt
      (I := I) (M := M) α hx]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem rsTriv_base (r s : ℕ) (α : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (chartAt H α).source := by
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet =
    (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet =
    (chartAt H α).source
  rw [Set.inter_self]
  exact trivializationAt_baseSet_eq_chartAt_source (I := I) α

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartRepack_extract (r s : ℕ) (α : M)
    (S : RSTensorSection I M r s) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartRepack (I := I) (M := M) r s α
        (chartExtract (I := I) (M := M) r s α S) x =
      S x := by
  classical
  have hmodel :
      modelRepack (E := E) r s
          (chartExtract (I := I) (M := M) r s α S)
          (toEuclidean (E := E) (extChartAt I α x)) =
        secTriv (I := I) (M := M) r s S α x := by
    unfold modelRepack
    rw [tensorRSModel_eq_sum_basis (E := E) r s
      (secTriv (I := I) (M := M) r s S α x)]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [chartExtract_coord (E := E) (I := I) (M := M)
      r s α S (Idx, Jdx) hx]
    rfl
  have hxbase : x ∈
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [rsTriv_base (E := E) (I := I) (M := M) r s α]
    exact hx
  unfold chartRepack secModelPull
  rw [dif_pos hx, hmodel]
  unfold secTriv
  rw [(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).symmL_continuousLinearMapAt
        (R := ℝ) hxbase (S x)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartRepack_fine (r s : ℕ) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (S : RSTensorSection I M r s) (x : M) :
    chartRepack (I := I) (M := M) r s α
        (fun P => fineLocComp (I := I) (M := M) r s φ S α P) x =
      ((φ : M → ℝ) x *
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
  classical
  by_cases hx : x ∈ (chartAt H α).source
  · have hy : toEuclidean (E := E) (extChartAt I α x) ∈
        chartTargetEuclid (I := I) (M := M) α :=
      toEuclidean_extChartAt_mem_chartTargetEuclid
        (I := I) (M := M) α hx
    let c : ℝ := (φ : M → ℝ) x *
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    have hmodel :
        modelRepack (E := E) r s
            (fun P => fineLocComp (I := I) (M := M) r s φ S α P)
            (toEuclidean (E := E) (extChartAt I α x)) =
          c • secTriv (I := I) (M := M) r s S α x := by
      unfold modelRepack
      calc
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fineLocComp (I := I) (M := M) r s φ S α (Idx, Jdx)
                  (toEuclidean (E := E) (extChartAt I α x)) •
                tensorChartBasisElement (E := E) r s Idx Jdx) =
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                c •
                  (secCompRaw (I := I) (M := M) r s S α Idx Jdx x •
                    tensorChartBasisElement (E := E) r s Idx Jdx) := by
          refine Finset.sum_congr rfl ?_
          intro Idx _
          refine Finset.sum_congr rfl ?_
          intro Jdx _
          rw [fineLoc_apply (I := I) (M := M) r s φ S α
              (Idx, Jdx) hy,
            secComp_coord (I := I) (M := M) r s S α (Idx, Jdx) hx,
            symm_toEuclidean_symm_toEuclidean_extChartAt
              (I := I) (M := M) α hx]
          unfold secCompPou c
          rw [smul_smul]
          congr 1
          ring
        _ = c •
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                secCompRaw (I := I) (M := M) r s S α Idx Jdx x •
                  tensorChartBasisElement (E := E) r s Idx Jdx) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro Idx _
          rw [Finset.smul_sum]
        _ = c • secTriv (I := I) (M := M) r s S α x := by
          apply congrArg (fun T : TensorRSModel r s ℝ E => c • T)
          simpa only [secCompRaw] using
            (tensorRSModel_eq_sum_basis (E := E) r s
              (secTriv (I := I) (M := M) r s S α x)).symm
    have hxbase : x ∈
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [rsTriv_base (E := E) (I := I) (M := M) r s α]
      exact hx
    unfold chartRepack secModelPull
    rw [dif_pos hx, hmodel]
    rw [ContinuousLinearMap.map_smul]
    unfold secTriv
    rw [(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).symmL_continuousLinearMapAt
          (R := ℝ) hxbase (S x)]
  · have hρ :
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
      by_contra hne
      exact hx (chartAtlasPOU_isSubordinate I M α
        (subset_tsupport _ hne))
    unfold chartRepack secModelPull
    rw [dif_neg hx, hρ, mul_zero, zero_smul]

noncomputable def finePouRepack
    {κ : M → Type*} [∀ α, Fintype (κ α)]
    (r s : ℕ) (φ : ∀ α, κ α → C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) : RSTensorSection I M r s :=
  fun x =>
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ z : κ α,
        chartRepack (I := I) (M := M) r s α
          (fun P => fineLocComp (I := I) (M := M) r s (φ α z) S α P) x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem finePou_retract
    {κ : M → Type*} [∀ α, Fintype (κ α)]
    (r s : ℕ) (φ : ∀ α, κ α → C^∞⟮I, M; ℝ⟯)
    (hsum : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ x ∈ tsupport
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        ∑ z : κ α, ((φ α z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1)
    (S : RSTensorSection I M r s) :
    finePouRepack (I := I) (M := M) r s φ S = S := by
  classical
  funext x
  unfold finePouRepack
  have hinner : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (∑ z : κ α,
          chartRepack (I := I) (M := M) r s α
            (fun P => fineLocComp (I := I) (M := M) r s
              (φ α z) S α P) x) =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
    intro α hα
    calc
      (∑ z : κ α,
          chartRepack (I := I) (M := M) r s α
            (fun P => fineLocComp (I := I) (M := M) r s
              (φ α z) S α P) x) =
        ∑ z : κ α,
          (((φ α z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
          refine Finset.sum_congr rfl ?_
          intro z _
          exact chartRepack_fine (I := I) (M := M) r s α (φ α z) S x
      _ = ((∑ z : κ α,
            ((φ α z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
          rw [Finset.sum_mul, Finset.sum_smul]
      _ = ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
          by_cases hρ :
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
          · rw [hρ, mul_zero]
          · rw [hsum α hα x (subset_tsupport _ hρ), one_mul]
  calc
    (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ z : κ α,
          chartRepack (I := I) (M := M) r s α
            (fun P => fineLocComp (I := I) (M := M) r s
              (φ α z) S α P) x) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          exact hinner α hα
    _ = (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
        rw [Finset.sum_smul]
    _ = S x := by
      rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_smul]

noncomputable def canonFineData
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α) (α : M) :
    FineChartData (I := I)
      (extChartOpenPartialHomeomorph (I := I) α)
      (tsupport (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (rFine α) :=
  Classical.choice (existsFineChart (I := I)
    (extChartOpenPartialHomeomorph (I := I) α)
    (isClosed_tsupport _).isCompact
    (by
      change tsupport
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
          (extChartAt I α).source
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α)
    (hr α))

abbrev CanonFineIdx
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α) (α : M) : Type _ :=
  (canonFineData (I := I) (M := M) rFine hr α).S

noncomputable def canonFineWeight
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (α : M) (z : CanonFineIdx (I := I) (M := M) rFine hr α) :
    C^∞⟮I, M; ℝ⟯ :=
  (canonFineData (I := I) (M := M) rFine hr α).rho z

noncomputable def canonFineChi
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (α : M) (z : CanonFineIdx (I := I) (M := M) rFine hr α) :
    C^∞⟮I, M; ℝ⟯ :=
  (canonFineData (I := I) (M := M) rFine hr α).chi z

noncomputable def canonFinePsi
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (α : M) (z : CanonFineIdx (I := I) (M := M) rFine hr α) :
    C^∞⟮I, M; ℝ⟯ :=
  (canonFineData (I := I) (M := M) rFine hr α).psi z

abbrev CanonChartIdx : Type _ :=
  chartAtlasPOU_finset (I := I) (M := M)

abbrev CanonFineFlat
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α) : Type _ :=
  Σ a : CanonChartIdx (I := I) (M := M),
    CanonFineIdx (I := I) (M := M) rFine hr a.1

def canonFlatBase
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) : M :=
  z.1.1

noncomputable def canonFlatWeight
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    C^∞⟮I, M; ℝ⟯ :=
  canonFineWeight (I := I) (M := M) rFine hr z.1.1 z.2

noncomputable def canonFlatChi
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    C^∞⟮I, M; ℝ⟯ :=
  canonFineChi (I := I) (M := M) rFine hr z.1.1 z.2

noncomputable def canonFlatPsi
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (z : CanonFineFlat (I := I) (M := M) rFine hr) :
    C^∞⟮I, M; ℝ⟯ :=
  canonFinePsi (I := I) (M := M) rFine hr z.1.1 z.2

omit [NeZero (Module.finrank ℝ E)] in
theorem canonChi_weight
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (α : M) (z : CanonFineIdx (I := I) (M := M) rFine hr α)
    (x : M) :
    ((canonFineChi (I := I) (M := M) rFine hr α z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        ((canonFineWeight (I := I) (M := M) rFine hr α z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      ((canonFineWeight (I := I) (M := M) rFine hr α z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x := by
  by_cases hρ :
      ((canonFineWeight (I := I) (M := M) rFine hr α z :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, mul_zero]
  · have hx : x ∈ tsupport
        (((canonFineData (I := I) (M := M) rFine hr α).rho z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hρ
    have hχ :
        ((canonFineChi (I := I) (M := M) rFine hr α z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
      exact ((canonFineData (I := I) (M := M) rFine hr α).chi_one z)
        |>.self_of_nhdsSet x hx
    rw [hχ, one_mul]

noncomputable def canonFineQMap
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      FineWkpArray (E := E)
        (CanonFineFlat (I := I) (M := M) rFine hr) r s k p hp :=
  fineExtractMap (I := I) (M := M) g r s k hp hp_top
    (canonFlatWeight (I := I) (M := M) rFine hr)
    (canonFlatBase (I := I) (M := M) rFine hr)

theorem canonFineQ_add
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    canonFineQMap (I := I) (M := M) rFine hr g r s k hp hp_top
        (qadd (I := I) (M := M) g r s k p hp a b) =
      fun z P => eadd k p hp Set.univ
        (canonFineQMap (I := I) (M := M) rFine hr g r s k hp hp_top a z P)
        (canonFineQMap (I := I) (M := M) rFine hr g r s k hp hp_top b z P) := by
  exact fineExtract_add (I := I) (M := M) g r s k hp hp_top
    (canonFlatWeight (I := I) (M := M) rFine hr)
    (canonFlatBase (I := I) (M := M) rFine hr) a b

theorem canonFineQ_smul
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (c : ℝ) (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    canonFineQMap (I := I) (M := M) rFine hr g r s k hp hp_top
        (qsmul (I := I) (M := M) g r s k p hp c a) =
      fun z P => esmul k p hp Set.univ c
        (canonFineQMap (I := I) (M := M) rFine hr g r s k hp hp_top a z P) := by
  exact fineExtract_smul (I := I) (M := M) g r s k hp hp_top
    (canonFlatWeight (I := I) (M := M) rFine hr)
    (canonFlatBase (I := I) (M := M) rFine hr) c a

noncomputable def canonFineRaw
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (S : RSTensorSection I M r s) :
    FineCompArray (E := E)
      (CanonFineFlat (I := I) (M := M) rFine hr) r s :=
  fun z P => fineLocComp (I := I) (M := M) r s
    (canonFlatWeight (I := I) (M := M) rFine hr z) S
    (canonFlatBase (I := I) (M := M) rFine hr z) P

noncomputable def canonCutRepack
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ)
    (u : FineCompArray (E := E)
      (CanonFineFlat (I := I) (M := M) rFine hr) r s) :
    RSTensorSection I M r s :=
  fun x =>
    ∑ a : CanonChartIdx (I := I) (M := M),
      ∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
        ((canonFineChi (I := I) (M := M) rFine hr a.1 z :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
          chartRepack (I := I) (M := M) r s a.1
            (u ⟨a, z⟩) x

omit [NeZero (Module.finrank ℝ E)] in
theorem canonCut_retract
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (S : RSTensorSection I M r s) :
    canonCutRepack (I := I) (M := M) rFine hr r s
        (canonFineRaw (I := I) (M := M) rFine hr r s S) =
      S := by
  classical
  funext x
  unfold canonCutRepack canonFineRaw
  have hinner : ∀ a : CanonChartIdx (I := I) (M := M),
      (∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
          ((canonFineChi (I := I) (M := M) rFine hr a.1 z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
            chartRepack (I := I) (M := M) r s a.1
              (fun P => fineLocComp (I := I) (M := M) r s
                (canonFineWeight (I := I) (M := M) rFine hr a.1 z)
                S a.1 P) x) =
        ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
    intro a
    calc
      (∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
          ((canonFineChi (I := I) (M := M) rFine hr a.1 z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
            chartRepack (I := I) (M := M) r s a.1
              (fun P => fineLocComp (I := I) (M := M) r s
                (canonFineWeight (I := I) (M := M) rFine hr a.1 z)
                S a.1 P) x) =
        ∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
          (((canonFineWeight (I := I) (M := M) rFine hr a.1 z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) •
              S x := by
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [chartRepack_fine (I := I) (M := M) r s a.1
            (canonFineWeight (I := I) (M := M) rFine hr a.1 z) S x,
            smul_smul]
          congr 1
          rw [← mul_assoc,
            canonChi_weight (I := I) (M := M) rFine hr a.1 z x]
      _ = ((∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
            ((canonFineWeight (I := I) (M := M) rFine hr a.1 z :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
          ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
          rw [Finset.sum_mul, Finset.sum_smul]
      _ = ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
          by_cases hρ :
              ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
          · rw [hρ, mul_zero]
          · have hsum :
                (∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
                  ((canonFineWeight (I := I) (M := M) rFine hr a.1 z :
                    C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = 1 := by
              simpa only [canonFineWeight] using
                (canonFineData (I := I) (M := M) rFine hr a.1).rho_sum
                  (subset_tsupport _ hρ)
            rw [hsum, one_mul]
  have hcanon :
      (∑ a : CanonChartIdx (I := I) (M := M),
          ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = 1 := by
    exact (Finset.sum_subtype
      (s := chartAtlasPOU_finset (I := I) (M := M))
      (p := fun a => a ∈ chartAtlasPOU_finset (I := I) (M := M))
      (fun _ => Iff.rfl)
      (fun a =>
        ((chartAtlasPOU I M a : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).symm.trans
          (chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x)
  calc
    (∑ a : CanonChartIdx (I := I) (M := M),
        ∑ z : CanonFineIdx (I := I) (M := M) rFine hr a.1,
          ((canonFineChi (I := I) (M := M) rFine hr a.1 z :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
            chartRepack (I := I) (M := M) r s a.1
              (fun P => fineLocComp (I := I) (M := M) r s
                (canonFineWeight (I := I) (M := M) rFine hr a.1 z)
                S a.1 P) x) =
      ∑ a : CanonChartIdx (I := I) (M := M),
        ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S x := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact hinner a
    _ = (∑ a : CanonChartIdx (I := I) (M := M),
          ((chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) • S x := by
        rw [Finset.sum_smul]
    _ = S x := by rw [hcanon, one_smul]

omit [NeZero (Module.finrank ℝ E)] in
theorem canonFine_retract
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (S : RSTensorSection I M r s) :
    finePouRepack (I := I) (M := M)
        (κ := fun α => CanonFineIdx (I := I) (M := M) rFine hr α)
        r s (canonFineWeight (I := I) (M := M) rFine hr) S =
      S := by
  apply finePou_retract (I := I) (M := M) r s
    (canonFineWeight (I := I) (M := M) rFine hr)
  intro α _hα x hx
  exact (canonFineData (I := I) (M := M) rFine hr α).rho_sum hx

noncomputable def fineExtract {ι : Type*} (r s : ℕ) (α : ι → M)
    (S : RSTensorSection I M r s) : FineCompArray (E := E) ι r s :=
  fun z => chartExtract (I := I) (M := M) r s (α z) S

noncomputable def fineRepack {ι : Type*} [Fintype ι]
    (r s : ℕ) (α : ι → M) (ρ : ι → M → ℝ)
    (u : FineCompArray (E := E) ι r s) : RSTensorSection I M r s :=
  fun x => ∑ z : ι, ρ z x •
    chartRepack (I := I) (M := M) r s (α z) (u z) x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem fineRepack_extract {ι : Type*} [Fintype ι]
    (r s : ℕ) (α : ι → M) (ρ : ι → M → ℝ)
    (hsupp : ∀ z x, ρ z x ≠ 0 → x ∈ (chartAt H (α z)).source)
    (hsum : ∀ x, ∑ z : ι, ρ z x = 1)
    (S : RSTensorSection I M r s) :
    fineRepack (I := I) (M := M) r s α ρ
        (fineExtract (I := I) (M := M) r s α S) =
      S := by
  classical
  funext x
  unfold fineRepack fineExtract
  calc
    (∑ z : ι, ρ z x •
        chartRepack (I := I) (M := M) r s (α z)
          (chartExtract (I := I) (M := M) r s (α z) S) x) =
        ∑ z : ι, ρ z x • S x := by
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : ρ z x = 0
          · simp [hz]
          · rw [chartRepack_extract (E := E) (I := I) (M := M)
              r s (α z) S (hsupp z x hz)]
    _ = (∑ z : ι, ρ z x) • S x := by
      rw [Finset.sum_smul]
    _ = S x := by
      rw [hsum x, one_smul]

noncomputable def fineProject {ι : Type*} [Fintype ι]
    (r s : ℕ) (α : ι → M) (ρ : ι → M → ℝ)
    (u : FineCompArray (E := E) ι r s) :
    FineCompArray (E := E) ι r s :=
  fineExtract (I := I) (M := M) r s α
    (fineRepack (I := I) (M := M) r s α ρ u)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem fineRepack_project {ι : Type*} [Fintype ι]
    (r s : ℕ) (α : ι → M) (ρ : ι → M → ℝ)
    (hsupp : ∀ z x, ρ z x ≠ 0 → x ∈ (chartAt H (α z)).source)
    (hsum : ∀ x, ∑ z : ι, ρ z x = 1)
    (u : FineCompArray (E := E) ι r s) :
    fineRepack (I := I) (M := M) r s α ρ
        (fineProject (I := I) (M := M) r s α ρ u) =
      fineRepack (I := I) (M := M) r s α ρ u := by
  exact fineRepack_extract (E := E) (I := I) (M := M)
    r s α ρ hsupp hsum
    (fineRepack (I := I) (M := M) r s α ρ u)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem fineProject_idem {ι : Type*} [Fintype ι]
    (r s : ℕ) (α : ι → M) (ρ : ι → M → ℝ)
    (hsupp : ∀ z x, ρ z x ≠ 0 → x ∈ (chartAt H (α z)).source)
    (hsum : ∀ x, ∑ z : ι, ρ z x = 1)
    (u : FineCompArray (E := E) ι r s) :
    fineProject (I := I) (M := M) r s α ρ
        (fineProject (I := I) (M := M) r s α ρ u) =
      fineProject (I := I) (M := M) r s α ρ u := by
  have h := congrArg
    (fineExtract (I := I) (M := M) r s α)
    (fineRepack_project (E := E) (I := I) (M := M)
      r s α ρ hsupp hsum u)
  simpa only [fineProject] using h

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
