import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality
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

abbrev RSTensorSection
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (r s : ℕ) :=
  (x : M) → TensorRSSpace r s I x

noncomputable def secTriv (r s : ℕ) (S : RSTensorSection I M r s)
    (α x : M) : TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x (S x)

noncomputable def secCompRaw (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  tensorChartComponentProjection (E := E) r s Idx Jdx
    (secTriv (I := I) (M := M) r s S α x)

noncomputable def secCompPou (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
    secCompRaw (I := I) (M := M) r s S α Idx Jdx x

noncomputable def secChartComp (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (secCompPou (I := I) (M := M) r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secComp_apply_mem (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    secChartComp (I := I) (M := M) r s S α Idx Jdx y =
      secCompPou (I := I) (M := M) r s S α Idx Jdx
        ((extChartAt I α).symm (toEuclidean.symm y)) := by
  unfold secChartComp
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secComp_apply_off (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    secChartComp (I := I) (M := M) r s S α Idx Jdx y = 0 := by
  unfold secChartComp
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secTriv_zero (r s : ℕ) (α x : M) :
    secTriv (I := I) (M := M) r s (0 : RSTensorSection I M r s) α x = 0 := by
  unfold secTriv
  let L : TensorRSSpace r s I x →L[ℝ] TensorRSModel r s ℝ E :=
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
  change L (0 : TensorRSSpace r s I x) = 0
  exact L.map_zero
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secTriv_add (r s : ℕ) (S T : RSTensorSection I M r s) (α x : M) :
    secTriv (I := I) (M := M) r s (S + T) α x =
      secTriv (I := I) (M := M) r s S α x +
        secTriv (I := I) (M := M) r s T α x := by
  unfold secTriv
  let L : TensorRSSpace r s I x →L[ℝ] TensorRSModel r s ℝ E :=
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
  change L (S x + T x) = L (S x) + L (T x)
  exact L.map_add (S x) (T x)
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secTriv_smul (r s : ℕ) (c : ℝ) (S : RSTensorSection I M r s)
    (α x : M) :
    secTriv (I := I) (M := M) r s (c • S) α x =
      c • secTriv (I := I) (M := M) r s S α x := by
  unfold secTriv
  let L : TensorRSSpace r s I x →L[ℝ] TensorRSModel r s ℝ E :=
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
  change L (c • S x) = c • L (S x)
  exact L.map_smul c (S x)
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secCompRaw_zero (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    secCompRaw (I := I) (M := M) r s
      (0 : RSTensorSection I M r s) α Idx Jdx x = 0 := by
  unfold secCompRaw
  rw [secTriv_zero (I := I) (M := M)]
  exact map_zero _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secCompRaw_add (r s : ℕ) (S T : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    secCompRaw (I := I) (M := M) r s (S + T) α Idx Jdx x =
      secCompRaw (I := I) (M := M) r s S α Idx Jdx x +
        secCompRaw (I := I) (M := M) r s T α Idx Jdx x := by
  unfold secCompRaw
  rw [secTriv_add (I := I) (M := M)]
  exact map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secCompRaw_smul (r s : ℕ) (c : ℝ)
    (S : RSTensorSection I M r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    secCompRaw (I := I) (M := M) r s (c • S) α Idx Jdx x =
      c • secCompRaw (I := I) (M := M) r s S α Idx Jdx x := by
  unfold secCompRaw
  rw [secTriv_smul (I := I) (M := M)]
  exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma secCompPou_zero (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secCompPou (I := I) (M := M) r s
      (0 : RSTensorSection I M r s) α Idx Jdx = 0 := by
  funext x
  change _ = (0 : ℝ)
  unfold secCompPou
  rw [secCompRaw_zero (I := I) (M := M)]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma secCompPou_add (r s : ℕ) (S T : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secCompPou (I := I) (M := M) r s (S + T) α Idx Jdx =
      secCompPou (I := I) (M := M) r s S α Idx Jdx +
        secCompPou (I := I) (M := M) r s T α Idx Jdx := by
  funext x
  unfold secCompPou
  rw [secCompRaw_add (I := I) (M := M), Pi.add_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma secCompPou_smul (r s : ℕ) (c : ℝ)
    (S : RSTensorSection I M r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secCompPou (I := I) (M := M) r s (c • S) α Idx Jdx =
      c • secCompPou (I := I) (M := M) r s S α Idx Jdx := by
  funext x
  unfold secCompPou
  rw [secCompRaw_smul (I := I) (M := M), Pi.smul_apply]
  change _ * (c * _) = c * (_ * _)
  ring

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartRaw_zero (α : M) :
    chartPushedRaw (I := I) (M := M) α (0 : M → ℝ) = 0 := by
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rfl
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartRaw_add (α : M) (u v : M → ℝ) :
    chartPushedRaw (I := I) (M := M) α (u + v) =
      chartPushedRaw (I := I) (M := M) α u +
        chartPushedRaw (I := I) (M := M) α v := by
  funext y
  rw [Pi.add_apply]
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rfl
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    ring

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartRaw_smul (α : M) (c : ℝ) (u : M → ℝ) :
    chartPushedRaw (I := I) (M := M) α (c • u) =
      c • chartPushedRaw (I := I) (M := M) α u := by
  funext y
  rw [Pi.smul_apply]
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rfl
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    change (0 : ℝ) = c * 0
    ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secChartComp_zero (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s
      (0 : RSTensorSection I M r s) α Idx Jdx = 0 := by
  unfold secChartComp
  rw [secCompPou_zero (I := I) (M := M), chartRaw_zero (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secChartComp_add (r s : ℕ) (S T : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s (S + T) α Idx Jdx =
      secChartComp (I := I) (M := M) r s S α Idx Jdx +
        secChartComp (I := I) (M := M) r s T α Idx Jdx := by
  unfold secChartComp
  rw [secCompPou_add (I := I) (M := M), chartRaw_add (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secChartComp_smul (r s : ℕ) (c : ℝ)
    (S : RSTensorSection I M r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s (c • S) α Idx Jdx =
      c • secChartComp (I := I) (M := M) r s S α Idx Jdx := by
  unfold secChartComp
  rw [secCompPou_smul (I := I) (M := M), chartRaw_smul (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secChartComp_neg (r s : ℕ) (S : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s (-S) α Idx Jdx =
      -secChartComp (I := I) (M := M) r s S α Idx Jdx := by
  have h := secChartComp_smul (I := I) (M := M) r s (-1 : ℝ) S α Idx Jdx
  simpa only [neg_one_smul] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem secChartComp_sub (r s : ℕ) (S T : RSTensorSection I M r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s (S - T) α Idx Jdx =
      secChartComp (I := I) (M := M) r s S α Idx Jdx -
        secChartComp (I := I) (M := M) r s T α Idx Jdx := by
  rw [sub_eq_add_neg, secChartComp_add, secChartComp_neg, ← sub_eq_add_neg]

noncomputable def secChartCompLin (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    RSTensorSection I M r s →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) where
  toFun S := secChartComp (I := I) (M := M) r s S α Idx Jdx
  map_add' S T := secChartComp_add (I := I) (M := M) r s S T α Idx Jdx
  map_smul' c S := secChartComp_smul (I := I) (M := M) r s c S α Idx Jdx

def MemWkpTensor
    (_g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (p : ℝ≥0∞) (S : RSTensorSection I M r s) : Prop :=
  ∀ (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)),
    MemWkp (d := Module.finrank ℝ E) k p
      (secChartComp (I := I) (M := M) r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWkpTensor_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (p : ℝ≥0∞) (S : RSTensorSection I M r s) :
    MemWkpTensor (I := I) (M := M) g k p S ↔
      ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s S α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWkpTensor.zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpTensor (I := I) (M := M) g k p
      (0 : RSTensorSection I M r s) := by
  intro α Idx Jdx
  rw [secChartComp_zero (I := I) (M := M)]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWkpTensor.add
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S T : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S)
    (hT : MemWkpTensor (I := I) (M := M) g k p T) :
    MemWkpTensor (I := I) (M := M) g k p (S + T) := by
  intro α Idx Jdx
  rw [secChartComp_add (I := I) (M := M)]
  exact MemWkp.add (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hS α Idx Jdx) (hT α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWkpTensor.smul
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ) {S : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S) :
    MemWkpTensor (I := I) (M := M) g k p (c • S) := by
  intro α Idx Jdx
  rw [secChartComp_smul (I := I) (M := M)]
  have hfun :
      (c • secChartComp (I := I) (M := M) r s S α Idx Jdx) =
        (fun y => c * secChartComp (I := I) (M := M) r s S α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact MemWkp.const_smul (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α) (hS α Idx Jdx) c

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWkpTensor.neg
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S) :
    MemWkpTensor (I := I) (M := M) g k p (-S) := by
  have h := MemWkpTensor.smul (I := I) (M := M) g hp (-1 : ℝ) hS
  simpa only [neg_one_smul] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWkpTensor.sub
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S T : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S)
    (hT : MemWkpTensor (I := I) (M := M) g k p T) :
    MemWkpTensor (I := I) (M := M) g k p (S - T) := by
  rw [sub_eq_add_neg]
  exact MemWkpTensor.add (I := I) (M := M) g hp hS
    (MemWkpTensor.neg (I := I) (M := M) g hp hT)

def wkpTensorSub
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℝ (RSTensorSection I M r s) where
  carrier := {S | MemWkpTensor (I := I) (M := M) g k p S}
  zero_mem' := MemWkpTensor.zero (I := I) (M := M) g r s k hp
  add_mem' := fun hS hT => MemWkpTensor.add (I := I) (M := M) g hp hS hT
  smul_mem' := fun c _ hS => MemWkpTensor.smul (I := I) (M := M) g hp c hS

abbrev WkpTensor
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :=
  ↥(wkpTensorSub (I := I) (M := M) g r s k p hp)

def wkpTensorNorm
    (_g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (p : ℝ≥0∞) (S : RSTensorSection I M r s) : ℝ≥0∞ :=
  ∑' α : M,
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s S α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wkpTensorNorm_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpTensorNorm (I := I) (M := M) g k p
      (0 : RSTensorSection I M r s) = 0 := by
  unfold wkpTensorNorm
  have hzero : ∀ α : M,
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
            (secChartComp (I := I) (M := M) r s
              (0 : RSTensorSection I M r s) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
    intro α
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [secChartComp_zero (I := I) (M := M)]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hzero]
  exact tsum_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wkpTensorNorm_add_le
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S T : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S)
    (hT : MemWkpTensor (I := I) (M := M) g k p T) :
    wkpTensorNorm (I := I) (M := M) g k p (S + T) ≤
      wkpTensorNorm (I := I) (M := M) g k p S +
        wkpTensorNorm (I := I) (M := M) g k p T := by
  unfold wkpTensorNorm
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Idx _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [secChartComp_add (I := I) (M := M)]
  exact wkpNorm_add_le (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hS α Idx Jdx) (hT α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wkpTensorNorm_smul
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ) {S : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S) :
    wkpTensorNorm (I := I) (M := M) g k p (c • S) =
      ‖c‖₊ * wkpTensorNorm (I := I) (M := M) g k p S := by
  unfold wkpTensorNorm
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Idx _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  rw [secChartComp_smul (I := I) (M := M)]
  have hfun :
      (c • secChartComp (I := I) (M := M) r s S α Idx Jdx) =
        (fun y => c * secChartComp (I := I) (M := M) r s S α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact wkpNorm_const_smul (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α) (hS α Idx Jdx) c

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem secComp_zero_off
    (r s : ℕ) (S : RSTensorSection I M r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s S α Idx Jdx = 0 := by
  have hρ : ∀ x : M, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  funext y
  change _ = (0 : ℝ)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · unfold secChartComp
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    unfold secCompPou
    rw [hρ]
    ring
  · unfold secChartComp
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpTensorNorm_lt_top
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S : RSTensorSection I M r s}
    (hS : MemWkpTensor (I := I) (M := M) g k p S) :
    wkpTensorNorm (I := I) (M := M) g k p S < ⊤ := by
  classical
  unfold wkpTensorNorm
  have hcollapse :
      (∑' α : M,
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
              (secChartComp (I := I) (M := M) r s S α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
                (secChartComp (I := I) (M := M) r s S α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α) := by
    rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
    intro α hα
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [secComp_zero_off (I := I) (M := M) r s S hα Idx Jdx]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [hcollapse]
  refine ENNReal.sum_lt_top.mpr ?_
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Idx _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Jdx _
  exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (hS α Idx Jdx)

def TensorAEEq
    (_g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : RSTensorSection I M r s) : Prop :=
  ∀ (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)),
    secChartComp (I := I) (M := M) r s S α Idx Jdx
      =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
    secChartComp (I := I) (M := M) r s T α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.rfl
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : RSTensorSection I M r s) :
    TensorAEEq (I := I) (M := M) g S S := by
  intro α Idx Jdx
  exact Filter.EventuallyEq.rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.symm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : RSTensorSection I M r s}
    (h : TensorAEEq (I := I) (M := M) g S T) :
    TensorAEEq (I := I) (M := M) g T S := by
  intro α Idx Jdx
  exact (h α Idx Jdx).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.trans
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T U : RSTensorSection I M r s}
    (hST : TensorAEEq (I := I) (M := M) g S T)
    (hTU : TensorAEEq (I := I) (M := M) g T U) :
    TensorAEEq (I := I) (M := M) g S U := by
  intro α Idx Jdx
  exact (hST α Idx Jdx).trans (hTU α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.add
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S₁ S₂ T₁ T₂ : RSTensorSection I M r s}
    (hS : TensorAEEq (I := I) (M := M) g S₁ S₂)
    (hT : TensorAEEq (I := I) (M := M) g T₁ T₂) :
    TensorAEEq (I := I) (M := M) g (S₁ + T₁) (S₂ + T₂) := by
  intro α Idx Jdx
  rw [secChartComp_add (I := I) (M := M),
    secChartComp_add (I := I) (M := M)]
  filter_upwards [hS α Idx Jdx, hT α Idx Jdx] with y hyS hyT
  simp only [Pi.add_apply]
  rw [hyS, hyT]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.smul
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : RSTensorSection I M r s}
    (h : TensorAEEq (I := I) (M := M) g S T) (c : ℝ) :
    TensorAEEq (I := I) (M := M) g (c • S) (c • T) := by
  intro α Idx Jdx
  rw [secChartComp_smul (I := I) (M := M),
    secChartComp_smul (I := I) (M := M)]
  filter_upwards [h α Idx Jdx] with y hy
  simp only [Pi.smul_apply]
  rw [hy]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.neg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : RSTensorSection I M r s}
    (h : TensorAEEq (I := I) (M := M) g S T) :
    TensorAEEq (I := I) (M := M) g (-S) (-T) := by
  simpa only [neg_one_smul] using h.smul (-1 : ℝ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem TensorAEEq.sub
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S₁ S₂ T₁ T₂ : RSTensorSection I M r s}
    (hS : TensorAEEq (I := I) (M := M) g S₁ S₂)
    (hT : TensorAEEq (I := I) (M := M) g T₁ T₂) :
    TensorAEEq (I := I) (M := M) g (S₁ - T₁) (S₂ - T₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hS.add hT.neg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wkpTensorNorm_congr
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S T : RSTensorSection I M r s}
    (hST : TensorAEEq (I := I) (M := M) g S T) :
    wkpTensorNorm (I := I) (M := M) g k p S =
      wkpTensorNorm (I := I) (M := M) g k p T := by
  unfold wkpTensorNorm
  refine tsum_congr ?_
  intro α
  refine Finset.sum_congr rfl ?_
  intro Idx _
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  exact wkpNorm_congr_ae (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α) (hST α Idx Jdx)

def tensorChartSetoid
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Setoid (WkpTensor (I := I) (M := M) g r s k p hp) where
  r S T := TensorAEEq (I := I) (M := M) g S.1 T.1
  iseqv := {
    refl := fun S => TensorAEEq.rfl (I := I) (M := M) g S.1
    symm := fun h => h.symm
    trans := fun hST hTU => hST.trans hTU }

def WkpTensorQuot
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  Quotient (tensorChartSetoid (I := I) (M := M) g r s k p hp)

noncomputable def wkpTensorQNorm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp → ℝ≥0∞ :=
  Quotient.lift
    (fun S : WkpTensor (I := I) (M := M) g r s k p hp =>
      wkpTensorNorm (I := I) (M := M) g k p S.1)
    (fun S T hST =>
      wkpTensorNorm_congr (I := I) (M := M) g hp
        (show TensorAEEq (I := I) (M := M) g S.1 T.1 from hST))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] theorem wkpTensorQNorm_mk
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
      (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S) =
        wkpTensorNorm (I := I) (M := M) g k p S.1 := rfl

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
