import DifferentialGeometry.Geometry.Neck.FiniteAlignment
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Topology.Connected.FiniteCollarOrder

noncomputable section
open Set Topology
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Affine DifferentialGeometry.Geometry.Boundary

namespace DifferentialGeometry.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M]

def cylindricalChart.heightRegion (C : cylindricalChart J (M := M)) (A : Set ℝ) : Set M :=
  C.region {x | (x : S² × ℝ).2 ∈ A}

structure cylindricalChart.signedUnitCollar (C : cylindricalChart J (M := M)) (σ : ℝ) where
  lower : ℝ
  upper : ℝ
  width : 1 ≤ upper - lower
  contained : ∀ p t, t ∈ Icc lower upper → (p, σ * t) ∈ C.domain

def cylindricalChart.signedUnitCollar.map {C : cylindricalChart J (M := M)} {σ : ℝ}
    (K : C.signedUnitCollar σ) (x : S² × Icc K.lower K.upper) : M :=
  C.chart ⟨(x.1, σ * (x.2 : ℝ)), K.contained x.1 x.2 x.2.property⟩

def cylindricalChart.signedUnitCollar.lowerFace {C : cylindricalChart J (M := M)} {σ : ℝ}
    (K : C.signedUnitCollar σ) (p : S²) : M :=
  K.map (p, ⟨K.lower, le_rfl, by linarith only [K.width]⟩)

def cylindricalChart.signedUnitCollar.upperFace {C : cylindricalChart J (M := M)} {σ : ℝ}
    (K : C.signedUnitCollar σ) (p : S²) : M :=
  K.map (p, ⟨K.upper, by linarith only [K.width], le_rfl⟩)

theorem cylindricalChart.signedUnitCollar.continuous_map
    {C : cylindricalChart J (M := M)} {σ : ℝ} (K : C.signedUnitCollar σ) :
    Continuous K.map :=
  continuous_subtype_val.comp (C.chart.continuous.comp
    ((continuous_fst.prodMk (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _))

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
  [IsManifold I ∞ W] [T2Space W]
  [FiniteDimensional ℝ F] [IsManifold J ∞ M] [T2Space M]

structure separatingNeckChain (g : SmoothRiemannianMetric J M) (Cₒ ε : ℝ) (n : ℕ)
    [NeZero n] where
  inclusion : W → M
  smooth_inclusion : ContMDiff I J ∞ inclusion
  embedding : IsEmbedding inclusion
  fullRank : ∀ w, Function.Injective (mfderiv I J inclusion w)
  dimension : Module.finrank ℝ E = Module.finrank ℝ F
  charts : Fin (n + 1) → cylindricalChart J (M := M)
  controlLower : Fin (n + 1) → ℝ
  controlUpper : Fin (n + 1) → ℝ
  control_center : ∀ i, controlLower i < 0 ∧ 0 < controlUpper i
  control_domain : ∀ i, (univ : Set S²) ×ˢ Ioo (controlLower i) (controlUpper i) ⊆ (charts i).domain
  metric_close : ∀ i, (charts i).metricCloseOn g ε
    {x | (x : S² × ℝ).2 ∈ Ioo (controlLower i) (controlUpper i)}
  truncationLower : Fin (n + 1) → ℝ
  truncationUpper : Fin (n + 1) → ℝ
  truncation_order : ∀ i, truncationLower i < truncationUpper i
  truncation_domain : ∀ i, (univ : Set S²) ×ˢ Icc (truncationLower i) (truncationUpper i) ⊆ (charts i).domain
  truncation_cover : range inclusion ⊆ ⋃ i,
    (charts i).heightRegion (Icc (truncationLower i) (truncationUpper i))
  truncation_disjoint : ∀ i j : Fin (n + 1), i.val + 1 < j.val →
    Disjoint ((charts i).heightRegion (Icc (truncationLower i) (truncationUpper i)))
      ((charts j).heightRegion (Icc (truncationLower j) (truncationUpper j)))
  lowerEnd : Set W
  upperEnd : Set W
  boundary : I.boundary W = lowerEnd ∪ upperEnd
  ends_disjoint : Disjoint lowerEnd upperEnd
  lowerEnd_image : inclusion '' lowerEnd = range (fun p : S² ↦
    ((charts 0).chart ⟨(p, 0), control_domain 0 ⟨mem_univ _, control_center 0⟩⟩ : M))
  upperEnd_image : inclusion '' upperEnd = range (fun p : S² ↦
    ((charts (Fin.last n)).chart
      ⟨(p, 0), control_domain (Fin.last n) ⟨mem_univ _, control_center (Fin.last n)⟩⟩ : M))
  lowerEnd_truncation : inclusion '' lowerEnd ⊆
    (charts 0).heightRegion (Icc (truncationLower 0) (truncationUpper 0))
  upperEnd_truncation : inclusion '' upperEnd ⊆ (charts (Fin.last n)).heightRegion
    (Icc (truncationLower (Fin.last n)) (truncationUpper (Fin.last n)))
  sign : Fin n → ℝ
  sourceTranslation : Fin n → ℝ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  overlap : Fin n → Set M
  overlap_compact : ∀ j, IsCompact (overlap j)
  overlap_preconnected : ∀ j, IsPreconnected (overlap j)
  overlap_controlled : ∀ j, overlap j ⊆
    (charts j.castSucc).heightRegion (Ioo (controlLower j.castSucc) (controlUpper j.castSucc)) ∩
    (charts j.succ).heightRegion (Ioo (controlLower j.succ) (controlUpper j.succ))
  overlap_error : ∀ j y, y ∈ overlap j →
    Real.sqrt (charts j.castSucc).scale *
      |(charts j.castSucc).axial y - sign j * (charts j.succ).axial y - sourceTranslation j| +
    Real.sqrt (g.inner y
      (gradFun g (charts j.castSucc).axial y - sign j • gradFun g (charts j.succ).axial y)
      (gradFun g (charts j.castSucc).axial y - sign j • gradFun g (charts j.succ).axial y)) ≤ Cₒ * ε
  origin : Fin n → Fin (n + 1)
  origin_adjacent : ∀ j, origin j = j.castSucc ∨ origin j = j.succ
  collar : ∀ j, (charts (origin j)).signedUnitCollar
    (finiteLineAffineAlignment sign (fun j ↦ -sign j * sourceTranslation j) (origin j)).1
  collar_internal : ∀ j x, (collar j).map x ∈ interior (range inclusion)
  collar_overlap : ∀ j, range (collar j).map ⊆ overlap j
  collar_truncation : ∀ j, range (collar j).map ⊆
    (charts j.castSucc).heightRegion (Icc (truncationLower j.castSucc) (truncationUpper j.castSucc)) ∩
    (charts j.succ).heightRegion (Icc (truncationLower j.succ) (truncationUpper j.succ))
  lowerSide : Fin n → Set W
  upperSide : Fin n → Set W
  lowerSide_closed : ∀ j, IsClosed (lowerSide j)
  upperSide_closed : ∀ j, IsClosed (upperSide j)
  lowerSide_preconnected : ∀ j, IsPreconnected (lowerSide j)
  upperSide_preconnected : ∀ j, IsPreconnected (upperSide j)
  sides_disjoint : ∀ j, Disjoint (lowerSide j) (upperSide j)
  sides_cover : ∀ j, lowerSide j ∪ inclusion ⁻¹' range (collar j).map ∪ upperSide j = univ
  lowerFace_attach : ∀ j, lowerSide j ∩ inclusion ⁻¹' range (collar j).map =
    inclusion ⁻¹' range (collar j).lowerFace
  upperFace_attach : ∀ j, upperSide j ∩ inclusion ⁻¹' range (collar j).map =
    inclusion ⁻¹' range (collar j).upperFace
  lowerEnd_side : ∀ j, lowerEnd ⊆ lowerSide j
  upperEnd_side : ∀ j, upperEnd ⊆ upperSide j
  first_face_order : ∀ x : (charts 0).domain,
    ((charts 0).chart x : M) ∈ range (collar ⟨0, NeZero.pos n⟩).lowerFace →
      0 < (x : S² × ℝ).2
  middle_face_order : ∀ i j : Fin n, i.succ = j.castSucc →
    ∀ x y : (charts i.succ).domain, (x : S² × ℝ).1 = (y : S² × ℝ).1 →
      ((charts i.succ).chart x : M) ∈ range (collar i).upperFace →
      ((charts i.succ).chart y : M) ∈ range (collar j).lowerFace →
        (finiteLineAffineAlignment sign (fun j ↦ -sign j * sourceTranslation j) i.succ).1 *
          (x : S² × ℝ).2 <
        (finiteLineAffineAlignment sign (fun j ↦ -sign j * sourceTranslation j) i.succ).1 *
          (y : S² × ℝ).2
  last_face_order : ∀ x : (charts (Fin.last n)).domain,
    ((charts (Fin.last n)).chart x : M) ∈
      range (collar ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩).upperFace →
        (finiteLineAffineAlignment sign (fun j ↦ -sign j * sourceTranslation j) (Fin.last n)).1 *
          (x : S² × ℝ).2 < 0

end DifferentialGeometry.Geometry.Neck
