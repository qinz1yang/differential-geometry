import DifferentialGeometry.Analysis.Schauder.Composition
import DifferentialGeometry.Analysis.Schauder.Interpolation
import DifferentialGeometry.Analysis.Schauder.Localization
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

def parabolicExtChartRepresentation
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    Real → E → F :=
  fun t y ↦ u t ((extChartAt I x₀).symm y)

def parabolicEuclideanChartRepresentation
    [FiniteDimensional Real E]
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    Real → EuclideanSpace Real (Fin (Module.finrank Real E)) → F :=
  fun t y ↦ u t ((extChartAt I x₀).symm ((toEuclidean (E := E)).symm y))

omit [NormedAddCommGroup F] [NormedSpace Real F] in
@[simp]
theorem parabolicExtChartRepresentation_apply
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F)
    (t : Real) (y : E) :
    parabolicExtChartRepresentation I x₀ u t y =
      u t ((extChartAt I x₀).symm y) := by
  rfl

omit [NormedAddCommGroup F] [NormedSpace Real F] in
@[simp]
theorem parabolicEuclideanChartRepresentation_apply
    [FiniteDimensional Real E]
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F)
    (t : Real) (y : EuclideanSpace Real (Fin (Module.finrank Real E))) :
    parabolicEuclideanChartRepresentation I x₀ u t y =
      u t ((extChartAt I x₀).symm ((toEuclidean (E := E)).symm y)) := by
  rfl

theorem exists_finite_buffered_euclidean_chart_cover
    [FiniteDimensional Real E] [I.Boundaryless] [CompactSpace M] :
    ∃ s : Finset M, ∃ r R Rext : M → Real,
      (∀ x ∈ s, 0 < r x ∧ r x < R x ∧ R x < Rext x) ∧
      (∀ x ∈ s,
        (toEuclidean (E := E)).symm ''
            Metric.closedBall (toEuclidean (extChartAt I x x)) (Rext x) ⊆
          (extChartAt I x).target) ∧
      ∀ y : M, ∃ x ∈ s,
        y ∈ (extChartAt I x).source ∧
          toEuclidean (extChartAt I x y) ∈
            Metric.ball (toEuclidean (extChartAt I x x)) (r x) := by
  classical
  have hlocal : ∀ x : M, ∃ ε : Real, 0 < ε ∧
      Euclidean.ball (extChartAt I x x) ε ⊆ (extChartAt I x).target := by
    intro x
    exact Euclidean.nhds_basis_ball.mem_iff.mp
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  choose ε hε hball using hlocal
  let r : M → Real := fun x ↦ ε x / 4
  let R : M → Real := fun x ↦ ε x / 2
  let Rext : M → Real := fun x ↦ 3 * ε x / 4
  let U : M → Set M := fun x ↦
    (extChartAt I x).source ∩
      (extChartAt I x) ⁻¹' Euclidean.ball (extChartAt I x x) (r x)
  have hUopen : ∀ x : M, IsOpen (U x) := by
    intro x
    exact (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) Euclidean.isOpen_ball
  have hUself : ∀ x : M, x ∈ U x := by
    intro x
    refine ⟨mem_extChartAt_source x, ?_⟩
    change extChartAt I x x ∈ Euclidean.ball (extChartAt I x x) (r x)
    apply Euclidean.mem_ball_self
    exact div_pos (hε x) (by norm_num)
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hUself x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  refine ⟨s, r, R, Rext, ?_, ?_, ?_⟩
  · intro x hx
    dsimp only [r, R, Rext]
    constructor
    · exact div_pos (hε x) (by norm_num)
    constructor <;> nlinarith [hε x]
  · intro x hx
    rw [← Euclidean.closedBall_eq_image]
    exact fun y hy ↦ hball x (by
      dsimp [Euclidean.closedBall, Euclidean.ball, Rext] at hy ⊢
      linarith [hε x])
  · intro y
    rcases Set.mem_iUnion₂.mp (hs (Set.mem_univ y)) with ⟨x, hxs, hyU⟩
    exact ⟨x, hxs, hyU.1, hyU.2⟩

def IsParabolicC2InEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} (I : ModelWithCorners Real E H) (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : Prop :=
  ∀ i, IsParabolicC2On (Q i)
    (parabolicEuclideanChartRepresentation I (center i) u)

namespace IsParabolicC2InEuclideanChartsOn

theorem mono
    [FiniteDimensional Real E]
    {A : Type*} {center : A → M}
    {Q R : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    (hQR : ∀ i, Q i ⊆ R i) {u : Real → M → F}
    (hu : IsParabolicC2InEuclideanChartsOn I center R u) :
    IsParabolicC2InEuclideanChartsOn I center Q u := by
  intro i
  exact ⟨fun p hp => (hu i).1 p (hQR i hp),
    fun p hp => (hu i).2 p (hQR i hp)⟩

end IsParabolicC2InEuclideanChartsOn

def eParabolicC2HolderGaugeInExtChartOn
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint E)) (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (parabolicExtChartRepresentation I x₀ u)

def eParabolicC2HolderGaugeInEuclideanChartOn
    [FiniteDimensional Real E]
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (parabolicEuclideanChartRepresentation I x₀ u)

def eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint E)) (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
    (parabolicExtChartRepresentation I x₀ u)

def eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
    [FiniteDimensional Real E]
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
    (parabolicEuclideanChartRepresentation I x₀ u)

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartOn_le_mul_of_nested_balls
    {J : Set Real} (hJ : Convex Real J) (x₀ : M) (center : E)
    {r R : Real} (hrR : r < R) {alpha : NNReal} (halpha : alpha ≤ 1)
    {u : Real → M → F}
    (hu : IsParabolicC2On (parabolicCylinder J (Metric.ball center R))
      (parabolicExtChartRepresentation I x₀ u)) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartOn alpha I x₀
        (parabolicCylinder J (Metric.closedBall center r)) u ≤
      bufferedParabolicC2HolderGaugeWithLowerJetsFactor
          (Real.toNNReal (R - r)) *
        eParabolicC2HolderGaugeInExtChartOn alpha I x₀
          (parabolicCylinder J (Metric.ball center R)) u := by
  exact eParabolicC2HolderGaugeWithLowerJetsOn_le_mul_of_nested_balls
    hJ center hrR halpha hu

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_mul_of_nested_balls
    [FiniteDimensional Real E]
    {J : Set Real} (hJ : Convex Real J) (x₀ : M)
    (center : EuclideanSpace Real (Fin (Module.finrank Real E)))
    {r R : Real} (hrR : r < R) {alpha : NNReal} (halpha : alpha ≤ 1)
    {u : Real → M → F}
    (hu : IsParabolicC2On (parabolicCylinder J (Metric.ball center R))
      (parabolicEuclideanChartRepresentation I x₀ u)) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn alpha I x₀
        (parabolicCylinder J (Metric.closedBall center r)) u ≤
      bufferedParabolicC2HolderGaugeWithLowerJetsFactor
          (Real.toNNReal (R - r)) *
        eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀
          (parabolicCylinder J (Metric.ball center R)) u := by
  exact eParabolicC2HolderGaugeWithLowerJetsOn_le_mul_of_nested_balls
    hJ center hrR halpha hu

theorem eParabolicC2HolderGaugeInExtChartOn_le_with_lower_jets
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint E)) (u : Real → M → F) :
    eParabolicC2HolderGaugeInExtChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInExtChartOn alpha I x₀ Q u :=
  eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _

theorem eParabolicC2HolderGaugeInEuclideanChartOn_le_with_lower_jets
    [FiniteDimensional Real E]
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I x₀ Q u :=
  eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _

theorem eParabolicC2HolderGaugeInExtChartOn_mono
    {Q R : Set (ParabolicPoint E)} (hQR : Q ⊆ R)
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (u : Real → M → F) :
    eParabolicC2HolderGaugeInExtChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeInExtChartOn alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeInEuclideanChartOn_mono
    [FiniteDimensional Real E]
    {Q R : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    (hQR : Q ⊆ R) (alpha : NNReal)
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartOn_mono
    {Q R : Set (ParabolicPoint E)} (hQR : Q ⊆ R)
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (u : Real → M → F) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInExtChartOn alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeWithLowerJetsOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_mono
    [FiniteDimensional Real E]
    {Q R : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    (hQR : Q ⊆ R) (alpha : NNReal)
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeWithLowerJetsOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeInExtChartOn_eq_of_coordinate_representation
    [I.Boundaryless]
    {x₀ : M} {J : Set Real} (hJ : IsOpen J) {Q : Set (ParabolicPoint E)}
    (hQ : Q ⊆ parabolicCylinder J (extChartAt I x₀).target)
    (alpha : NNReal) (u : Real → M → F) (v : Real → E → F)
    (hv : ∀ t ∈ J, ∀ y ∈ (extChartAt I x₀).target,
      v t y = u t ((extChartAt I x₀).symm y)) :
    eParabolicC2HolderGaugeInExtChartOn alpha I x₀ Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  unfold eParabolicC2HolderGaugeInExtChartOn
  apply eParabolicC2HolderGaugeOn_congr_of_eqOn_open
    (isOpen_parabolicCylinder hJ (isOpen_extChartAt_target (I := I) x₀)) hQ
  intro p hp
  exact (hv p.time hp.1 p.space hp.2).symm

def eParabolicC2HolderGaugeInExtChartsOn
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u

def eParabolicC2HolderGaugeInEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center i) (Q i) u

def eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
    alpha I (center i) (Q i) u

def eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
    alpha I (center i) (Q i) u

theorem eParabolicC2HolderGaugeInExtChartsOn_le_with_lower_jets
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) :
    eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
        alpha I center Q u := by
  apply iSup_mono
  intro i
  exact eParabolicC2HolderGaugeInExtChartOn_le_with_lower_jets
    alpha I (center i) (Q i) u

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_with_lower_jets
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q u := by
  apply iSup_mono
  intro i
  exact eParabolicC2HolderGaugeInEuclideanChartOn_le_with_lower_jets
    alpha I (center i) (Q i) u

theorem eParabolicC2HolderGaugeInExtChartOn_le_extCharts
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeInExtChartOn alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeInEuclideanChartOn_le_euclideanCharts
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartOn_le_extCharts
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
        alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
        alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
      alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_euclideanCharts
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
      alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeInExtChartsOn_le_iff
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_iff
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
        alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn_le_iff
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
        alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
        alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_iff
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeInExtChartsOn_le_iSup
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : A → ENNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInExtChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u ≤
      ⨆ i, C i := by
  apply iSup_mono
  exact h

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_iSup
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → ENNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤
      ⨆ i, C i := by
  apply iSup_mono
  exact h

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn_le_iSup
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : A → ENNReal)
    (h : ∀ i, eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
        alpha I center Q u ≤
      ⨆ i, C i := by
  apply iSup_mono
  exact h

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_iSup
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → ENNReal)
    (h : ∀ i, eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q u ≤
      ⨆ i, C i := by
  apply iSup_mono
  exact h

theorem eParabolicC2HolderGaugeInExtChartsOn_le_sum_of_finite
    {A : Type*} [Fintype A]
    (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : A → NNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInExtChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u ≤
      ∑ i, C i := by
  classical
  unfold eParabolicC2HolderGaugeInExtChartsOn
  apply iSup_le
  intro i
  exact (h i).trans
    (ENNReal.coe_le_coe.mpr
      (Finset.single_le_sum (fun j _ ↦ zero_le (C j)) (Finset.mem_univ i)))

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_sum_of_finite
    [FiniteDimensional Real E]
    {A : Type*} [Fintype A]
    (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → NNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤
      ∑ i, C i := by
  classical
  unfold eParabolicC2HolderGaugeInEuclideanChartsOn
  apply iSup_le
  intro i
  exact (h i).trans
    (ENNReal.coe_le_coe.mpr
      (Finset.single_le_sum (fun j _ ↦ zero_le (C j)) (Finset.mem_univ i)))

theorem eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn_le_sum_of_finite
    {A : Type*} [Fintype A]
    (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : A → NNReal)
    (h : ∀ i, eParabolicC2HolderGaugeWithLowerJetsInExtChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
        alpha I center Q u ≤
      ∑ i, C i := by
  classical
  unfold eParabolicC2HolderGaugeWithLowerJetsInExtChartsOn
  apply iSup_le
  intro i
  exact (h i).trans
    (ENNReal.coe_le_coe.mpr
      (Finset.single_le_sum (fun j _ ↦ zero_le (C j)) (Finset.mem_univ i)))

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_sum_of_finite
    [FiniteDimensional Real E]
    {A : Type*} [Fintype A]
    (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → NNReal)
    (h : ∀ i, eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q u ≤
      ∑ i, C i := by
  classical
  unfold eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
  apply iSup_le
  intro i
  exact (h i).trans
    (ENNReal.coe_le_coe.mpr
      (Finset.single_le_sum (fun j _ ↦ zero_le (C j)) (Finset.mem_univ i)))

end DifferentialGeometry.Analysis.Schauder

end
