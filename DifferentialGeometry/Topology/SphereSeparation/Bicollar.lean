import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Topology.SphereSeparation.LocalSides
import DifferentialGeometry.Topology.SphereSeparation.SameDimension
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere

set_option autoImplicit false

open Function Set
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation

def AxialInterval (a : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-a) a, isOpen_Ioo⟩


def axialZero {a : ℝ} (ha : 0 < a) : AxialInterval a :=
  ⟨0, neg_lt_zero.mpr ha, ha⟩


def negativeHalfDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Iio (axialZero ha)


def zeroSliceDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ {axialZero ha}


def positiveHalfDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Ioi (axialZero ha)


def negativeHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' negativeHalfDomain ha


def zeroSliceImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' zeroSliceDomain ha


def positiveHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' positiveHalfDomain ha

theorem isOpen_negativeHalfImage_of_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Topology.IsOpenEmbedding Φ) :
    IsOpen (negativeHalfImage Φ ha) :=
  hΦ.isOpenMap _ (isOpen_univ.prod isOpen_Iio)

theorem isOpen_positiveHalfImage_of_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Topology.IsOpenEmbedding Φ) :
    IsOpen (positiveHalfImage Φ ha) :=
  hΦ.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)

private theorem negativeAxis_connected {a : ℝ} (ha : 0 < a) :
    IsConnected (Iio (axialZero ha) : Set (AxialInterval a)) := by
  have hI : IsConnected (Ioo (-a) 0) := isConnected_Ioo (neg_lt_zero.mpr ha)
  let _ : ConnectedSpace (Ioo (-a) 0) := Subtype.connectedSpace hI
  let f : Ioo (-a) 0 → AxialInterval a := fun r =>
    ⟨r.1, r.2.1, lt_trans r.2.2 ha⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Iio (axialZero ha) := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.2
    · intro hr
      exact ⟨⟨r.1, r.2.1, hr⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf

private theorem positiveAxis_connected {a : ℝ} (ha : 0 < a) :
    IsConnected (Ioi (axialZero ha) : Set (AxialInterval a)) := by
  have hI : IsConnected (Ioo 0 a) := isConnected_Ioo ha
  let _ : ConnectedSpace (Ioo 0 a) := Subtype.connectedSpace hI
  let f : Ioo 0 a → AxialInterval a := fun r =>
    ⟨r.1, lt_trans (neg_lt_zero.mpr ha) r.2.1, r.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Ioi (axialZero ha) := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.1
    · intro hr
      exact ⟨⟨r.1, hr, r.2.2⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf

theorem isConnected_negativeHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ) :
    IsConnected (negativeHalfImage Φ ha) := by
  exact (isConnected_sphereTwo.prod (negativeAxis_connected ha)).image Φ
    hΦ.continuousOn

theorem isConnected_positiveHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ) :
    IsConnected (positiveHalfImage Φ ha) := by
  exact (isConnected_sphereTwo.prod (positiveAxis_connected ha)).image Φ
    hΦ.continuousOn

theorem bicollar_halves_opposite
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : SphereSides (zeroSliceImage Φ ha)) :
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  have hΦcont : Continuous Φ := hΦ.contMDiff.continuous
  have hneg : IsConnected (negativeHalfImage Φ ha) :=
    isConnected_negativeHalfImage ha Φ hΦcont
  have hpos : IsConnected (positiveHalfImage Φ ha) :=
    isConnected_positiveHalfImage ha Φ hΦcont
  have hnegCompl : negativeHalfImage Φ ha ⊆ (zeroSliceImage Φ ha)ᶜ := by
    intro y hyneg hyzero
    rcases hyneg with ⟨p, hp, rfl⟩
    rcases hyzero with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqzero : q.2 = axialZero ha := hq.2
    have hpneg : p.2 < axialZero ha := hp.2
    rw [← hpq, hqzero] at hpneg
    exact (lt_irrefl _ hpneg)
  have hposCompl : positiveHalfImage Φ ha ⊆ (zeroSliceImage Φ ha)ᶜ := by
    intro y hypos hyzero
    rcases hypos with ⟨p, hp, rfl⟩
    rcases hyzero with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqzero : q.2 = axialZero ha := hq.2
    have hppos : axialZero ha < p.2 := hp.2
    rw [← hpq, hqzero] at hppos
    exact (lt_irrefl _ hppos)
  have hopen : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  have hzeroNonempty : (zeroSliceImage Φ ha).Nonempty := by
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    exact ⟨Φ (p, axialZero ha), ⟨(p, axialZero ha), ⟨hp, rfl⟩, rfl⟩⟩
  have hzeroRange : zeroSliceImage Φ ha ⊆ Set.range Φ := by
    rintro y ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  have hrangeDecomp :
      Set.range Φ ⊆
        (negativeHalfImage Φ ha ∪ zeroSliceImage Φ ha) ∪ positiveHalfImage Φ ha := by
    rintro y ⟨p, rfl⟩
    rcases lt_trichotomy p.2 (axialZero ha) with hp | hp | hp
    · exact Or.inl (Or.inl ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
  exact d.neighborhood_halves_opposite hzeroNonempty hneg hpos
    hnegCompl hposCompl hopen hzeroRange hrangeDecomp

end Poincare.Topology.SphereSeparation
