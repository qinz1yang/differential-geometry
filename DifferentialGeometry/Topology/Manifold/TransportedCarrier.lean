import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# A smooth structure transported to the same points (kernel of LFR47)

Frozen blueprint master207A, lemma `lem:collapse-soul-flow-smooth-carrier` (LFR47, lines
28975–29034), formula (LFR47.1): the smooth structure of a smooth manifold `X` (there: the total
space of the smoothed normal bundle `Ê`) is transported to the SAME underlying space `N` by a
homeomorphism `F : X ≃ₜ N` (there: `F = e ∘ B⁻¹`). In the new carrier `F` is a smooth
diffeomorphism; if `F` is a `C^r` diffeomorphism for the old structure of `N`, the identity
transition between the new and the old carrier is `C^r` in both directions.

`TransportedCarrier F` is a one-field wrapper of the points of `N`; its topology is the topology of
`N` (`TransportedCarrier.homeomorphPoint` is the identity on points), and its charts are those of
`X` pushed along `F` (`DifferentialGeometry.Topology.Handle.chartedSpaceOfHomeomorph`).

* `TransportedCarrier.diffeomorph F : X ≃ₘ⟮IX, IX⟯ TransportedCarrier F`, pointwise `F`;
* `TransportedCarrier.identity F : TransportedCarrier F.toHomeomorph ≃ₘ^r⟮IX, I⟯ N` for a `C^r`
  diffeomorphism `F : X ≃ₘ^r⟮IX, I⟯ N`, pointwise the identity of `N`;
* for a metric space `N`, the same distance (`TransportedCarrier.dist_eq`, an isometry
  `isometryEquivPoint` onto `N`) and the same completeness.

The metric part (pullback of a finite-order metric to the new carrier, its sectional curvature)
is `Geometry/Metric/Pullback/TransportedCarrier.lean`.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe uX uN

/-- The points of `N`, to be equipped with the smooth structure transported from `X` along
`F : X ≃ₜ N`. -/
structure TransportedCarrier {X : Type uX} {N : Type uN} [TopologicalSpace X] [TopologicalSpace N]
    (F : X ≃ₜ N) : Type uN where
  /-- The underlying point of `N`. -/
  point : N

namespace TransportedCarrier

variable {X : Type uX} {N : Type uN} [TopologicalSpace X] [TopologicalSpace N] (F : X ≃ₜ N)

/-- The tautological bijection with the points of `N`. -/
def equivPoint : TransportedCarrier F ≃ N where
  toFun := point
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology of `N`. -/
instance instTopologicalSpace : TopologicalSpace (TransportedCarrier F) :=
  TopologicalSpace.induced point ‹TopologicalSpace N›

/-- The carrier is homeomorphic to `N` by the identity on points. -/
def homeomorphPoint : TransportedCarrier F ≃ₜ N :=
  (equivPoint F).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem homeomorphPoint_apply (y : TransportedCarrier F) :
    homeomorphPoint F y = y.point := rfl

@[simp] theorem homeomorphPoint_symm_apply (y : N) :
    (homeomorphPoint F).symm y = ⟨y⟩ := rfl

instance instT2Space [T2Space N] : T2Space (TransportedCarrier F) :=
  (homeomorphPoint F).isEmbedding.t2Space

instance instCompactSpace [CompactSpace N] : CompactSpace (TransportedCarrier F) :=
  (homeomorphPoint F).symm.compactSpace

instance instConnectedSpace [ConnectedSpace N] : ConnectedSpace (TransportedCarrier F) :=
  (homeomorphPoint F).symm.surjective.connectedSpace (homeomorphPoint F).symm.continuous

/-- The identification of the carrier with `X`: `y ↦ F⁻¹ y`. -/
def toSource : TransportedCarrier F ≃ₜ X :=
  (homeomorphPoint F).trans F.symm

@[simp] theorem toSource_apply (y : TransportedCarrier F) : toSource F y = F.symm y.point := rfl

@[simp] theorem toSource_symm_apply (x : X) : (toSource F).symm x = ⟨F x⟩ := rfl

variable {HX : Type*} [TopologicalSpace HX] [ChartedSpace HX X]

/-- The charts of `X`, pushed to the points of `N` along `F`. -/
instance instChartedSpace : ChartedSpace HX (TransportedCarrier F) :=
  Handle.chartedSpaceOfHomeomorph (toSource F)

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  (IX : ModelWithCorners ℝ EX HX)

instance instIsManifold (n : WithTop ℕ∞) [IsManifold IX n X] :
    IsManifold IX n (TransportedCarrier F) :=
  Handle.isManifoldOfHomeomorph IX (toSource F)

variable {IX}

theorem contMDiff_toSource (n : WithTop ℕ∞) [IsManifold IX n X] :
    ContMDiff IX IX n (toSource F) :=
  Handle.contMDiff_homeomorph_of_chartedSpaceOfHomeomorph (toSource F) IX n

theorem contMDiff_toSource_symm (n : WithTop ℕ∞) [IsManifold IX n X] :
    ContMDiff IX IX n (toSource F).symm :=
  Handle.contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph (toSource F) IX n

/-- **LFR47, smooth half.** In the transported carrier `F` is a smooth diffeomorphism. -/
def diffeomorph [IsManifold IX ∞ X] : X ≃ₘ⟮IX, IX⟯ TransportedCarrier F where
  toEquiv := (toSource F).symm.toEquiv
  contMDiff_toFun := contMDiff_toSource_symm F ∞
  contMDiff_invFun := contMDiff_toSource F ∞

@[simp] theorem diffeomorph_apply [IsManifold IX ∞ X] (x : X) :
    diffeomorph (IX := IX) F x = ⟨F x⟩ := rfl

@[simp] theorem diffeomorph_symm_apply [IsManifold IX ∞ X] (y : TransportedCarrier F) :
    (diffeomorph (IX := IX) F).symm y = F.symm y.point := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H N]

/-- **LFR47, transition.** If `F` is a `C^r` diffeomorphism for the old structure of `N`, the
identity of the points of `N` is a `C^r` diffeomorphism from the transported carrier to the old
one. -/
def identity {r : ℕ∞} [IsManifold IX ∞ X] (F : X ≃ₘ^r⟮IX, I⟯ N) :
    TransportedCarrier F.toHomeomorph ≃ₘ^r⟮IX, I⟯ N where
  toEquiv := equivPoint F.toHomeomorph
  contMDiff_toFun := by
    have h : ContMDiff IX I r (fun y : TransportedCarrier F.toHomeomorph =>
        F (toSource F.toHomeomorph y)) :=
      F.contMDiff.comp ((contMDiff_toSource F.toHomeomorph ∞).of_le (mod_cast le_top))
    refine h.congr fun y => ?_
    change y.point = F (F.symm y.point)
    exact (F.apply_symm_apply y.point).symm
  contMDiff_invFun := by
    have h : ContMDiff I IX r (fun y : N => (toSource F.toHomeomorph).symm (F.symm y)) :=
      ((contMDiff_toSource_symm F.toHomeomorph ∞).of_le (mod_cast le_top)).comp F.symm.contMDiff
    refine h.congr fun y => ?_
    change (⟨y⟩ : TransportedCarrier F.toHomeomorph) = ⟨F (F.symm y)⟩
    rw [F.apply_symm_apply]

@[simp] theorem identity_apply {r : ℕ∞} [IsManifold IX ∞ X] (F : X ≃ₘ^r⟮IX, I⟯ N)
    (y : TransportedCarrier F.toHomeomorph) : identity F y = y.point := rfl

@[simp] theorem identity_symm_apply {r : ℕ∞} [IsManifold IX ∞ X] (F : X ≃ₘ^r⟮IX, I⟯ N)
    (y : N) : (identity F).symm y = ⟨y⟩ := rfl

/-- The transported smooth diffeomorphism followed by the identity transition is `F`. -/
theorem identity_diffeomorph_apply {r : ℕ∞} [IsManifold IX ∞ X] (F : X ≃ₘ^r⟮IX, I⟯ N)
    (x : X) : identity F (diffeomorph (IX := IX) F.toHomeomorph x) = F x := rfl

section Distance

variable {X : Type uX} {N : Type uN} [TopologicalSpace X] [MetricSpace N] (F : X ≃ₜ N)

/-- The distance of `N`: the carrier change does not touch distances. -/
instance instMetricSpace : MetricSpace (TransportedCarrier F) :=
  (MetricSpace.induced point (equivPoint F).injective ‹MetricSpace N›).replaceTopology rfl

@[simp] theorem dist_eq (y z : TransportedCarrier F) : dist y z = dist y.point z.point := rfl

/-- The identity on points is an isometry onto `N`. -/
def isometryEquivPoint : TransportedCarrier F ≃ᵢ N where
  toEquiv := equivPoint F
  isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl

@[simp] theorem isometryEquivPoint_apply (y : TransportedCarrier F) :
    isometryEquivPoint F y = y.point := rfl

/-- Completeness is unchanged. -/
instance instCompleteSpace [CompleteSpace N] : CompleteSpace (TransportedCarrier F) :=
  (isometryEquivPoint F).completeSpace

end Distance

end TransportedCarrier

end DifferentialGeometry.Topology
