import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05WithCarrierMetric
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypesApplications
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization
import DifferentialGeometry.Geometry.Collapse.ZeroModel.UnitMapClassification
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR52Applications
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR54
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowPoint
import DifferentialGeometry.Geometry.Collapse.ZeroModel.SolidTorusZeroModelApplications
import DifferentialGeometry.Topology.VectorBundle.SphereBundleEnds
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# LPA05's sublevel-type clause (LFR54 on the ACTUAL selected sublevels)

Frozen blueprint master207A, LPA05 (A:30548): "Its actual smooth radial sublevels have exactly the
types in LFR54, including their boundaries", and LFR54 (A:29526): `D³`, `S¹ × D²`, `ℝP³ ∖ int D³`,
`D(o(K))`, or the compact types. On LPA05's selection with the carrier and the compact metric
(`lpa05_selected_zero_packets_with_witnesses_withCarrierMetric`) for ORIENTED sources
(`o i : ManifoldOrientation (𝓡 3) (X i) 3`, as in the reordered slim chain), at every selected
centre `c` and every `ρ ∈ [1/5, 2]`, the actual sublevel `A = {η_c ≤ ρ}` of the SAME radial function
is:

* (compact model) the whole source, which is globally diffeomorphic to the compact model and,
  with its orientation, orientation-preservingly diffeomorphic to a closed connected oriented
  three-manifold of one of LFR53's four types (`isCompactNonnegativeType_of_finite_metric` on the
  model with its `C^{K-1}` metric of `sec ≥ 0`, oriented by the source); or
* carried by an ambient partial diffeomorphism `Ψ` onto a disc core `D_T` of the soul bundle
  `D : TotalSpace F V ≃ N_c` of the model, and `D_T` (with its boundary charts) is
  - `ClosedCell 3` (point soul, LFR54-ROW `exists_closedCell_diffeomorph_discCore_of_subsingleton`),
  - `solidTorusCarrier` (circle soul, oriented total space: LFR54-P1
    `exists_solidTorusCarrier_diffeomorph_discCore_of_orientable`),
  - a smooth embedding onto `ℝP³ ∖ (open ball)` or `{Q ≤ 0} = D(o(K))` (surface soul: Q0
    `exists_antipodal_or_klein_unit_map` + `discCore_surface_soul_types_of_unit_map_dichotomy`),
  each with the boundary level `{‖(D⁻¹ ·).2‖ = T}` going onto the model boundary.

The orientation of `TotalSpace F V` is the source orientation pulled back along the open-ball
diffeomorphism of the zero-model ball and the carrier (`nonempty_smoothOrientation_of_ball_chart`);
the preconnected unit sphere bundle that Q0 needs is LC77's at-most-one-end of the SAME model
(`ZeroModelFamily.one_end`, `isPreconnected_sphereBundle_iff`), which also excludes the two
trivial surface rows `S² × [-1, 1]`, `T² × [-1, 1]`; the base metric of `sec ≥ 0` is EXIT-51's.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The source orientation on the soul bundle.** An oriented three-manifold `M`, an open-ball
partial diffeomorphism `Ψ : M ⇀ Ns` onto all of `Ns` and a carrier `D : TotalSpace F V ≃ Ns` orient
the total space (pull-back along the local diffeomorphism `Ψ⁻¹ ∘ D`). -/
theorem nonempty_smoothOrientation_of_ball_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
    (o : ManifoldOrientation I3 M 3)
    {Ns : Type*} [TopologicalSpace Ns] [ChartedSpace E3 Ns]
    (Ψ : PartialDiffeomorph I3 I3 M Ns ∞) (hΨ : Ψ.target = univ)
    {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V IB]
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞) :
    Nonempty (SmoothOrientation (IB.prod 𝓘(ℝ, F)) (TotalSpace F V)) := by
  let o' : ManifoldOrientation I3 M (Module.finrank ℝ E3) :=
    Eq.rec (motive := fun m _ => ManifoldOrientation I3 M m) o o.dimension_eq.symm
  let oM := smoothOrientationOfManifoldOrientation I3 o'
  have hloc : IsLocalDiffeomorph (IB.prod 𝓘(ℝ, F)) I3 ∞ (fun z => Ψ.symm (D z)) := fun z =>
    (D.isLocalDiffeomorph z).comp (hg := PartialDiffeomorph.isLocalDiffeomorphAt I3 I3 ∞
      Ψ.symm (by rw [PartialDiffeomorph.symm_source, hΨ]; exact mem_univ _))
  have hbij : ∀ z, Bijective (mfderiv (IB.prod 𝓘(ℝ, F)) I3 (fun z => Ψ.symm (D z)) z) := by
    intro z
    obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv (by simp) z
    rw [← hL]
    exact L.bijective
  exact ⟨pullbackSmoothOrientation (IB.prod 𝓘(ℝ, F)) I3 _ hloc.contMDiff hbij oM⟩

/-- **LFR53 on a compact model reached by a global diffeomorphism.** An oriented connected
three-manifold `M` diffeomorphic to a compact model `Nc` carrying a `C^n` metric of `sec ≥ 0`,
`2 ≤ n`, is orientation-preservingly diffeomorphic to a closed connected oriented three-manifold of
one of LFR53's four types: `Nc` with the orientation pushed forward from `M`. -/
theorem exists_compactNonnegativeType_of_diffeomorph
    {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [ConnectedSpace M]
    (oM : ManifoldOrientation I3 M 3)
    {Nc : Type} [TopologicalSpace Nc] [T2Space Nc] [CompactSpace Nc] [ChartedSpace E3 Nc]
    [IsManifold I3 ∞ Nc] (Φ : Diffeomorph I3 I3 M Nc ∞) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (G : ContMDiffRiemannianMetric I3 n E3 (TangentSpace I3 : Nc → Type _))
    (hG : ∀ (x : Nc) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) :
    ∃ P : ConnectedClosedOrientedManifold.{0} 3, IsCompactNonnegativeType P ∧
      ∃ Φ' : Diffeomorph I3 I3 M P.Carrier ∞, Φ'.preservesOrientation oM P.orientation := by
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_diffeomorph_map Φ oM
  have instConn_LPA02b : ConnectedSpace Nc := Φ.toHomeomorph.connectedSpace_iff.mp inferInstance
  let P : ConnectedClosedOrientedManifold.{0} 3 := { Carrier := Nc, orientation := O }
  refine ⟨P, isCompactNonnegativeType_of_finite_metric P hn G hG, Φ, fun x => ?_⟩
  change _ = O.orientation (Φ x)
  rw [hO]
  dsimp only
  rw [Φ.symm_apply_apply]

/-- **Closed model, LFR53 type.** `A` is the whole source `M`, the compact model `Nc` is globally
diffeomorphic to `M`, and `M` with its orientation is orientation-preservingly diffeomorphic to a
closed connected oriented three-manifold of one of LFR53's four types (spherical space form,
`S² × S¹`, `ℝP³ # ℝP³`, compact orientable flat). (A conclusion predicate of
`lpa05_selected_sublevel_types_withCarrier`; it is never assumed.) -/
def CompactModelSublevel {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
    (oM : ManifoldOrientation I3 M 3) (Nc : Type) [TopologicalSpace Nc] [ChartedSpace E3 Nc]
    (A : Set M) : Prop :=
  A = univ ∧ CompactSpace Nc ∧ Nonempty (Diffeomorph I3 I3 M Nc ∞) ∧
    ∃ P : ConnectedClosedOrientedManifold.{0} 3, IsCompactNonnegativeType P ∧
      ∃ Φ : Diffeomorph I3 I3 M P.Carrier ∞, Φ.preservesOrientation oM P.orientation

/-- **`D³`.** `A` is carried by an ambient partial diffeomorphism onto a disc core `D_T` of a point-soul
bundle `D : TotalSpace F V ≃ Nc` (base `Fin 0 → ℝ`), and `D_T ≅ ClosedCell 3`, boundary onto the
boundary sphere. (A conclusion predicate of `lpa05_selected_sublevel_types_withCarrier`; it is never
assumed.) -/
def PointSoulCoreSublevel {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] (Nc : Type) [TopologicalSpace Nc]
    [ChartedSpace E3 Nc] (A : Set M) : Prop :=
  ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
    (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
    (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
    (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
    (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
    (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
    (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
    (hd : Module.finrank ℝ ((Fin 0 → ℝ) × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
    A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
    letI := discCoreChartedSpace D hd T₀ hT₀
    letI := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {y : Nc // ‖(D.symm y).2‖ ≤ T₀} (ClosedCell 3) ∞,
      (∀ y, T₀ * ‖(Φ y).val‖ = ‖(D.symm y.val).2‖) ∧
      ∀ y, ‖(D.symm y.val).2‖ = T₀ ↔ ‖(Φ y).val‖ = 1

/-- **`S¹ × D²`.** `A` is carried by an ambient partial diffeomorphism onto a disc core `D_T` of a
circle-soul bundle over `AddCircle 1`, and `solidTorusCarrier ≅ D_T`, boundary torus onto the
boundary level. (A conclusion predicate of `lpa05_selected_sublevel_types_withCarrier`; it is never
assumed.) -/
def CircleSoulCoreSublevel {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] (Nc : Type) [TopologicalSpace Nc]
    [ChartedSpace E3 Nc] (A : Set M) : Prop :=
  ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
    (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
    (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
    (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
    (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
    (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
    (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
    (hd : Module.finrank ℝ (ℝ × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
    A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
    letI := discCoreChartedSpace D hd T₀ hT₀
    ∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{0}.model
        (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{0}.Carrier
        {y : Nc // ‖(D.symm y).2‖ ≤ T₀} ∞,
      ∀ y : GC.GraphManifold.solidTorusCarrier.{0}.Carrier,
        GC.GraphManifold.cliffordHeight (y : GC.GraphManifold.solidTorusSet.{0}).val = 0 ↔
          ‖(D.symm (Φ y).val).2‖ = T₀

/-- **`ℝP³ ∖ int D³`.** `A` is carried by an ambient partial diffeomorphism onto a disc core `D_T` of a
surface-soul bundle (base on `𝓡 2`), and `D_T` embeds smoothly onto `ℝP³ ∖ (open ball)`, boundary
onto the boundary sphere. (A conclusion predicate of `lpa05_selected_sublevel_types_withCarrier`; it is never
assumed.) -/
def ProjectiveSoulCoreSublevel {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] (Nc : Type) [TopologicalSpace Nc]
    [ChartedSpace E3 Nc] (A : Set M) : Prop :=
  ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B) (_ : IsManifold (𝓡 2) ∞ B)
    (_ : CompactSpace B) (_ : T2Space B) (_ : ConnectedSpace B),
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
      (_ : FiniteDimensional ℝ F) (V : B → Type)
      (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
      (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
      (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
      (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
      (hd : Module.finrank ℝ (E2 × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
      (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
      A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      letI := discCoreChartedSpace D hd T₀ hT₀
      ∃ (cb : OrientedBallChart projectiveThreeSpaceLift.{0}.toClosedOrientedManifold)
        (f : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} → projectiveThreeSpaceLift.{0}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {w | w ∉ cb.chart '' Metric.ball (0 : E3) 1} ∧
        ∀ y, f y ∈ cb.chart '' Metric.sphere (0 : E3) 1 ↔ ‖(D.symm y.val).2‖ = T₀

/-- **`D(o(K))`.** `A` is carried by an ambient partial diffeomorphism onto a disc core `D_T` of a
surface-soul bundle (base on `𝓡 2`), and `D_T ≅ {Q ≤ 0} = mobiusBundleSet`, boundary onto `{Q = 0}`. (A conclusion predicate of `lpa05_selected_sublevel_types_withCarrier`; it is never
assumed.) -/
def KleinSoulCoreSublevel {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] (Nc : Type) [TopologicalSpace Nc]
    [ChartedSpace E3 Nc] (A : Set M) : Prop :=
  ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B) (_ : IsManifold (𝓡 2) ∞ B)
    (_ : CompactSpace B) (_ : T2Space B) (_ : ConnectedSpace B),
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
      (_ : FiniteDimensional ℝ F) (V : B → Type)
      (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
      (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
      (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
      (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
      (hd : Module.finrank ℝ (E2 × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
      (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
      A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      letI := discCoreChartedSpace D hd T₀ hT₀
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {y : Nc // ‖(D.symm y).2‖ ≤ T₀} GC.Seifert.mobiusBundleSet.{0} ∞,
        ∀ y, ‖(D.symm y.val).2‖ = T₀ ↔ GC.Seifert.mobiusBundleFunction (Φ y).val = 0

/-- **LPA05's sublevel-type clause.** For ORIENTED sources, in LPA05's selection with the carrier,
every actual sublevel `{η_c ≤ ρ}`, `ρ ∈ [1/5, 2]`, of every selected zero-model ball is the whole
source (compact model, globally diffeomorphic to it; the oriented source has one of LFR53's four
types) or is carried by an ambient partial
diffeomorphism onto a disc core of the soul bundle that is `ClosedCell 3`, `solidTorusCarrier`,
`ℝP³ ∖ (open ball)` (smooth embedding) or `{Q ≤ 0} = D(o(K))`, boundary onto boundary. -/
theorem lpa05_selected_sublevel_types_withCarrier
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
      [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (_ : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ oX : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∃ (N C : X i → Type) (_ : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (_ : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          ∀ c (hc : c ∈ Z.centres), ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            CompactModelSublevel (oX i) (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            PointSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            CircleSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            ProjectiveSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            KleinSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} := by
  have hLFR54 := ZeroModel.lfr54_classified_finite_zero_packet.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    lpa05_selected_zero_packets_with_witnesses_withCarrierMetric hβ hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder oX Λ w hΛ hw hwc
  obtain ⟨V₀, hTV, δ₀, hδ0, hδδ', hW⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand K hK A hA
    hder Λ w hΛ hw hwc
  refine ⟨V₀, hTV, δ₀, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi ρ hρ hρc hρw
  obtain ⟨N, C, mN, cN, hMN, mC, o, u, hmodels, Z, hcore, -⟩ := hi ρ hρ hρc hρw
  refine ⟨N, C, mN, cN, hMN, mC, o, Z, fun c hc ρ' hρ' => ?_⟩
  obtain ⟨T₀, hT₀, Ψ, hΨs, hΨi⟩ := hcore c hc ρ' hρ'
  obtain ⟨hpN, -, -, -, hcases, -⟩ := hmodels (Z.zero c hc).model
  have h1 : (1 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hballT := (Z.zero c hc).modelChart_target 1 h1
  rcases hcases with ⟨hcpt, hu, Gc, hGc⟩ | ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF3, hu⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF2, hu⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF1, hu, nB,
        hnB, kB, hkB⟩
  · -- compact model: the sublevel is the whole source
    left
    obtain ⟨hlip, -, -, -, -, -, hc0, -⟩ := (Z.zero c hc).radial_spec
    have hηc : Continuous (Z.zero c hc).radial :=
      @LipschitzWith.continuous (X i) ℝ ((mX i).rescale ((Z.zero c hc).radius)⁻¹
        (inv_pos.mpr (Z.zero c hc).radius_pos)).toPseudoEMetricSpace _ _ _ hlip
    have hAcl : IsClosed {x | (Z.zero c hc).radial x ≤ ρ'} := isClosed_le hηc continuous_const
    have huniv : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = univ := by
      rw [hΨi]
      exact eq_univ_of_forall fun y => by
        change u (Z.zero c hc).model y ≤ T₀
        rw [hu y]
        exact hT₀.le
    have hsrc : Ψ.source = {x | (Z.zero c hc).radial x ≤ ρ'} := by
      refine Subset.antisymm (fun x hx => ?_) hΨs
      have hy : Ψ x ∈ Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} := by
        rw [huniv]
        exact mem_univ _
      obtain ⟨a, ha, hax⟩ := hy
      have hax' := Ψ.toPartialEquiv.injOn (hΨs ha) hx hax
      rw [← hax']
      exact ha
    have hne : ({x | (Z.zero c hc).radial x ≤ ρ'} : Set (X i)).Nonempty :=
      ⟨(Z.zero c hc).center, by
        change (Z.zero c hc).radial (Z.zero c hc).center ≤ ρ'
        rw [hc0]
        linarith [hρ'.1]⟩
    have instConn_LPA02 : ConnectedSpace (X i) :=
      connectedSpace_of_aligned_metric (g i) (hmetric i) (Z.zero c hc).center
    have hunivA : {x | (Z.zero c hc).radial x ≤ ρ'} = univ :=
      IsClopen.eq_univ ⟨hAcl, hsrc ▸ Ψ.open_source⟩ hne
    have htgt : Ψ.target = univ := by
      rw [← Ψ.toPartialEquiv.image_source_eq_target]
      rw [hsrc, huniv]
    have instCpt_LPA02b : CompactSpace (N (Z.zero c hc).model) := hcpt
    let Φ := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv Ψ
      (hsrc.trans hunivA) htgt
    exact ⟨hunivA, hcpt, ⟨Φ⟩, exists_compactNonnegativeType_of_diffeomorph (oX i) Φ
      (by exact_mod_cast (show 2 ≤ K - 1 by omega)) Gc hGc⟩
  · -- point soul
    right; left
    have hd : Module.finrank ℝ ((Fin 0 → ℝ) × F) = 2 + 1 := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, hF3]
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨Φ, hΦ1, hΦ2⟩ := hLFR54.1 (B := Fin 0 → ℝ) hd (Module.finrank_fin_fun ℝ) D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ1,
      hΦ2⟩
  · -- circle soul
    right; right; left
    have hd : Module.finrank ℝ (ℝ × F) = 2 + 1 := finrank_real_prod_eq_three hF2
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oV⟩ := nonempty_smoothOrientation_of_ball_chart (oX i)
      ((Z.zero c hc).modelChart 1 h1) hballT D
    obtain ⟨Φ, hΦ⟩ := hLFR54.2.1 hF2 oV D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩
  · -- surface soul
    right; right; right
    have hd : Module.finrank ℝ (E2 × F) = 2 + 1 := by
      rw [Module.finrank_prod, finrank_euclideanSpace_fin, hF1]
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oN⟩ := nonempty_smoothOrientation_of_ball_chart (oX i)
      ((Z.zero c hc).modelChart 1 h1) hballT D
    have instP_LPA02 : ProperSpace (N (Z.zero c hc).model) := hpN
    rcases hLFR54.2.2.1 hd oN hnB kB hkB D (Z.one_end c hc) T₀ hT₀ with
      ⟨cb, f, hf1, hf2, hf3⟩ | ⟨Φ, hΦ⟩
    · left
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', cb, f, hf1, hf2, hf3⟩
    · right
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩

end DifferentialGeometry.Geometry.Collapse
