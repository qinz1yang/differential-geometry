import DifferentialGeometry.Geometry.Hyperbolic.Cusps.ApproximationThinness
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.HeightDistance
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Section
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Diameter
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.MetricSpace.Bounded
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.ImageGraph
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphExtension
import DifferentialGeometry.Geometry.Hyperbolic.Ends
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphRegion
import DifferentialGeometry.Geometry.Hyperbolic.ApproximationThickness
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.ThinRegionCapture
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.CoreAvoidance

noncomputable section

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace manifold_semilocallySimplyConnectedSpace)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
private theorem cylindricalCore_homeomorph
    {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C : ι → Type*}
    (e : ∀ i, C i × Set.Ici (0 : ℝ) → X) (F : X ≃ₜ Y) (R : ι → ℝ) :
    Topology.cylindricalCore (fun i z => F (e i z)) R = F '' Topology.cylindricalCore e R := by
  simp only [Topology.cylindricalCore, F.image_compl, Set.image_iUnion, Set.image_image]

private theorem compact_cylindricalCore_of_compact_core
    {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (ProjectiveOrthogonalGroup.PO n 1)} {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))
    (d : ℝ) (hd : 0 ≤ d) :
    IsCompact (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) (fun _ => d)) := by
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (CuspCrossSections.endStabilizer hn Γ {ξ.val}) (DifferentialGeometry.Hyperbolic.HUpper n) _
      (EquivariantMap.subAction hn (CuspCrossSections.endStabilizer hn Γ {ξ.val})))) ''
        Busemann.horosphere ξ.val (D.level ξ)
  let _ : Finite D.centers := D.finite_centers
  let _ : ∀ ξ : D.centers, CompactSpace (C ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  apply Topology.isCompact_cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ) (D.isOpen_image_horoballCylinderMap_pos hΓ)
  · rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  · exact fun _ => hd

private theorem source_cylindricalCore_properties
    {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (ProjectiveOrthogonalGroup.PO n 1)} {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))
    {Y : Type*} [TopologicalSpace Y]
    (F : @MulAction.orbitRel.Quotient Γ (DifferentialGeometry.Hyperbolic.HUpper n) _
      (EquivariantMap.subAction hn Γ) ≃ₜ Y) (o : Y) :
    let e (ξ : D.centers) := fun z => F (D.horoballCylinderMap hΓ ξ z)
    (∀ d : ℝ, 0 ≤ d → IsCompact (Topology.cylindricalCore e (fun _ => d))) ∧
    (∃ B : ℝ, ∀ d : ℝ, B < d → o ∈ interior (Topology.cylindricalCore e (fun _ => d))) ∧
    (∀ d : Set.Ici (0 : ℝ), ∀ ξ : D.centers, ∀ c,
      e ξ (c,d) ∈ Topology.cylindricalCore e (fun _ => d.val)) := by
  let _ : Finite D.centers := D.finite_centers
  let f (ξ : D.centers) := D.horoballCylinderMap hΓ ξ
  let e (ξ : D.centers) := fun z => F (f ξ z)
  have hcore (R : D.centers → ℝ) : Topology.cylindricalCore e R = F '' Topology.cylindricalCore (fun ξ => f ξ) R :=
    cylindricalCore_homeomorph (fun ξ => f ξ) F R
  have hcenter (d : Set.Ici (0 : ℝ)) (ξ : D.centers) (c) :
      e ξ (c,d) ∈ Topology.cylindricalCore e (fun _ => d.val) := by
    rw [hcore]
    exact ⟨f ξ (c,d), (Topology.mem_cylindricalCore_image_iff (fun ξ => f ξ)
      (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
      (D.pairwise_disjoint_range_horoballCylinderMap hΓ) (fun _ => d.val) ξ (c,d)).mpr le_rfl, rfl⟩
  have hB : ∃ B : ℝ, F.symm o ∈ Topology.cylindricalCore (fun ξ => f ξ) (fun _ => B) := by
    by_cases ho : ∃ ξ : D.centers, ∃ z, f ξ z = F.symm o
    · obtain ⟨ξ, z, hz⟩ := ho
      refine ⟨z.2.val, ?_⟩
      rw [← hz]
      exact (Topology.mem_cylindricalCore_image_iff (fun ξ => f ξ)
        (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
        (D.pairwise_disjoint_range_horoballCylinderMap hΓ) (fun _ => z.2.val) ξ z).mpr le_rfl
    · refine ⟨0, ?_⟩
      intro hm
      obtain ⟨ξ, z, _, hz⟩ := Set.mem_iUnion.mp hm
      exact ho ⟨ξ, z, hz⟩
  obtain ⟨B, hB⟩ := hB
  refine ⟨fun d hd => ?_, ⟨B, fun d hd => ?_⟩, hcenter⟩
  · rw [hcore]
    exact (compact_cylindricalCore_of_compact_core D hΓ d hd).image F.continuous
  · rw [hcore, ← F.image_interior]
    exact ⟨F.symm o, Topology.cylindricalCore_subset_interior_of_lt (fun ξ => f ξ)
      (D.horoballCylinderMap_isClosedEmbedding hΓ) (fun _ => B) (fun _ => d) (fun _ => hd) hB,
      F.apply_symm_apply o⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g) (x₀ : M)
  (hsec : ∀ (x : M) (v w : TangentSpace I x),
    Curvature.metricRm04StandardAt g x v w w v =
      (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem eventually_source_horosphere_diameter_le :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r),
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      ∀ᶠ t : ℝ in Filter.atTop, ∀ ξ : D.centers,
        Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - t)) ≤ ENNReal.ofReal (1 / 10) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i r D
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    have hρ : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    dsimp only [σ]
    rw [MonoidHom.range_comp]
    exact hρ.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let F := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}) H₃ _
      (EquivariantMap.subAction (by decide : 1 ≤ 3) (CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val})))) ''
      Busemann.horosphere ξ.val (D.level ξ)
  let _ : Finite D.centers := D.finite_centers
  let _ : ∀ ξ : D.centers, CompactSpace (C ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hdiam : ∀ᶠ t : ℝ in Filter.atTop, ∀ ξ : D.centers,
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - t)) ≤ ENNReal.ofReal (1 / 10) := by
    apply Filter.eventually_all.mpr
    intro ξ
    let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}
    have hinv (γ : P) (z : H₃) :
        pH ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (γ : ProjectiveOrthogonalGroup.PO 3 1) z) = pH z := by
      rw [← normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i,
        ← normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i]
      apply congrArg F
      exact Quotient.sound ⟨⟨γ.val, γ.property.1⟩, rfl⟩
    have hlim := HorosphereProjection.tendsto_ediam_image_horosphere (by decide : 1 ≤ 3) P ξ.val (D.level ξ)
      (CuspCrossSections.horospherical_endStabilizer (by decide : 1 ≤ 3) σ.range hΓ (D.region_nonempty ξ))
      (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ) pH
      (lipschitzWith_normalizedUniversalCoverProjection_original_metric g hg (-1 / 4) (by norm_num) x₀ hsec i) hinv
    exact ENNReal.tendsto_nhds_zero.mp hlim _ (by norm_num)
  exact hdiam

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem source_closedBall_eight_subset_cusp :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r),
      let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ
      ∀ (ξ : D.centers) (d : Set.Ici (0 : ℝ)), 6 ≤ d.val → ∀ c,
        riemannianClosedBallOf g (e ξ (c,d)) 8 ⊆ pH '' {z | Busemann.busemann ξ.val z < D.level ξ} := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i r D ξ d hd c
  have htail := riemannianClosedBallOf_normalizedUniversalCoverCuspCylinderMap_subset_tail
    g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ c d 1 2 (by norm_num) (by norm_num)
    (by norm_num [Real.sqrt_div] at hd ⊢; exact hd)
  norm_num only [show (4 : ℝ) * 2 = 8 by norm_num] at htail
  intro z hz
  obtain ⟨q, hq, rfl⟩ := htail hz
  rw [← normalizedUniversalCoverCuspCylinderMap_image_pos g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ]
  exact ⟨q, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq, rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_source_depth_and_scale (T : ℝ) (s : ℕ) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r),
      let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      ∃ d : Set.Ici (0 : ℝ), 0 < d.val ∧ T ≤ d.val ∧
        x₀ ∈ interior (Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val)) ∧
        (∀ ξ : D.centers, Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - d.val)) ≤
          ENNReal.ofReal (1 / 10)) ∧
        (∀ ξ : D.centers, ∀ c,
          riemannianClosedBallOf g (e ξ (c, d)) 8 ⊆ pH '' {z | Busemann.busemann ξ.val z < D.level ξ}) ∧
        ∃ N : ℕ, s ≤ N ∧ 99 ≤ N ∧
          Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val) ⊆
            riemannianClosedBallOf g x₀ (N + 1) ∧
          ∀ ξ : D.centers, ∀ c,
            riemannianClosedBallOf g (e ξ (c, d)) 9 ⊆ riemannianClosedBallOf g x₀ (N + 1) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i r D
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    have hρ : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    dsimp only [σ]
    rw [MonoidHom.range_comp]
    exact hρ.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let F := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hprops := source_cylindricalCore_properties (n := 3) (hn := by decide) (Γ := σ.range) (r := r) (Y := M) D hΓ F x₀
  change (∀ d : ℝ, 0 ≤ d → IsCompact (Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d))) ∧
    (∃ B : ℝ, ∀ d : ℝ, B < d → x₀ ∈ interior (Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d))) ∧
    (∀ d : Set.Ici (0 : ℝ), ∀ ξ : D.centers, ∀ c,
      e ξ (c,d) ∈ Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val)) at hprops
  obtain ⟨hcompact, ⟨B, hB⟩, hcenter⟩ := hprops
  have hdiam : ∀ᶠ t : ℝ in Filter.atTop, ∀ ξ : D.centers,
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - t)) ≤ ENNReal.ofReal (1 / 10) :=
    eventually_source_horosphere_diameter_le g hg x₀ hsec i D
  have hAex : ∃ A : ℝ, ∀ t : ℝ, A ≤ t → ∀ ξ : D.centers,
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - t)) ≤ ENNReal.ofReal (1 / 10) :=
    Filter.eventually_atTop.mp hdiam
  obtain ⟨A, hA⟩ := hAex
  let d : Set.Ici (0 : ℝ) := ⟨max (max T A) (max B 6) + 1, by
    change 0 ≤ max (max T A) (max B 6) + 1
    have h6 := (le_max_right B (6 : ℝ)).trans (le_max_right (max T A) (max B 6))
    linarith⟩
  have hdT : T ≤ d.val := (le_max_left T A).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))
  have hdA : A ≤ d.val := (le_max_right T A).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))
  have hdB : B < d.val := (le_max_left B 6).trans_lt ((le_max_right _ _).trans_lt (lt_add_one _))
  have hd6 : 6 ≤ d.val := (le_max_right B 6).trans ((le_max_right _ _).trans (le_add_of_nonneg_right (by norm_num)))
  refine ⟨d, by linarith, hdT, ?_, hA d.val hdA, ?_, ?_⟩
  · exact hB d.val hdB
  · exact fun ξ c => source_closedBall_eight_subset_cusp g hg x₀ hsec i D ξ d hd6 c
  · have hbounded : Bornology.IsBounded (Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val)) :=
      (hcompact d.val d.property).isBounded
    have hRex : ∃ R : ℝ, 0 < R ∧ Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val) ⊆ Metric.closedBall x₀ R :=
      hbounded.subset_closedBall_lt 0 x₀
    obtain ⟨R, hR, hRsub⟩ := hRex
    let n : ℕ := Nat.ceil (R + 9)
    have hn : R + 9 ≤ (n : ℝ) := Nat.le_ceil (R + 9)
    let N := max s (max 99 n)
    have hnN : n ≤ N := (le_max_right 99 n).trans (le_max_right _ _)
    have hN : R + 9 ≤ (N : ℝ) := hn.trans (by exact_mod_cast hnN)
    refine ⟨N, le_max_left _ _, (le_max_left 99 n).trans (le_max_right _ _), ?_, ?_⟩
    · intro z hz
      change edist x₀ z ≤ ENNReal.ofReal ((N : ℝ) + 1)
      rw [edist_dist, dist_comm]
      have hdist : dist z x₀ ≤ R := hRsub hz
      have hRN : R ≤ (N : ℝ) + 1 :=
        (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 9)).trans
          (hN.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      exact ENNReal.ofReal_le_ofReal (hdist.trans hRN)
    · intro ξ c z hz
      have hcenterR : e ξ (c, d) ∈ riemannianClosedBallOf g x₀ R := by
        change edist x₀ (e ξ (c,d)) ≤ ENNReal.ofReal R
        rw [edist_dist, dist_comm]
        exact ENNReal.ofReal_le_ofReal (hRsub (hcenter d ξ c))
      have hd := (riemannianEDistOf_triangle g x₀ (e ξ (c, d)) z).trans (add_le_add hcenterR hz)
      rw [← ENNReal.ofReal_add hR.le (by norm_num : (0 : ℝ) ≤ 9)] at hd
      exact hd.trans (ENNReal.ofReal_le_ofReal (hN.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))))

end DifferentialGeometry.Geometry.Hyperbolic
end

section
section

variable {X Y M N C T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace C] [TopologicalSpace T]

private theorem conjugate_partial_source (e : X ≃ₜ M) (f : Y ≃ₜ N)
    (Φ : OpenPartialHomeomorph M N) :
    ((e.toOpenPartialHomeomorph.trans Φ).transHomeomorph f.symm).source = e ⁻¹' Φ.source := by
  change Set.univ ∩ e ⁻¹' Φ.source = e ⁻¹' Φ.source
  exact Set.univ_inter _

private theorem graph_source_of_transHomeomorph
    (f : Y ≃ₜ N) (A : OpenPartialHomeomorph (T × ℝ) N)
    (Q : OpenPartialHomeomorph (T × ℝ) Y) (hA : A = Q.transHomeomorph f)
    (h : T → ℝ) (hgraph : ∀ t, (t, h t) ∈ A.source) : ∀ t, (t, h t) ∈ Q.source := by
  have hsource : A.source = Q.source := congrArg (fun a : OpenPartialHomeomorph (T × ℝ) N => a.source) hA
  exact fun t => hsource ▸ hgraph t

private theorem conjugate_graph_equation
    (e : X ≃ₜ M) (f : Y ≃ₜ N) (Φ : OpenPartialHomeomorph M N)
    (A : OpenPartialHomeomorph (T × ℝ) N) (Q : OpenPartialHomeomorph (T × ℝ) Y)
    (hA : A = Q.transHomeomorph f)
    (β : C → M) (βQ : C → X) (hβ : ∀ c, β c = e (βQ c))
    (η : T ≃ₜ C) (h : T → ℝ) (hgraph : ∀ t, Φ (β (η t)) = A (t, h t)) (c : C) :
    ((e.toOpenPartialHomeomorph.trans Φ).transHomeomorph f.symm) (βQ c) =
      Q (η.symm c, h (η.symm c)) := by
  have hβη : β (η (η.symm c)) = e (βQ c) :=
    (congrArg β (η.apply_symm_apply c)).trans (hβ c)
  have hchart : A (η.symm c, h (η.symm c)) = f (Q (η.symm c, h (η.symm c))) :=
    congrArg (fun a : OpenPartialHomeomorph (T × ℝ) N => a (η.symm c, h (η.symm c))) hA
  have heq : Φ (e (βQ c)) = f (Q (η.symm c, h (η.symm c))) :=
    (congrArg Φ hβη).symm.trans ((hgraph (η.symm c)).trans hchart)
  exact (congrArg f.symm heq).trans (f.symm_apply_apply _)


end
end

section
private theorem projection_image_eq_of_quotient_image_eq
    {X Q Y : Type*} (π : X → Q) (e : Q → Y) (p : X → Y)
    (hrep : ∀ x, e (π x) = p x) {U V : Set X} (h : π '' U = π '' V) :
    p '' U = p '' V := by
  have hp : p = e ∘ π := funext fun x => (hrep x).symm
  rw [hp, Set.image_comp, Set.image_comp, h]

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

private theorem exists_cusp_center_or_pair_of_nonempty_thinRegion
    {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation hn Γ r) (S : Set (BoundaryH n))
    (hS : (OrbifoldThinRegions.thinRegion hn Γ r S).Nonempty) :
    let π := Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
    (∃ ξ : D.centers, π '' interior (OrbifoldThinRegions.thinRegion hn Γ r S) =
      π '' interior (OrbifoldThinRegions.thinRegion hn Γ r {ξ.val})) ∨
      ∃ ξ η : BoundaryH n, ξ ≠ η ∧ S = {ξ, η} := by
  obtain ⟨z, hz⟩ := hS
  rcases hz.2 with ⟨ξ, hξ, _⟩ | ⟨ξ, η, hne, heq, _⟩
  · subst S
    obtain ⟨γ, hγ⟩ := D.covers_centers ξ ⟨z, hz⟩
    let η : D.centers := ⟨(poBoundaryMulAction hn).smul (γ : PO n 1) ξ, hγ⟩
    refine Or.inl ⟨η, ?_⟩
    exact OrbifoldThinRegions.quotient_interior_thinRegion_eq_of_image_eq hn Γ r γ
      (by simp only [Set.image_singleton]; rfl)
  · exact Or.inr ⟨ξ, η, hne, heq⟩

private theorem card_centers_le_of_endCount_le
    {Γ Λ : Subgroup (PO 3 1)} {r ε : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation (by decide) Γ r)
    (E : CuspTruncation.FiniteCuspTruncation (by decide) Λ r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hΛ : IsDiscrete (SetLike.coe Λ))
    [MeasureTheory.HasFundamentalDomain Γ (PO 3 1)]
    [MeasureTheory.HasFundamentalDomain Λ (PO 3 1)]
    (hcovΓ : MeasureTheory.covolume Γ (PO 3 1) ≠ ⊤)
    (hcovΛ : MeasureTheory.covolume Λ (PO 3 1) ≠ ⊤)
    (hr : 0 < r) (hre : r < ε)
    (hgeomΓ : ∀ z : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (Margulis.smallSubgroup (by decide) Γ ε z))
    (hgeomΛ : ∀ z : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (Margulis.smallSubgroup (by decide) Λ ε z))
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : @MulAction.orbitRel.Quotient Γ (HUpper 3) _ (EquivariantMap.subAction (by decide) Γ) ≃ₜ M)
    (f : @MulAction.orbitRel.Quotient Λ (HUpper 3) _ (EquivariantMap.subAction (by decide) Λ) ≃ₜ N)
    (hcount : Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N) :
    Nat.card D.centers ≤ Nat.card E.centers := by
  have hD : Geometry.Topology.endCount M = (D.centers.ncard : ℕ∞) :=
    (Geometry.Topology.endCount_homeomorph e).symm.trans
      (D.endCount_quotient_eq_ncard_centers hΓ (by decide) hcovΓ hr hre hgeomΓ)
  have hE : Geometry.Topology.endCount N = (E.centers.ncard : ℕ∞) :=
    (Geometry.Topology.endCount_homeomorph f).symm.trans
      (E.endCount_quotient_eq_ncard_centers hΛ (by decide) hcovΛ hr hre hgeomΛ)
  rw [hD, hE] at hcount
  simpa only [Nat.card_coe_set_eq] using ENat.natCast_le_natCast.mp hcount

end DifferentialGeometry.Geometry.Hyperbolic
end

section
namespace DifferentialGeometry.Geometry.Hyperbolic

private theorem exists_busemann_height_of_horosphereGraphChart
    {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (ProjectiveOrthogonalGroup.PO n 1)} {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation hn Γ r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)
    {Y : Type*} [TopologicalSpace Y]
    (F : (@MulAction.orbitRel.Quotient Γ (DifferentialGeometry.Hyperbolic.HUpper n) _
      (EquivariantMap.subAction hn Γ)) ≃ₜ Y)
    (pH : DifferentialGeometry.Hyperbolic.HUpper n → Y)
    (hproj : ∀ z, F (Quotient.mk
      (@MulAction.orbitRel Γ (DifferentialGeometry.Hyperbolic.HUpper n) _
        (EquivariantMap.subAction hn Γ)) z) = pH z) :
    ∃ B : Y → ℝ, ∀ z, Busemann.busemann ξ.val z < D.level ξ →
      B (pH z) = 2 * Busemann.busemann ξ.val z := by
  let P := CuspCrossSections.endStabilizer hn Γ {ξ.val}
  let πP := Quotient.mk (@MulAction.orbitRel P (DifferentialGeometry.Hyperbolic.HUpper n) _
    (EquivariantMap.subAction hn P))
  let πΓ := Quotient.mk (@MulAction.orbitRel Γ (DifferentialGeometry.Hyperbolic.HUpper n) _
    (EquivariantMap.subAction hn Γ))
  let E := D.horosphereHeightHomeomorph hΓ ξ
  let A := D.horosphereGraphChart hΓ ξ
  refine ⟨fun y => 2 * (A.symm (F.symm y)).2, ?_⟩
  intro z hz
  have hzthin : z ∈ interior (OrbifoldThinRegions.thinRegion hn Γ r {ξ.val}) :=
    D.horoball_inside ξ (show z ∈ Busemann.horoball ξ.val (D.level ξ) from hz.le)
  have hu : E (πP z) ∈ A.source := by
    rw [D.horosphereGraphChart_source]
    change E.symm (E (πP z)) ∈ πP '' interior (OrbifoldThinRegions.thinRegion hn Γ r {ξ.val})
    rw [E.symm_apply_apply]
    exact ⟨z, hzthin, rfl⟩
  have hA : A (E (πP z)) = πΓ z := by
    rw [D.horosphereGraphChart_apply, E.symm_apply_apply]
    rfl
  have hF : F.symm (pH z) = πΓ z := by
    rw [← hproj, F.symm_apply_apply]
  change 2 * (A.symm (F.symm (pH z))).2 = _
  rw [hF, ← hA, A.left_inv hu]
  rfl

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open Set

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (by decide) Δ

private theorem selected_pair_preserved (Λ : Subgroup (PO 3 1))
    (a b : BoundaryH 3) (γ : CuspCrossSections.endStabilizer (by decide) Λ {a, b}) :
    (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) a ∈ ({a, b} : Set (BoundaryH 3)) ∧
    (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) b ∈ ({a, b} : Set (BoundaryH 3)) := by
  have he := (ElementaryEnds.mem_setStabilizer (by decide) {a, b} γ).mp γ.property.2
  exact ⟨he.subset (mem_image_of_mem _ (by simp)),
    he.subset (mem_image_of_mem _ (by simp))⟩

variable {Γ Λ : Subgroup (PO 3 1)} [DiscreteTopology Γ] [DiscreteTopology Λ]
  {r s : ℝ} (D : FiniteCuspTruncation (by decide) Γ r)
  (E : FiniteCuspTruncation (by decide) Λ s)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "hΛ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Λ))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper 3)
local notation "QΛ" => MulAction.orbitRel.Quotient Λ (HUpper 3)
local notation "πΛ" => Quotient.mk (MulAction.orbitRel Λ (HUpper 3))
local notation "CΓ" => fun ξ : D.centers =>
  (Quotient.mk (MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide) Γ (Set.singleton (Subtype.val ξ))) (HUpper 3))) ''
    Busemann.horosphere (Subtype.val ξ) (D.level ξ)
local notation "CΛ" => fun η : E.centers =>
  (Quotient.mk (MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide) Λ (Set.singleton (Subtype.val η))) (HUpper 3))) ''
    Busemann.horosphere (Subtype.val η) (E.level η)
local notation "Pairs" => {p : BoundaryH 3 × BoundaryH 3 // Prod.fst p ≠ Prod.snd p}
local notation "AP" => fun p : Pairs => CuspCrossSections.endStabilizer (by decide) Λ (Set.insert (Prod.fst (Subtype.val p)) (Set.singleton (Prod.snd (Subtype.val p))))
local notation "AS" => fun p : Pairs =>
  {z : MulAction.orbitRel.Quotient (AP p) (HUpper 3) //
    AxisGeometry.quotientAxisDistance 2 (AP p) (Prod.fst (Subtype.val p)) (Prod.snd (Subtype.val p)) (Subtype.property p)
      (selected_pair_preserved Λ (Prod.fst (Subtype.val p)) (Prod.snd (Subtype.val p))) z = Real.arsinh 1}

variable [IsCancelSMul Λ (HUpper 3)]

private local instance (S : Set (BoundaryH 3)) :
    IsCancelSMul (CuspCrossSections.endStabilizer (Nat.succ_le_succ (Nat.zero_le 2)) Λ S) (HUpper 3) :=
  EquivariantMap.isCancelSMul_subAction (Nat.succ_le_succ (Nat.zero_le 2)) (show CuspCrossSections.endStabilizer (by decide) Λ S ≤ Λ from inf_le_left)

private abbrev SelectedSection (c : E.centers ⊕ Pairs) : Type :=
  Sum.elim (fun η => (CΛ η : Type)) (fun p => AS p) c

local notation "T" => SelectedSection E

private local instance selectedSectionTopologicalSpace (c : E.centers ⊕ Pairs) : TopologicalSpace (T c) := by
  cases c with
  | inl η => exact inferInstanceAs (TopologicalSpace (CΛ η))
  | inr p => exact inferInstanceAs (TopologicalSpace (AS p))

private def selectedChart (c : E.centers ⊕ Pairs) : OpenPartialHomeomorph ((T c) × ℝ) QΛ := by
  cases c with
  | inl η => exact E.horosphereGraphChart hΛ η
  | inr p => exact OrbifoldThinRegions.axialGraphChart 2 Λ p.val.1 p.val.2 p.property (by decide) s

local notation "A" => selectedChart E


end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open Integral.Measure (riemannianVolumeMeasure)
open ProjectiveOrthogonalGroup (PO)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3

private theorem quarter_curvature_neg : (-1 / 4 : ℝ) < 0 := by norm_num

universe u v

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolic_topological_stability_of_cusp_count_le
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvol : riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hsec : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) (s : ℕ) :
    ∃ n : ℕ, s ≤ n ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E₃ N] [IsManifold (𝓡 3) ∞ N]
        [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N), RiemannianMetricComplete h →
        letI : MeasurableSpace N := borel N
        letI : BorelSpace N := ⟨rfl⟩
        riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
          (∀ (x : N) (v w : TangentSpace (𝓡 3) x),
            Curvature.metricRm04StandardAt h x v w w v =
              (-1 / 4 : ℝ) * (h.inner x v v * h.inner x w w - h.inner x v w * h.inner x v w)) →
          Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N →
          ∀ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
            PartialDiffeomorph.isMetricApproximationOn Φ
              (riemannianClosedBallOf g o ((n : ℝ) + 1)) (n + 1) (1 / ((n : ℝ) + 1)) g h →
            Nonempty (M ≃ₜ N) := by
  classical
  obtain ⟨δ₀, hδ₀, hthickness⟩ := exists_pos_deck_displacement_of_metric_approximation g o
  obtain ⟨ε, hε, hgeometry⟩ := BoundaryStabilizer.exists_margulis_geometry_constant (by decide : 1 ≤ 3)
  let r : ℝ := min 1 (min (ε / 2) δ₀)
  have hr : 0 < r := lt_min (by norm_num) (lt_min (half_pos hε) hδ₀)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrε : r < ε := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  have hrδ : r ≤ δ₀ := (min_le_right _ _).trans (min_le_right _ _)
  let _ : Inhabited M := ⟨o⟩
  let _ : LocallyPathConnectedSpace E₃ := (𝓡 3).toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E₃ M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology E₃ := ModelWithCorners.secondCountableTopology (𝓡 3)
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E₃ M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) g
  let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold (𝓡 3) 1 (UniversalCover M) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace (𝓡 3) (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace (𝓡 3) : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M)))).reindex
      (finCongr (show Module.finrank ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) = 3 from
        finrank_euclideanSpace_fin))
  let i := b.repr.symm
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg o hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) quarter_curvature_neg o hsec i).choose
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let _ : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let _ : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      g hg (-1 / 4) quarter_curvature_neg o hsec i
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_curvature_neg o hsec i
  let eSource := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) quarter_curvature_neg o hsec i
  obtain ⟨hfd, hcov⟩ := hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover
    g hg (-1 / 4) quarter_curvature_neg o hsec hvol i
  let _ : MeasureTheory.HasFundamentalDomain σ.range (PO 3 1) := hfd
  let D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r :=
    Classical.choice (CuspTruncation.exists_finite_cusp_truncation
      (by decide) (by decide) σ.range hΓ hcov hr hrε (hgeometry σ.range hΓ))
  let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap
    g hg (-1 / 4) quarter_curvature_neg o hsec i D ξ
  have hfinite (ξ : D.centers) : riemannianVolumeMeasure (𝓡 3) M g (Set.range (e ξ)) ≠ ⊤ :=
    (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ _)) hvol).ne
  obtain ⟨T, hT, hthin⟩ := exists_depth_ball_subset_image_interior_thinRegion_of_metric_approximation
    g hg (-1 / 4) quarter_curvature_neg o hsec i D hfinite r hr hr1
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  obtain ⟨d, hd, hdT, hoCore, hdiam, hcollar, n, hsn, hn99, hcore, hballs⟩ :=
    exists_source_depth_and_scale g hg o hsec T s i D
  refine ⟨n, hsn, ?_⟩
  intro N topN chartN smoothN t2N sigmaN connN h hh
  let _ : MeasurableSpace N := borel N
  let _ : BorelSpace N := ⟨rfl⟩
  intro hvolN hsecN hends Φ hΦ
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδsmall : δ ≤ 1 / 100 := by
    have hnR : (99 : ℝ) ≤ n := by exact_mod_cast hn99
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) (by linarith)
  have hp : 1 ≤ n + 1 := Nat.succ_pos n
  have hbaseApprox : PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g o 1) (n + 1) δ g h :=
    hΦ.mono (riemannianClosedBallOf_mono g o (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])) le_rfl le_rfl
  let oTarget : N := Φ o
  let _ : Inhabited N := ⟨oTarget⟩
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace E₃ N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact E₃ N
  let gTargetN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) h
  let ĝTarget := UniversalCover.liftedMetric (I := 𝓡 3) gTargetN
  let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gTargetN (hh.scaleMetric _ _)
  let _ : IsManifold (𝓡 3) 1 (UniversalCover N) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover N) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover N) := Manifold.metrizableSpace (𝓡 3) (UniversalCover N)
  let _ : T3Space (UniversalCover N) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : UniversalCover N → Type _) := ⟨ĝTarget.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace (𝓡 3) : UniversalCover N → Type _) :=
    ⟨⟨ĝTarget.inner, ĝTarget.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover N)
  let _ : PseudoEMetricSpace (UniversalCover N) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover N)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover N) := hĝTarget.complete
  let bTarget : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N))) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N)))).reindex
      (finCongr (show Module.finrank ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := N))) = 3 from
        finrank_euclideanSpace_fin))
  let iTarget := bTarget.repr.symm
  let ρTarget := normalizedUniversalCoverDeckRepresentation h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget
  let σTarget := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρTarget
  let hΛ : IsDiscrete (SetLike.coe σTarget.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget).choose
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σTarget.range
  let _ : DiscreteTopology σTarget.range := isDiscrete_iff_discreteTopology.mp hΛ
  let _ : IsCancelSMul σTarget.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget
  let pHTarget := normalizedUniversalCoverProjection h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget
  let eTarget := normalizedUniversalCoverProjectiveQuotientHomeomorph h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget
  obtain ⟨hfdTarget, hcovTarget⟩ := hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover
    h hh (-1 / 4) quarter_curvature_neg oTarget hsecN hvolN iTarget
  let _ : MeasureTheory.HasFundamentalDomain σTarget.range (PO 3 1) := hfdTarget
  let E : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σTarget.range r :=
    Classical.choice (CuspTruncation.exists_finite_cusp_truncation
      (by decide) (by decide) σTarget.range hΛ hcovTarget hr hrε (hgeometry σTarget.range hΛ))
  have hclosedGeometry (z : H₃) : BoundaryStabilizer.ElementaryGeometry (by decide : 1 ≤ 3)
      (OrbifoldStrata.closedSmallSubgroup (by decide : 1 ≤ 3) σTarget.range r z) :=
    OrbifoldStrata.closedSmallSubgroup_geometry (by decide) σTarget.range hrε z (hgeometry σTarget.range hΛ z)
  have hcount : Nat.card D.centers ≤ Nat.card E.centers :=
    card_centers_le_of_endCount_le D E hΓ hΛ hcov hcovTarget hr hrε
      (hgeometry σ.range hΓ) (hgeometry σTarget.range hΛ) eSource eTarget hends
  have hthickNative : ∀ S : Set B₃,
      Φ o ∉ pHTarget '' OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r S := by
    apply not_mem_image_thinRegion_of_forall_deck_displacement_gt
      h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget (Φ o) δ₀ r hrδ
    have hlong := hthickness N h hh Φ hsecN (n + 1) δ (hδsmall.trans (by norm_num)) hbaseApprox
    simpa only [neg_div, neg_neg] using hlong
  let QSource := MulAction.orbitRel.Quotient σ.range H₃
  let QTarget := MulAction.orbitRel.Quotient σTarget.range H₃
  let χ : OpenPartialHomeomorph QSource QTarget :=
    (eSource.toOpenPartialHomeomorph.trans Φ.toOpenPartialHomeomorph).transHomeomorph eTarget.symm
  let K : Set QSource := Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) (fun _ => d.val)
  have hcoreEq : Topology.cylindricalCore (fun ξ => (e ξ : _ → M)) (fun _ => d.val) = eSource '' K :=
    cylindricalCore_homeomorph (fun ξ => D.horoballCylinderMap hΓ ξ) eSource (fun _ => d.val)
  have hKsource : K ⊆ χ.source := by
    rw [conjugate_partial_source]
    intro x hx
    exact hΦ.1 (hcore (hcoreEq.symm ▸ ⟨x, hx, rfl⟩))
  have hoK : eSource.symm o ∈ interior K := by
    rw [hcoreEq, ← eSource.image_interior, eSource.image_eq_preimage_symm] at hoCore
    exact hoCore
  have hthick : ∀ S : Set B₃, χ (eSource.symm o) ∉
      Quotient.mk (MulAction.orbitRel σTarget.range H₃) ''
        OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r S := by
    intro S hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    apply hthickNative S
    refine ⟨z, hz, ?_⟩
    have hrep := normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk
      h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget z
    change eTarget (Quotient.mk (MulAction.orbitRel σTarget.range H₃) z) = pHTarget z at hrep
    calc
      pHTarget z = eTarget (Quotient.mk (MulAction.orbitRel σTarget.range H₃) z) := hrep.symm
      _ = eTarget (χ (eSource.symm o)) := congrArg eTarget hzeq
      _ = Φ o := by change eTarget (eTarget.symm (Φ (eSource (eSource.symm o)))) = Φ o
                    rw [eTarget.apply_symm_apply, eSource.apply_symm_apply]
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}) H₃ _
      (EquivariantMap.subAction (by decide) (CuspCrossSections.endStabilizer (by decide) σ.range {ξ.val})))) ''
      Busemann.horosphere ξ.val (D.level ξ)
  let CTarget (η : E.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σTarget.range {η.val}) H₃ _
      (EquivariantMap.subAction (by decide) (CuspCrossSections.endStabilizer (by decide) σTarget.range {η.val})))) ''
      Busemann.horosphere η.val (E.level η)
  let Pairs := {p : B₃ × B₃ // p.1 ≠ p.2}
  let AP (p : Pairs) := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σTarget.range {p.val.1, p.val.2}
  have hpair (p : Pairs) (a : AP p) :
      (HyperbolicBoundary.poBoundaryMulAction (by decide : 1 ≤ 3)).smul (a : PO 3 1) p.val.1 ∈ ({p.val.1, p.val.2} : Set B₃) ∧
      (HyperbolicBoundary.poBoundaryMulAction (by decide : 1 ≤ 3)).smul (a : PO 3 1) p.val.2 ∈ ({p.val.1, p.val.2} : Set B₃) := by
    have he := (ElementaryEnds.mem_setStabilizer (by decide : 1 ≤ 3) {p.val.1, p.val.2} a).mp a.property.2
    exact ⟨he.subset ⟨p.val.1, by simp, rfl⟩, he.subset ⟨p.val.2, by simp, rfl⟩⟩
  let ASection (p : Pairs) : Type :=
    {q : @MulAction.orbitRel.Quotient (AP p) H₃ _ (EquivariantMap.subAction (by decide) (AP p)) //
      AxisGeometry.quotientAxisDistance 2 (AP p) p.val.1 p.val.2 p.property (hpair p) q = Real.arsinh 1}
  let TgtSection := CuspTruncation.FiniteCuspTruncation.SelectedSection E
  let _ : ∀ c, TopologicalSpace (TgtSection c) := CuspTruncation.FiniteCuspTruncation.selectedSectionTopologicalSpace E
  let targetChart := CuspTruncation.FiniteCuspTruncation.selectedChart E
  have hrepSource (z : H₃) : eSource (Quotient.mk (MulAction.orbitRel σ.range H₃) z) = pH z :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) quarter_curvature_neg o hsec i z
  have hrepTarget (z : H₃) : eTarget (Quotient.mk (MulAction.orbitRel σTarget.range H₃) z) = pHTarget z :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk h hh (-1 / 4) quarter_curvature_neg oTarget hsecN iTarget z
  have happrox (ξ : D.centers) (c : C ξ) : PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g (e ξ (c, d)) 9) (n + 1) δ g h :=
    hΦ.mono (hballs ξ c) le_rfl le_rfl
  have hcollarTwo (ξ : D.centers) (c : C ξ) :
      riemannianClosedBallOf g (e ξ (c, d)) 2 ⊆ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ} :=
    (riemannianClosedBallOf_mono g (e ξ (c,d)) (by norm_num : (2 : ℝ) ≤ 8)).trans (hcollar ξ c)
  have hβ (ξ : D.centers) (c : C ξ) : e ξ (c, d) = eSource (D.horoballCylinderMap hΓ ξ (c,d)) := by
    rfl
  have hgraphs (ξ : D.centers) : ∃ (label : E.centers ⊕ Pairs)
      (f : C(TgtSection label, ℝ)) (θ : C ξ ≃ₜ TgtSection label),
      (∀ q, (q, f.toFun q) ∈ (targetChart label).source) ∧
      ∀ c, χ (D.horoballCylinderMap hΓ ξ (c, d)) = targetChart label (θ.toFun c, f.toFun (θ.toFun c)) := by
    let PSource := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range {ξ.val}
    let _ : MulAction PSource H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) PSource
    let _ : IsCancelSMul PSource H₃ :=
      EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show PSource ≤ σ.range from inf_le_left)
    let : ChartedSpace (Fin 2 → ℝ) (C ξ) := D.horosphereQuotientChartedSpace hΓ ξ
    have hlabel := hthin N h hh oTarget hsecN iTarget ε hrε (hgeometry σTarget.range hΛ)
      Φ (n + 1) δ (hδsmall.trans (by norm_num)) ξ d hdT (happrox ξ)
    let S : Set B₃ := hlabel.choose
    have hball : ∀ c : C ξ, riemannianBallOf h (Φ (e ξ (c,d))) 2 ⊆
        pHTarget '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r S) := hlabel.choose_spec
    have hS : (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r S).Nonempty := by
      obtain ⟨c, hc⟩ := (D.isConnected_quotient_horosphere ξ).nonempty
      let c₀ : C ξ := ⟨c, hc⟩
      have hcenter : Φ (e ξ (c₀,d)) ∈ riemannianBallOf h (Φ (e ξ (c₀,d))) 2 := by
        change riemannianEDistOf h _ _ < ENNReal.ofReal 2
        rw [riemannianEDistOf_self]
        norm_num
      obtain ⟨y, hy, _⟩ := hball c₀ hcenter
      exact ⟨y, interior_subset hy⟩
    have hBex := exists_busemann_height_of_horosphereGraphChart D hΓ ξ eSource pH hrepSource
    let B : M → ℝ := hBex.choose
    have hB : ∀ z, Busemann.busemann ξ.val z < D.level ξ → B (pH z) = 2 * Busemann.busemann ξ.val z := hBex.choose_spec
    rcases exists_cusp_center_or_pair_of_nonempty_thinRegion E S hS with ⟨ηTarget, hrel⟩ | ⟨a, b, hab, hrel⟩
    · have himage : pHTarget '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r S) =
          pHTarget '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r {ηTarget.val}) :=
        projection_image_eq_of_quotient_image_eq _ eTarget pHTarget hrepTarget hrel
      have hballCusp (c : C ξ) : riemannianBallOf h (Φ (e ξ (c,d))) 2 ⊆
          pHTarget '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r {ηTarget.val}) :=
        (hball c).trans himage.le
      let PTarget := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σTarget.range {ηTarget.val}
      let _ : MulAction PTarget H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
      let _ : IsCancelSMul PTarget H₃ :=
        EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
      let : ChartedSpace (Fin 2 → ℝ) (CTarget ηTarget) := E.horosphereQuotientChartedSpace hΛ ηTarget
      obtain ⟨A, hA, η, f, hf, _, hsource, hgraph, _⟩ :=
        exists_cusp_image_graph_of_metric_approximation g hg o hsec h hh oTarget hsecN Φ hp
          (by norm_num : (2 : ℝ) < 9) hδsmall i D ξ d.val hd B hB (happrox ξ) (hcollarTwo ξ) (hdiam ξ)
            iTarget E ηTarget hballCusp
      let f' : TgtSection (Sum.inl ηTarget) → ℝ := f
      refine ⟨Sum.inl ηTarget, ⟨f', hf.continuous⟩, η.toHomeomorph.symm, ?_, ?_⟩
      · exact graph_source_of_transHomeomorph eTarget A.toOpenPartialHomeomorph
          (E.horosphereGraphChart hΛ ηTarget) hA f' hsource
      · exact conjugate_graph_equation eSource eTarget Φ.toOpenPartialHomeomorph
          A.toOpenPartialHomeomorph (E.horosphereGraphChart hΛ ηTarget) hA
          (fun c => e ξ (c,d)) (fun c => D.horoballCylinderMap hΓ ξ (c,d)) (hβ ξ)
          η.toHomeomorph f' hgraph
    · have hballAxis (c : C ξ) : riemannianBallOf h (Φ (e ξ (c,d))) 2 ⊆
          pHTarget '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r {a,b}) :=
        (hball c).trans ((congrArg (fun L : Set B₃ => pHTarget '' interior
          (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r L)) hrel).le)
      have havoid (c : C ξ) : Φ (e ξ (c,d)) ∉ pHTarget ''
          (AxisGeometry.axis a b ∩ OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σTarget.range r {a,b}) := by
        apply not_mem_axial_core_of_metric_approximation_in_cusp g hg o hsec h hh oTarget hsecN
          Φ (e ξ (c,d)) hp hδsmall (happrox ξ c) i iTarget D ξ a b hab r
        · linarith
        · exact (riemannianClosedBallOf_mono g (e ξ (c,d)) (by linarith : 8 * r ≤ 8)).trans (hcollar ξ c)
      let PTarget := AP ⟨(a,b), hab⟩
      let _ : MulAction PTarget H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
      let _ : DiscreteTopology PTarget := isDiscrete_iff_discreteTopology.mp (hΛ.mono (show PTarget ≤ σTarget.range from inf_le_left))
      let _ : IsCancelSMul PTarget H₃ :=
        EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
      let : ChartedSpace (Fin 2 → ℝ) (ASection ⟨(a,b), hab⟩) := AxisGeometry.axisSectionChartedSpace 2 (AP ⟨(a,b), hab⟩) a b hab (hpair ⟨(a,b), hab⟩)
      obtain ⟨A, hA, η, f, hf, _, hsource, hgraph, _⟩ :=
        exists_axial_image_graph_of_metric_approximation g hg o hsec h hh oTarget hsecN Φ hp
          (by norm_num : (2 : ℝ) < 9) hδsmall i D ξ d.val hd B hB (happrox ξ) (hcollarTwo ξ) (hdiam ξ)
            iTarget a b hab r hballAxis havoid
      let f' : TgtSection (Sum.inr ⟨(a,b), hab⟩) → ℝ := f
      refine ⟨Sum.inr ⟨(a,b), hab⟩, ⟨f', hf.continuous⟩, η.toHomeomorph.symm, ?_, ?_⟩
      · exact graph_source_of_transHomeomorph eTarget A.toOpenPartialHomeomorph
          (OrbifoldThinRegions.axialGraphChart 2 σTarget.range a b hab (by decide) r) hA f' hsource
      · exact conjugate_graph_equation eSource eTarget Φ.toOpenPartialHomeomorph
          A.toOpenPartialHomeomorph (OrbifoldThinRegions.axialGraphChart 2 σTarget.range a b hab (by decide) r) hA
          (fun c => e ξ (c,d)) (fun c => D.horoballCylinderMap hΓ ξ (c,d)) (hβ ξ)
          η.toHomeomorph f' hgraph
  choose choice f θ hgraph hmatch using hgraphs
  obtain ⟨F, _, _, _, _⟩ := D.exists_homeomorph_of_boundary_graphs_of_card_le E hr hclosedGeometry
    χ (fun _ => d.val) (fun _ => hd) hKsource (eSource.symm o) hoK hthick choice f θ hgraph hmatch hcount
  exact ⟨(eSource.symm.trans F).trans eTarget⟩

end DifferentialGeometry.Geometry.Hyperbolic
end
