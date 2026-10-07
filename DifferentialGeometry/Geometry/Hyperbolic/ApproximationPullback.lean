import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

section Pullback

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [IsManifold I ∞ M] [T2Space M] in
private theorem preimage_source_localDiffeomorph (q : C(Hyperboloid E₃, M))
    (hq : IsLocalDiffeomorph I₃ I ∞ q) (S : TopologicalSpace.Opens M) :
    let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
    IsLocalDiffeomorph I₃ I ∞ (fun x : U => (⟨q x, x.property⟩ : S)) := by
  dsimp only
  intro x
  exact isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property)
    ((isLocalDiffeomorph_comp hq (isLocalDiffeomorph_subtype_val _)) x)

private theorem pullback_error_eq (g : SmoothRiemannianMetric I M)
    (gN : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (q : C(Hyperboloid E₃, M)) (hq : IsLocalDiffeomorph I₃ I ∞ q)
    (hsurj : Function.Surjective q)
    (hmetric : ∀ (x : Hyperboloid E₃) (v w : TangentSpace I₃ x),
      g.inner (q x) (mfderiv I₃ I q x v) (mfderiv I₃ I q x w) =
        4 * Hyperboloid.riemannianMetric.inner x v w)
    (K : Set M) (p : ℕ) :
    let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
    let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
    let qU : U → S := fun x => ⟨q x, x.property⟩
    let hqU := preimage_source_localDiffeomorph q hq S
    let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gN) qU hqU
    let g0 := (scaleMetric 4 (by norm_num) Hyperboloid.riemannianMetric).restrictOpen U
    CheegerGromovCompactness.metricCkENormOn ((fun x : U => q x) ⁻¹' K) p h g0 g0 =
      PartialDiffeomorph.metricCkErrorOn Φ K p g gN := by
  let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
  let qU : U → S := fun x => ⟨q x, x.property⟩
  let hqU := preimage_source_localDiffeomorph q hq S
  have hqUv (x : U) (v : TangentSpace I₃ x) : mfderiv I₃ I qU x v =
      mfderiv I₃ I q (x : Hyperboloid E₃) v := by
    have hchain := mfderiv_comp_apply x
      ((isLocalDiffeomorph_subtype_val S).contMDiff.mdifferentiableAt (by simp))
      (hqU.contMDiff.mdifferentiableAt (by simp)) v
    rw [mfderiv_subtype_val_apply] at hchain
    have hchain' := mfderiv_comp_apply x
      (hq.contMDiff.mdifferentiableAt (by simp))
      ((isLocalDiffeomorph_subtype_val U).contMDiff.mdifferentiableAt (by simp)) v
    rw [mfderiv_subtype_val_apply] at hchain'
    exact hchain.symm.trans hchain'
  have hbase : localPullMetric (g.restrictOpen S) qU hqU =
      (scaleMetric 4 (by norm_num) Hyperboloid.riemannianMetric).restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hqUv, hqUv]
    exact hmetric x v w
  have himage : qU '' ((fun x : U => q x) ⁻¹' K) = (Subtype.val : S → M) ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, hy⟩ := hsurj x.val
      have hyS : q y ∈ S := hy ▸ x.property
      refine ⟨⟨y, hyS⟩, ?_, Subtype.ext hy⟩
      change q y ∈ K
      rwa [hy]
  dsimp only
  change CheegerGromovCompactness.metricCkENormOn _ p _ _ _ = _
  rw [← hbase, CheegerGromovCompactness.metricCkENormOn_localPullMetric, himage]
  rfl

end Pullback

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_projection_surjective
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let J := Hyperboloid.hUpperDiffeomorph 3
      let q := (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i).comp
        (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
      Function.Surjective q := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i
  let J := Hyperboloid.hUpperDiffeomorph 3
  let P := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let q := P.comp (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let e := normalizedUniversalCoverIsometryEquiv g hg (-1 / 4) (by norm_num) x₀ hsec i
  have heq (x : Hyperboloid E₃) : q x = UniversalCover.proj (e x) := by
    calc
      q x = P (J.symm x) := rfl
      _ = UniversalCover.proj (e (J (J.symm x))) :=
        normalizedUniversalCoverProjection_apply g hg (-1 / 4) (by norm_num) x₀ hsec i (J.symm x)
      _ = UniversalCover.proj (e x) := congrArg (fun z => UniversalCover.proj (e z)) (J.apply_symm_apply x)
  intro y
  let z : UniversalCover M := ⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩
  refine ⟨e.symm z, ?_⟩
  rw [heq, e.apply_symm_apply]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_projection_inner
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let J := Hyperboloid.hUpperDiffeomorph 3
      let q := (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i).comp
        (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
      ∀ (x : Hyperboloid E₃) (v w : TangentSpace I₃ x),
        g.inner (q x) (mfderiv I₃ I q x v) (mfderiv I₃ I q x w) =
          4 * Hyperboloid.riemannianMetric.inner x v w := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i
  let J := Hyperboloid.hUpperDiffeomorph 3
  let P := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let q := P.comp (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
  intro x v w
  have hJ (u : TangentSpace I₃ x) :
      mfderiv I₃ I₃ J (J.symm x) (mfderiv I₃ I₃ J.symm x u) = u := by
    have ht := mfderiv_comp_apply x
      (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)) u
    have heq : (fun z => J (J.symm z)) = id := funext J.apply_symm_apply
    change mfderiv I₃ I₃ (fun z => J (J.symm z)) x u = _ at ht
    rw [heq, mfderiv_id] at ht
    exact ht.symm
  have ht := normalizedUniversalCoverProjection_inner g hg (-1 / 4) (by norm_num) x₀ hsec i
    (J.symm x) (mfderiv I₃ I₃ J.symm x v) (mfderiv I₃ I₃ J.symm x w)
  rw [hJ, hJ, J.apply_symm_apply] at ht
  have hd (u : TangentSpace I₃ x) : mfderiv I₃ I q x u =
      mfderiv I₃ I P (J.symm x) (mfderiv I₃ I₃ J.symm x u) :=
    mfderiv_comp_apply x
      ((normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4)
        (by norm_num) x₀ hsec i).contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)) u
  rw [hd, hd]
  change g.inner (P (J.symm x))
    (mfderiv I₃ I P (J.symm x) (mfderiv I₃ I₃ J.symm x v))
    (mfderiv I₃ I P (J.symm x) (mfderiv I₃ I₃ J.symm x w)) = _
  norm_num only [neg_div, neg_neg, one_div, inv_inv] at ht
  exact ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricCkENormOn_normalized_universal_cover_pullback
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (K : Set M) (p : ℕ) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let J := Hyperboloid.hUpperDiffeomorph 3
      let q := (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i).comp
        (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
      let hq := isLocalDiffeomorph_comp
        (normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i)
        J.symm.isLocalDiffeomorph
      let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
      let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
      let qU : U → S := fun x => ⟨q x, x.property⟩
      let hqU := preimage_source_localDiffeomorph q hq S
      let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
      let g0 := (scaleMetric 4 (by norm_num) Hyperboloid.riemannianMetric).restrictOpen U
      CheegerGromovCompactness.metricCkENormOn ((fun x : U => q x) ⁻¹' K) p h g0 g0 =
        PartialDiffeomorph.metricCkErrorOn Φ K p g gTarget := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i
  let J := Hyperboloid.hUpperDiffeomorph 3
  let P := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let q := P.comp (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
  have hq : IsLocalDiffeomorph I₃ I ∞ q := by
    change IsLocalDiffeomorph I₃ I ∞ ((P : _ → M) ∘ (J.symm : _ → _))
    exact isLocalDiffeomorph_comp
      (normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i)
      J.symm.isLocalDiffeomorph
  have hsurj : Function.Surjective q := native_projection_surjective g hg x₀ hsec i
  have hmetric := native_projection_inner g hg x₀ hsec i
  exact pullback_error_eq g gTarget Φ q hq hsurj hmetric K p

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricCkENormOn_normalized_universal_cover_pullback_lt
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    {K : Set M} {p : ℕ} {ε : ℝ}
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ K p ε g gTarget) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let J := Hyperboloid.hUpperDiffeomorph 3
      let q := (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i).comp
        (J.symm.toHomeomorph : C(Hyperboloid E₃, DifferentialGeometry.Hyperbolic.HUpper 3))
      let hq := isLocalDiffeomorph_comp
        (normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i)
        J.symm.isLocalDiffeomorph
      let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
      let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
      let qU : U → S := fun x => ⟨q x, x.property⟩
      let hqU := preimage_source_localDiffeomorph q hq S
      let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
      let g0 := (scaleMetric 4 (by norm_num) Hyperboloid.riemannianMetric).restrictOpen U
      CheegerGromovCompactness.metricCkENormOn ((fun x : U => q x) ⁻¹' K) p h g0 g0 < ENNReal.ofReal ε := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i
  exact (metricCkENormOn_normalized_universal_cover_pullback
    g hg x₀ hsec gTarget Φ K p i).trans_lt hΦ.2

end DifferentialGeometry.Geometry.Hyperbolic
