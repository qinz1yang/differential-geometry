import DifferentialGeometry.Geometry.Hyperbolic.Cusps.SmoothInclusion
import DifferentialGeometry.Geometry.Hyperbolic.ApproximationPullback
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannGeodesic
import DifferentialGeometry.Geometry.Metric.Approximation.Inverse
import DifferentialGeometry.Geometry.Geodesic.Naturality.InverseCurve
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Quotient

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

section Obstruction

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E₃ Q] [IsManifold I₃ ∞ Q]

omit [IsManifold I₃ ∞ Q] in
private theorem not_periodic_of_inverse_cover
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (χ : PartialDiffeomorph I₃ I Q M ∞)
    (q : C(Hyperboloid E₃, M)) (hq : IsLocalDiffeomorph I₃ I ∞ q)
    (cover : C(Hyperboloid E₃, Q)) (hcover : IsCoveringMap cover)
    (hcover_surj : Function.Surjective cover) (hcover_smooth : IsLocalDiffeomorph I₃ I₃ ∞ cover)
    (hχ : ∀ x, χ (cover x) = q x)
    (ξ : Metric.sphere (0 : E₃) 1) (B : Q → ℝ)
    (hB : ∀ x : Hyperboloid E₃,
      2 * Real.log (x.time - inner ℝ (ξ : E₃) x.space) = B (cover x))
    (K : Set M) (p : ℕ) (hp : 1 ≤ p)
    (hsmall :
      let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
      let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
      let qU : U → S := fun x => ⟨q x, x.property⟩
      ∀ hqU : IsLocalDiffeomorph I₃ I ∞ qU,
      let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
      let g0 := (scaleMetric 4 (by norm_num) Hyperboloid.riemannianMetric).restrictOpen U
      CheegerGromovCompactness.metricCkENormOn ((fun x : U => q x) ⁻¹' K) p h g0 g0 ≤
        ENNReal.ofReal (1 / 100))
    (γ : C(ℝ, N)) {T : ℝ} (hT : 0 < T)
    (htarget : ∀ t, γ t ∈ Φ.target) (hcusp : ∀ t, Φ.symm (γ t) ∈ χ.target)
    (hK : ∀ t, Φ.symm (γ t) ∈ K)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) T))
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) :
    ¬ Function.Periodic γ T := by
  intro hperiod
  let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
  let qU : U → S := fun x => ⟨q x, x.property⟩
  have hqU : IsLocalDiffeomorph I₃ I ∞ qU := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property)
      ((isLocalDiffeomorph_comp hq (isLocalDiffeomorph_subtype_val U)) x)
  let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
  obtain ⟨z₀, hz₀⟩ := hcover_surj (χ.symm (Φ.symm (γ 0)))
  obtain ⟨ℓ, _, hcoverℓ, hqℓ, hℓsm, hgeolift, hunitlift⟩ :=
    Riemannian.Geodesic.exists_inverse_curve_lift gTarget Φ χ q hq cover hcover
      hcover_smooth hχ γ htarget hcusp z₀ hz₀ (Set.Icc (0 : ℝ) T) hγ hgeo hunit
  have hheight (t : ℝ) :
      2 * Real.log ((ℓ t).val.time - inner ℝ (ξ : E₃) (ℓ t).val.space) =
        B (χ.symm (Φ.symm (γ t))) := by
    exact (hB (ℓ t)).trans (congrArg B (hcoverℓ t))
  have hperiodheight : Function.Periodic
      (fun t => 2 * Real.log ((ℓ t).val.time - inner ℝ (ξ : E₃) (ℓ t).val.space)) T := by
    intro t
    dsimp only
    rw [hheight, hheight, hperiod t]
  apply Hyperboloid.not_periodic_two_mul_log_time_sub_inner_of_isGeodesicOn
    U h ξ hp (hsmall hqU) ℓ hT (fun t ht => (hℓsm t ht).of_le (by simp))
      hgeolift (fun t _ => ?_) hunitlift hperiodheight
  change q (ℓ t) ∈ K
  rw [hqℓ]
  exact hK t

end Obstruction

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_periodic_of_captured_geodesic_in_cusp
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞) (o : M)
    {R A ε T : ℝ} {p : ℕ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hmargin : 2 * A < R)
    (hε : ε ≤ 1 / 100)
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g o R) p ε g gTarget)
    (γ : C(ℝ, N)) (hT : 0 < T)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) T))
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (hcaptured : Set.MapsTo γ (Set.Icc (0 : ℝ) T) (riemannianClosedBallOf gTarget (Φ o) A)) :
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      riemannianClosedBallOf g o (2 * A) ⊆
        (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i) ''
          {z : H₃ | Busemann.busemann ξ.val z < D.level ξ} →
      ¬ Function.Periodic γ T := by
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
  intro i r D ξ hcollar hperiod
  have hall (t : ℝ) : γ t ∈ riemannianClosedBallOf gTarget (Φ o) A := by
    obtain ⟨s, hs, heq⟩ := hperiod.exists_mem_Ico₀ hT t
    rw [heq]
    exact hcaptured ⟨hs.1, hs.2.le⟩
  have hcpt : IsCompact (riemannianClosedBallOf g o R) := hg.closedEBall_isCompact o R
  have hcapture (t : ℝ) := PartialDiffeomorph.inverse_mem_closedBall_of_metric_approximation
    g gTarget Φ o hA hmargin (hε.trans (by norm_num : (1 / 100 : ℝ) ≤ 3 / 4)) hcpt hΦ (γ t) (hall t)
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      g hg (-1 / 4) (by norm_num) x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul P H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : ProjectiveOrthogonalGroup.PO 3 1)).continuous⟩
  obtain ⟨hΓ, hχexists⟩ := exists_normalizedUniversalCoverCuspPartialDiffeomorph
    g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ
  let := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 2) P (hΓ.mono inf_le_left)
  let : ContMDiffConstSMul I₃ ∞ P H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : ProjectiveOrthogonalGroup.PO 3 1)⟩
  obtain ⟨χ, _, hχtarget, _, hχrep, _, _⟩ := hχexists
  let QP := MulAction.orbitRel.Quotient P H₃
  let coverPlus : C(H₃, QP) := ⟨Quotient.mk (MulAction.orbitRel P H₃), continuous_quot_mk⟩
  let J := Hyperboloid.hUpperDiffeomorph 3
  let cover := coverPlus.comp (J.symm.toHomeomorph : C(Hyperboloid E₃, H₃))
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let q := pH.comp (J.symm.toHomeomorph : C(Hyperboloid E₃, H₃))
  have hq : IsLocalDiffeomorph I₃ I ∞ q := by
    change IsLocalDiffeomorph I₃ I ∞ ((pH : H₃ → M) ∘ (J.symm : Hyperboloid E₃ → H₃))
    exact isLocalDiffeomorph_comp
      (normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i)
      J.symm.isLocalDiffeomorph
  have hcoverPlus : IsCoveringMap coverPlus :=
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := P)).isCoveringMap
  have hcover : IsCoveringMap cover := hcoverPlus.comp_homeomorph J.symm.toHomeomorph
  have hcover_surj : Function.Surjective cover := Quotient.mk_surjective.comp J.symm.surjective
  have hcover_smooth : IsLocalDiffeomorph I₃ I₃ ∞ cover := by
    change IsLocalDiffeomorph I₃ I₃ ∞ ((coverPlus : H₃ → QP) ∘ (J.symm : Hyperboloid E₃ → H₃))
    exact isLocalDiffeomorph_comp
      (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (G := P) (n := ∞) I₃)
      J.symm.isLocalDiffeomorph
  have hχq (x : Hyperboloid E₃) : χ (cover x) = q x := hχrep (J.symm x)
  have hhor := CuspCrossSections.horospherical_endStabilizer
    (Nat.le_add_left 1 2) σ.range hΓ (D.region_nonempty ξ)
  let B : QP → ℝ := fun u => 2 * HorosphereProjection.quotientBusemann
    (Nat.le_add_left 1 2) P ξ.val hhor u
  have hB (x : Hyperboloid E₃) :
      2 * Real.log (x.time - inner ℝ (BoundaryTopology.toSphere ξ.val : E₃) x.space) = B (cover x) := by
    have ht := Busemann.busemann_eq_log_native ξ.val (J.symm x)
    have hJ : Hyperboloid.hUpperIsometryEquiv 3 (J.symm x) = x := J.apply_symm_apply x
    rw [hJ, real_inner_comm] at ht
    change 2 * Real.log (x.time - inner ℝ (BoundaryTopology.spatial ξ.val) x.space) =
      2 * HorosphereProjection.quotientBusemann (Nat.le_add_left 1 2) P ξ.val hhor
        (Quotient.mk (MulAction.orbitRel P H₃) (J.symm x))
    rw [HorosphereProjection.quotientBusemann_mk]
    exact congrArg (fun t : ℝ => 2 * t) ht.symm
  apply not_periodic_of_inverse_cover gTarget Φ χ q hq cover hcover hcover_surj hcover_smooth
    hχq (BoundaryTopology.toSphere ξ.val) B hB (riemannianClosedBallOf g o R) p hp ?_
      γ hT (fun t => (hcapture t).1) ?_ (fun t => (hcapture t).2.1) hγ hgeo hunit hperiod
  · dsimp only
    intro hqU
    exact (metricCkENormOn_normalized_universal_cover_pullback_lt
      g hg x₀ hsec gTarget Φ hΦ i).le.trans (ENNReal.ofReal_le_ofReal hε)
  · intro t
    rw [hχtarget]
    exact hcollar (hcapture t).2.2

end DifferentialGeometry.Geometry.Hyperbolic
