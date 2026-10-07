import DifferentialGeometry.Geometry.Hyperbolic.Cusps.SmoothInclusion
import DifferentialGeometry.Geometry.Hyperbolic.ApproximationPullback
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannGeodesic
import DifferentialGeometry.Geometry.Metric.Approximation.Inverse
import DifferentialGeometry.Geometry.Geodesic.Naturality.InverseCurve
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Order.ProjIcc

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

private theorem exists_continuous_extension_Icc {Y : Type*} [TopologicalSpace Y]
    (γ : C(ℝ, Y)) {V : Set Y} (hV : IsOpen V)
    (hγ : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) V) :
    ∃ γ' : C(ℝ, Y), (∀ t, γ' t ∈ V) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ' : ℝ → Y) =ᶠ[𝓝 t] γ := by
  obtain ⟨a, b, hab, hsub₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hV.preimage γ.continuous).mem_nhds (hγ (by simp : (0 : ℝ) ∈ Set.Icc 0 1)))
  obtain ⟨c, d, hcd, hsub₁⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hV.preimage γ.continuous).mem_nhds (hγ (by simp : (1 : ℝ) ∈ Set.Icc 0 1)))
  let l := a / 2
  let u := (1 + d) / 2
  have hl : l < 0 := by dsimp only [l]; linarith [hab.1]
  have hu : 1 < u := by dsimp only [u]; linarith [hcd.2]
  have hlu : l ≤ u := by linarith
  have hmaps : Set.MapsTo γ (Set.Icc l u) V := by
    intro t ht
    by_cases ht₀ : t < 0
    · apply hsub₀
      constructor
      · have hat : a / 2 ≤ t := ht.1
        linarith [hab.1]
      · linarith [hab.2]
    · by_cases ht₁ : 1 < t
      · apply hsub₁
        constructor
        · linarith [hcd.1]
        · have htd : t ≤ (1 + d) / 2 := ht.2
          linarith [hcd.2]
      · exact hγ ⟨le_of_not_gt ht₀, le_of_not_gt ht₁⟩
  let τ : C(ℝ, ℝ) := ⟨fun t => (Set.projIcc l u hlu t : ℝ),
    continuous_subtype_val.comp continuous_projIcc⟩
  refine ⟨γ.comp τ, fun t => hmaps (Set.projIcc l u hlu t).property, ?_⟩
  intro t ht
  filter_upwards [Ioo_mem_nhds (show l < t by linarith [ht.1])
    (show t < u by linarith [ht.2])] with s hs
  change γ (Set.projIcc l u hlu s) = γ s
  rw [Set.projIcc_of_mem hlu ⟨hs.1.le, hs.2.le⟩]

section Obstruction

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E₃ Q] [IsManifold I₃ ∞ Q]

omit [IsManifold I₃ ∞ Q] in
private theorem height_bound_of_inverse_cover
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (χ : PartialDiffeomorph I₃ I Q M ∞)
    (q : C(Hyperboloid E₃, M)) (hq : IsLocalDiffeomorph I₃ I ∞ q)
    (cover : C(Hyperboloid E₃, Q)) (hcover : IsCoveringMap cover)
    (hcover_surj : Function.Surjective cover) (hcover_smooth : IsLocalDiffeomorph I₃ I₃ ∞ cover)
    (hχ : ∀ x, χ (cover x) = q x)
    (ξ : Metric.sphere (0 : E₃) 1) (B : Q → ℝ)
    (hB : ∀ x : Hyperboloid E₃,
      2 * Real.log (x.time - inner ℝ (ξ : E₃) x.space) = B (cover x))
    (height : M → ℝ) (hheight : ∀ y ∈ χ.target, B (χ.symm y) = height y)
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
    (γ : C(ℝ, N))
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Φ.target)
    (hcusp : ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ.symm (γ t) ∈ χ.target)
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ.symm (γ t) ∈ K)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) 1))
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (hzero : deriv (fun t => height (Φ.symm (γ t))) 0 = 0) :
    |height (Φ.symm (γ 1)) - height (Φ.symm (γ 0))| ≤ 1 / 3 := by
  let V : Set N := Φ.target ∩ (Φ.symm : N → M) ⁻¹' χ.target
  have hV : IsOpen V :=
    Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Φ.open_target χ.open_target
  have hγV : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) V :=
    fun t ht => ⟨htarget t ht, hcusp t ht⟩
  obtain ⟨γ', hγ'V, hgerm⟩ := exists_continuous_extension_Icc γ hV hγV
  have hγ'sm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ' t :=
    (hγ t ht).congr_of_eventuallyEq (hgerm t ht)
  have hγ'geo : Riemannian.Geodesic.IsGeodesicOn gTarget γ' (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact Riemannian.Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hgerm t ht).eq_of_nhds (hgerm t ht) (hgeo t ht)
  have hγ'unit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      gTarget.inner (γ' t) (mfderiv 𝓘(ℝ, ℝ) I γ' t 1) (mfderiv 𝓘(ℝ, ℝ) I γ' t 1) = 1 := by
    have heq := hgerm t ht
    rw [heq.mfderiv_eq]
    exact (congrArg (fun y : N => gTarget.inner y
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E₃) (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E₃)) heq.eq_of_nhds).trans
        (hunit t ht)
  let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let U : TopologicalSpace.Opens (Hyperboloid E₃) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
  let qU : U → S := fun x => ⟨q x, x.property⟩
  have hqU : IsLocalDiffeomorph I₃ I ∞ qU := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property)
      ((isLocalDiffeomorph_comp hq (isLocalDiffeomorph_subtype_val U)) x)
  let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
  obtain ⟨z₀, hz₀⟩ := hcover_surj (χ.symm (Φ.symm (γ' 0)))
  obtain ⟨ℓ, _, hcoverℓ, hqℓ, hℓsm, hgeolift, hunitlift⟩ :=
    Riemannian.Geodesic.exists_inverse_curve_lift gTarget Φ χ q hq cover hcover hcover_smooth hχ
      γ' (fun t => (hγ'V t).1) (fun t => (hγ'V t).2) z₀ hz₀ (Set.Icc (0 : ℝ) 1)
        hγ'sm hγ'geo hγ'unit
  let ρ : U → ℝ := fun y => 2 * Real.log (y.val.time - inner ℝ (ξ : E₃) y.val.space)
  have hρ : ContMDiff I₃ 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.mul (Hyperboloid.contMDiff_log_time_sub_inner ξ)).comp contMDiff_subtype_val
  have hvalue (t : ℝ) : ρ (ℓ t) = height (Φ.symm (γ' t)) :=
    ((hB (ℓ t)).trans (congrArg B (hcoverℓ t))).trans (hheight _ (hγ'V t).2)
  have hscalar : (ρ ∘ ℓ) =ᶠ[𝓝 (0 : ℝ)] (fun t => height (Φ.symm (γ t))) := by
    filter_upwards [hgerm 0 (by simp)] with t ht
    exact (hvalue t).trans (congrArg (fun y : N => height (Φ.symm y)) ht)
  have hd : deriv (ρ ∘ ℓ) 0 =
      mvfderiv I₃ ρ (ℓ 0) (mfderiv 𝓘(ℝ, ℝ) I₃ ℓ 0 1) := by
    have hr : deriv (ρ ∘ ℓ) 0 = mvfderiv 𝓘(ℝ, ℝ) (ρ ∘ ℓ) 0 (1 : ℝ) := by
      rw [mvfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (f := ρ ∘ ℓ)).symm
    rw [hr]
    exact mvfderiv_comp_apply 0 (hρ.mdifferentiableAt (by simp))
      ((hℓsm 0 (by simp)).mdifferentiableAt (by simp)) _
  have hzeroℓ : mvfderiv I₃ ρ (ℓ 0) (mfderiv 𝓘(ℝ, ℝ) I₃ ℓ 0 1) = 0 :=
    hd.symm.trans (hscalar.deriv_eq.trans hzero)
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ℓ t ∈ (fun x : U => q x) ⁻¹' K := by
    change q (ℓ t) ∈ K
    rw [hqℓ, (hgerm t ht).eq_of_nhds]
    exact hK t ht
  have hb := Hyperboloid.abs_two_mul_log_time_sub_inner_sub_le_of_isGeodesicOn
    U h ξ hp (hsmall hqU) ℓ (fun t ht => (hℓsm t ht).of_le (by simp))
      hgeolift hmem hunitlift hzeroℓ
  have hv₀ : ρ (ℓ 0) = height (Φ.symm (γ 0)) := (hvalue 0).trans
    (congrArg (fun y : N => height (Φ.symm y)) (hgerm 0 (by simp)).eq_of_nhds)
  have hv₁ : ρ (ℓ 1) = height (Φ.symm (γ 1)) := (hvalue 1).trans
    (congrArg (fun y : N => height (Φ.symm y)) (hgerm 1 (by simp)).eq_of_nhds)
  exact (congrArg₂ (fun a b : ℝ => |a - b|) hv₁.symm hv₀.symm).trans_le hb

end Obstruction

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem abs_sub_height_le_of_captured_tangent_geodesic_in_cusp
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞) (o : M)
    {R A ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hmargin : 2 * A < R)
    (hε : ε ≤ 1 / 100)
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g o R) p ε g gTarget)
    (γ : C(ℝ, N))
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) 1))
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (hcaptured : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf gTarget (Φ o) A))
    (height : M → ℝ) (hzero : deriv (fun t => height (Φ.symm (γ t))) 0 = 0) :
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
      (∀ z : H₃, Busemann.busemann ξ.val z < D.level ξ →
        height (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i z) =
          2 * Busemann.busemann ξ.val z) →
      |height (Φ.symm (γ 1)) - height (Φ.symm (γ 0))| ≤ 1 / 3 := by
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
  intro i r D ξ hcollar hheight
  have hcpt : IsCompact (riemannianClosedBallOf g o R) := hg.closedEBall_isCompact o R
  have hcapture (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    PartialDiffeomorph.inverse_mem_closedBall_of_metric_approximation
      g gTarget Φ o hA hmargin (hε.trans (by norm_num : (1 / 100 : ℝ) ≤ 3 / 4)) hcpt hΦ
        (γ t) (hcaptured ht)
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
  obtain ⟨χ, _, hχtarget, _, hχrep, hχinverse, _⟩ := hχexists
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
  have hdesc (y : M) (hy : y ∈ χ.target) : B (χ.symm y) = height y := by
    rw [hχtarget] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hχinverse z hz]
    change 2 * HorosphereProjection.quotientBusemann (Nat.le_add_left 1 2) P ξ.val hhor
      (Quotient.mk (MulAction.orbitRel P H₃) z) = _
    rw [HorosphereProjection.quotientBusemann_mk]
    exact (hheight z hz).symm
  apply height_bound_of_inverse_cover gTarget Φ χ q hq cover hcover hcover_surj hcover_smooth
    hχq (BoundaryTopology.toSphere ξ.val) B hB height hdesc (riemannianClosedBallOf g o R) p hp ?_
      γ (fun t ht => (hcapture t ht).1) ?_ (fun t ht => (hcapture t ht).2.1) hγ hgeo hunit hzero
  · dsimp only
    intro hqU
    exact (metricCkENormOn_normalized_universal_cover_pullback_lt
      g hg x₀ hsec gTarget Φ hΦ i).le.trans (ENNReal.ofReal_le_ofReal hε)
  · intro t ht
    rw [hχtarget]
    exact hcollar (hcapture t ht).2.2

end DifferentialGeometry.Geometry.Hyperbolic
