import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessRestriction
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.mono_of_regular_strict_of_lt
    (hS : IsSolutionOn S) {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hde : delta < eps) (he : eps < 1)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0, parabolicTime t (S.scalar t x) s ∈ D.regular) :
    ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf
          ((W.monoOfRegular hS hde.le he hreg).model.S.base.metric 0)
          (W.monoOfRegular hS hde.le he hreg).model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a ((W.monoOfRegular hS hde.le he hreg).comparison.jet b s)
          ((W.monoOfRegular hS hde.le he hreg).model.S.base.metric s)
          ((W.monoOfRegular hS hde.le he hreg).model.S.base.metric s) y < eps := by
  intro a b hab s hs y hy
  have ht : s ∈ Icc (-modelDepth delta) 0 :=
    ⟨(neg_le_neg (modelDepth_anti W.eps_pos hde.le)).trans hs.1, hs.2⟩
  have hy' := riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
    (modelRadius_anti W.eps_pos hde.le) hy
  exact (W.comparison.close a b (hab.trans (modelOrder_anti W.eps_pos hde.le)) s ht y
    hy').trans_lt hde

theorem WindowedModelWitness.exists_strict_of_lt
    (hS : IsSolutionOn S) {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hde : delta < eps) (he : eps < 1)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0, parabolicTime t (S.scalar t x) s ∈ D.regular) :
    ∃ W' : WindowedModelWitness eps kappa S x t,
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps :=
  ⟨W.monoOfRegular hS hde.le he hreg, W.mono_of_regular_strict_of_lt hS hde he hreg⟩

omit [T2Space M] in
theorem WindowedModelWitness.window_subset_regular_of_lt
    {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hde : delta < eps)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0, parabolicTime t (S.scalar t x) s ∈ D.regular)
    (ht : t ∈ D.regular) :
    Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular := by
  intro s hs
  rcases hs.2.eq_or_lt with heq | hlt
  · exact heq ▸ ht
  have hR := W.scalar_pos
  have heps : 0 < eps := W.eps_pos.trans hde
  set R := S.scalar t x
  have hinv : eps⁻¹ < delta⁻¹ := (inv_lt_inv₀ heps W.eps_pos).mpr hde
  have h1 : -(eps * R)⁻¹ ≤ s - t := by linarith [hs.1]
  have h2 : (eps * R)⁻¹ * R = eps⁻¹ := by field_simp
  have h3 : -eps⁻¹ ≤ (s - t) * R := by
    have := mul_le_mul_of_nonneg_right h1 hR.le
    linarith
  have h4 : (s - t) * R < 0 := mul_neg_of_neg_of_pos (by linarith) hR
  have hmem := hreg ((s - t) * R) ⟨by simp only [modelDepth]; linarith, h4⟩
  have hpt : parabolicTime t R ((s - t) * R) = s := by
    simp only [parabolicTime]
    field_simp
    ring
  rwa [hpt] at hmem

theorem orientedWitness_mono_of_regular
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1) {x : M} {t : ℝ}
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0, parabolicTime t (S.scalar t x) s ∈ D.regular)
    (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W, oN, hO⟩ := hw
  exact ⟨W.monoOfRegular hS hde he hreg, oN, hO⟩

theorem orientedWitness_exists_strict_of_lt
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta < eps) (he : eps < 1) {x : M} {t : ℝ}
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0, parabolicTime t (S.scalar t x) s ∈ D.regular)
    (hw : OrientedWitness S o delta kappa x t) :
    ∃ W' : WindowedModelWitness eps kappa S x t,
      (∃ oN : TangentOrientationSection W'.model.M,
        ∀ y ∈ W'.embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
            PreservesTangentOrientationAt oN o W'.embedding y hf) ∧
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  obtain ⟨W, oN, hO⟩ := hw
  exact ⟨W.monoOfRegular hS hde.le he hreg, ⟨oN, hO⟩,
    W.mono_of_regular_strict_of_lt hS hde he hreg⟩

section RestrictOpen

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem trans_subtypeVal_symm_source {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] (U : TopologicalSpace.Opens M) (x : U)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) :
    (Φ.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) U ⟨x⟩).symm).source = Φ.source ∩ Φ ⁻¹' (U : Set M) := by
  rw [PartialDiffeomorph.trans_source]
  change Φ.source ∩ Φ ⁻¹' (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target = _
  rw [U.openPartialHomeomorphSubtypeCoe_target]

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem trans_subtypeVal_symm_coe {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] (U : TopologicalSpace.Opens M) (x : U)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) {y : N} (hy : Φ y ∈ (U : Set M)) :
    ((Φ.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) U ⟨x⟩).symm) y : M) = Φ y := by
  rw [PartialDiffeomorph.trans_apply]
  apply (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩).right_inv'
  change Φ y ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
  rwa [U.openPartialHomeomorphSubtypeCoe_target]

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem mfderiv_eq_of_coe_eqOn {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] {U : TopologicalSpace.Opens M}
    (F : PartialDiffeomorph I3 I3 N U ∞) (Φ : N → M)
    (hF : ∀ z ∈ F.source, (F z : M) = Φ z) {y : N} (hy : y ∈ F.source) :
    mfderiv I3 I3 F y = mfderiv I3 I3 Φ y := by
  have hlocal : (fun z => (F z : M)) =ᶠ[𝓝 y] Φ :=
    Filter.eventuallyEq_of_mem (F.open_source.mem_nhds hy) hF
  exact (DifferentialGeometry.mfderiv_subtypeVal_comp (I := I3) (J := I3) F y).symm.trans
    hlocal.mfderiv_eq

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem trans_subtypeVal_symm_mfderiv {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] (U : TopologicalSpace.Opens M) (x : U)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) {y : N}
    (hy : y ∈ (Φ.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) U ⟨x⟩).symm).source) :
    mfderiv I3 I3 (Φ.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) U ⟨x⟩).symm) y = mfderiv I3 I3 Φ y := by
  refine mfderiv_eq_of_coe_eqOn _ Φ (fun z hz => ?_) hy
  have hz' : z ∈ Φ.source ∩ Φ ⁻¹' (U : Set M) := trans_subtypeVal_symm_source U x Φ ▸ hz
  exact trans_subtypeVal_symm_coe U x Φ hz'.2

variable {U : TopologicalSpace.Opens M} {x : U}

variable [SigmaCompactSpace U] {eps kappa t : ℝ}

def WindowedModelWitness.toRestrictOpen
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M)) :
    WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t := by
  let F := W.embedding.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩).symm
  have hsc : (solutionOnRestrictOpen S U).scalar t x = S.scalar t x.val :=
    scalar_restrictOpen S U t x
  have hQ : 0 < (solutionOnRestrictOpen S U).scalar t x := by rw [hsc]; exact W.scalar_pos
  have hmetric (v : ℝ) :
      rescaledMetric (solutionOnRestrictOpen S U) t ((solutionOnRestrictOpen S U).scalar t x)
        hQ v = (rescaledMetric S t (S.scalar t x.val) W.scalar_pos v).restrictOpen U := by
    simp only [hsc]
    apply SmoothRiemannianMetric.ext_inner
    intro y V Z
    change (S.scalar t x.val) *
      ((S.base.metric (parabolicTime t (S.scalar t x.val) v)).restrictOpen U).inner y V Z = _
    rfl
  have hbuf : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ F.source := by
    intro y hy
    rw [trans_subtypeVal_symm_source U x]
    exact ⟨W.buffered_ball hy, hU ⟨y, hy, rfl⟩⟩
  have hball : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hbase : W.embedding W.model.basepoint ∈ (U : Set M) := by rw [W.base_map]; exact x.2
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hQ
      window_mem := by simpa only [hsc] using W.window_mem
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := F
      buffered_ball := hbuf
      base_map := Subtype.ext ((trans_subtypeVal_symm_coe U x W.embedding hbase).trans W.base_map)
      comparison :=
        { pullback := W.comparison.pullback
          pullback_eq := ?_
          jet := W.comparison.jet
          jet_zero := W.comparison.jet_zero
          jet_succ := W.comparison.jet_succ
          equivalence := W.comparison.equivalence
          close := W.comparison.close }
      source_capture := ?_ }
  · intro v y hy V
    rw [W.comparison.pullback_eq v y hy V, hmetric, SmoothRiemannianMetric.restrictOpen_inner,
      trans_subtypeVal_symm_mfderiv U x W.embedding (hbuf (hball hy)),
      trans_subtypeVal_symm_coe U x W.embedding (hU ⟨y, hball hy, rfl⟩)]
    rfl
  · intro z hz
    rw [hmetric] at hz
    have hz' : z.val ∈ riemannianBallOf (rescaledMetric S t (S.scalar t x.val) W.scalar_pos 0)
        x.val (modelRadius eps - 1) :=
      (DifferentialGeometry.riemannianEDistOf_le_restrictOpen _ U x z).trans_lt hz
    obtain ⟨w, hw, hweq⟩ := W.source_capture hz'
    have hwU : W.embedding w ∈ (U : Set M) := hweq ▸ z.2
    refine ⟨w, ?_, Subtype.ext ((trans_subtypeVal_symm_coe U x W.embedding hwU).trans hweq)⟩
    rw [trans_subtypeVal_symm_source U x]
    exact ⟨hw, hwU⟩

@[simp] theorem WindowedModelWitness.toRestrictOpen_model
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M)) :
    (W.toRestrictOpen hU).model = W.model := rfl

theorem WindowedModelWitness.toRestrictOpen_embedding
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M)) :
    (W.toRestrictOpen hU).embedding = W.embedding.trans
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩).symm := rfl

theorem WindowedModelWitness.toRestrictOpen_source
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M)) :
    (W.toRestrictOpen hU).embedding.source = W.embedding.source ∩ W.embedding ⁻¹' (U : Set M) :=
  trans_subtypeVal_symm_source U x W.embedding

theorem WindowedModelWitness.toRestrictOpen_embedding_coe
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M)) {y : W.model.M} (hy : W.embedding y ∈ (U : Set M)) :
    ((W.toRestrictOpen hU).embedding y : M) = W.embedding y :=
  trans_subtypeVal_symm_coe U x W.embedding hy

theorem WindowedModelWitness.toRestrictOpen_strict
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M))
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps) :
    ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf ((W.toRestrictOpen hU).model.S.base.metric 0)
          (W.toRestrictOpen hU).model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a ((W.toRestrictOpen hU).comparison.jet b s)
          ((W.toRestrictOpen hU).model.S.base.metric s)
          ((W.toRestrictOpen hU).model.S.base.metric s) y < eps :=
  hstrict

theorem WindowedModelWitness.toRestrictOpen_preservesTangentOrientationAt
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M))
    (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source,
      ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
        PreservesTangentOrientationAt oN o W.embedding y hf) :
    ∀ y ∈ (W.toRestrictOpen hU).embedding.source,
      ∃ hf : Function.Bijective (mfderiv I3 I3 (W.toRestrictOpen hU).embedding y),
        PreservesTangentOrientationAt oN (o.restrictOpen U) (W.toRestrictOpen hU).embedding y
          hf := by
  intro y hy
  change W.model.M at y
  have hy' : y ∈ W.embedding.source ∩ W.embedding ⁻¹' (U : Set M) := by
    rwa [W.toRestrictOpen_source hU] at hy
  obtain ⟨hf, hpres⟩ := hO y hy'.1
  have hder : mfderiv I3 I3 (W.toRestrictOpen hU).embedding y =
      mfderiv I3 I3 W.embedding y :=
    trans_subtypeVal_symm_mfderiv U x W.embedding hy
  refine ⟨hder.symm ▸ hf, ?_⟩
  have hc := W.toRestrictOpen_embedding_coe hU hy'.2
  unfold PreservesTangentOrientationAt at hpres ⊢
  rw [TangentOrientationSection.restrictOpen_orientation]
  convert hpres using 2
  rw [hc]
  apply Iff.of_eq
  congr 3
  ext v
  exact DFunLike.congr_fun hder v

theorem WindowedModelWitness.orientedWitness_toRestrictOpen
    (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M))
    (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source,
      ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
        PreservesTangentOrientationAt oN o W.embedding y hf) :
    OrientedWitness (solutionOnRestrictOpen S U) (o.restrictOpen U) eps kappa x t :=
  ⟨W.toRestrictOpen hU, oN, W.toRestrictOpen_preservesTangentOrientationAt hU o oN hO⟩

end RestrictOpen

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
