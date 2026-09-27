import DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {epsc eps C1 C2 : ℝ} {y : M}
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ F]
  [J.Boundaryless] [IsManifold J ∞ N] [SigmaCompactSpace N] in
private theorem false_of_isOpen_isCompact_subset_product_chart
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V) {C : Set M} (hCo : IsOpen C) (hCc : IsCompact C)
    (hCV : C ⊆ V) (hne : C.Nonempty) : False := by
  let ψ : O → M := fun o => (Φ o).val
  have hψ : Continuous ψ := continuous_subtype_val.comp Φ.continuous
  let P : Set O := ψ ⁻¹' C
  have hPo : IsOpen P := hCo.preimage hψ
  have hPeq : P = Φ.symm '' ((Subtype.val : V → M) ⁻¹' C) := by
    ext o
    constructor
    · intro ho
      exact ⟨Φ o, ho, Φ.symm_apply_apply o⟩
    · rintro ⟨z, hz, rfl⟩
      change (Φ (Φ.symm z)).val ∈ C
      rw [Φ.apply_symm_apply]
      exact hz
  have hVc : IsCompact ((Subtype.val : V → M) ⁻¹' C) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hCV)]
  have hPc : IsCompact P := by
    rw [hPeq]
    exact hVc.image Φ.symm.continuous
  let Q : Set (N × ℝ) := (Subtype.val : O → N × ℝ) '' P
  have hQc : IsCompact Q := hPc.image continuous_subtype_val
  have hQo : IsOpen Q := O.isOpen.isOpenMap_subtype_val P hPo
  obtain ⟨c, hc⟩ := hne
  have hQne : Q.Nonempty := by
    let o : O := Φ.symm ⟨c, hCV hc⟩
    refine ⟨o.val, o, ?_, rfl⟩
    change (Φ (Φ.symm ⟨c, hCV hc⟩)).val ∈ C
    rw [Φ.apply_symm_apply]
    exact hc
  have hQuniv : Q = univ := (IsClopen.eq_univ ⟨hQc.isClosed, hQo⟩ hQne)
  have hR : IsCompact (univ : Set ℝ) := by
    have himage := (hQuniv ▸ hQc).image (continuous_snd : Continuous (Prod.snd : N × ℝ → ℝ))
    rwa [image_univ_of_surjective (Prod.snd_surjective)] at himage
  exact noncompact_univ ℝ hR

theorem SpatialCanonicalWitness.exists_localNeck_of_product_chart
    (W : SpatialCanonicalWitness g epsc C1 C2 y) (hchart : W.capTubeHasNeckChart eps)
    (heps : eps ≤ 1 / 1000) (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V) (hcapture : W.domain.carrier ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4) (hsmall : 720 * eta < C2⁻¹ * metricScalarAt g y / 16)
    (hclose : ∀ z : V, z.val ∈ W.domain.carrier → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    ∃ neck : SpatialLocalNeck g epsc y W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  have hdomOpen (hwhole : W.domain.carrier = connectedComponent y) : False := by
    let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
    exact false_of_isOpen_isCompact_subset_product_chart O V Φ
      (hwhole ▸ isOpen_connectedComponent) W.domain.compact hcapture
      ⟨y, interior_subset W.center_inside⟩
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | positive whole data sec => exact (hdomOpen whole).elim
  | round whole data => exact (hdomOpen whole).elim
  | cap cap depth =>
    exfalso
    obtain ⟨v, bnk, hbmap⟩ := hchart cap depth halt
    have hfront : frontier cap.core.carrier = range (fun z : Sphere 2 => bnk.map (z, 0)) := by
      rw [← cap.inner_boundary]
      ext w
      constructor
      · rintro ⟨⟨z, t⟩, ⟨-, ht⟩, rfl⟩
        have ht' : t = 0 := ht
        subst ht'
        exact ⟨z, (hbmap _).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hbmap _⟩
    have hvtube : v ∈ cap.tube := by
      rw [← cap.tube_eq]
      exact ⟨(bnk.center, 0), ⟨mem_univ _, by norm_num⟩, (hbmap _).trans bnk.center_eq⟩
    have hvdom : v ∈ W.domain.carrier := by
      rw [cap.union_eq]
      exact Or.inr hvtube
    have hcoreDom : cap.core.carrier ⊆ W.domain.carrier :=
      cap.core_inside.trans interior_subset
    have hfrontDom : frontier cap.core.carrier ⊆ W.domain.carrier :=
      (cap.core.compact.isClosed.frontier_subset).trans hcoreDom
    have hs : (0 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨neg_lt_zero.mpr (inv_pos.mpr bnk.eps_pos), inv_pos.mpr bnk.eps_pos⟩
    have hsmallv : 720 * eta < metricScalarAt g v / 16 :=
      hsmall.trans_le (div_le_div_of_nonneg_right (W.scalar_bounds v hvdom).1 (by norm_num))
    have hempty := bnk.interior_eq_empty_of_frontier_in_product_chart heps hs h hdim O V Φ
      cap.core.compact (hcoreDom.trans hcapture) hfront heta hsmallv
      (fun z hz m hm => hclose z (hfrontDom hz) m hm)
    have hy := cap.center_inside
    rw [hempty] at hy
    exact hy

theorem SpatialCanonicalWitness.exists_localNeck_of_ball_product_chart
    (W : SpatialCanonicalWitness g epsc C1 C2 y) (hchart : W.capTubeHasNeckChart eps)
    (heps : eps ≤ 1 / 1000) (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : riemannianBallOf g y (2 * (C1 / Real.sqrt (metricScalarAt g y))) ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4) (hsmall : 720 * eta < C2⁻¹ * metricScalarAt g y / 16)
    (hclose : ∀ z : V, z.val ∈ riemannianBallOf g y (2 * (C1 / Real.sqrt (metricScalarAt g y))) →
      ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    ∃ neck : SpatialLocalNeck g epsc y W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  have hsub : W.domain.carrier ⊆
      riemannianBallOf g y (2 * (C1 / Real.sqrt (metricScalarAt g y))) := fun z hz =>
    (W.inside_ball hz).trans_le (ENNReal.ofReal_le_ofReal (by linarith [W.radius_upper]))
  exact W.exists_localNeck_of_product_chart hchart heps h hdim O V Φ (hsub.trans hcapture)
    heta hsmall (fun z hz m hm => hclose z (hsub hz) m hm)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
