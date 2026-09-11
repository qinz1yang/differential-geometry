import DifferentialGeometry.Geometry.Comparison.Variation.EndpointParallel

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma ContMDiffAt.add_tangentBundleAlong {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ} {n : WithTop ℕ∞}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun s =>
      (TotalSpace.mk' E (γ s) (V s) : TangentBundle I M)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun s =>
      (TotalSpace.mk' E (γ s) (W s) : TangentBundle I M)) t) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun s =>
      (TotalSpace.mk' E (γ s) (V s + W s) : TangentBundle I M)) t := by
  rw [Bundle.contMDiffAt_totalSpace] at hV hW ⊢
  refine ⟨hV.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (γ t)
  apply (hV.2.add hW.2).congr_of_eventuallyEq
  have he : ∀ᶠ s in 𝓝 t, γ s ∈ e.baseSet :=
    hV.1.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  filter_upwards [he] with s hs
  exact (e.linear ℝ hs).map_add (V s) (W s)

variable [FiniteDimensional ℝ E] [I.Boundaryless]


lemma parallel_field_eq_section (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    (V : ∀ t, TangentSpace I (γ t)) (v : TangentSpace I (γ 0))
    (hV : V 0 = v)
    (hdiff : ∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hpar : ∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) :
    ∀ t ∈ Icc (0 : ℝ) L, V t = parallelTransportSectionOnIcc (I := I) g γ hγ hL v t := by
  apply parallel_transport_unique_of_eq_at_point g γ le_rfl hγ V
    (parallelTransportSectionOnIcc (I := I) g γ hγ hL v) hdiff
    (fun _ ht => parallelTransportSectionOnIcc_differentiableAt g γ hγ hL v ht) hpar
    (fun _ ht => parallelTransportSectionOnIcc_covDerivAlong g γ hγ hL v ht)
    (t₀ := 0) ⟨le_rfl, hL.le⟩
  simpa only [parallelTransportSectionOnIcc_initial] using hV

theorem exists_smooth_endpoint_interpolation (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (D : TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ L))
    (v : TangentSpace I (γ 0)) :
    let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by exact_mod_cast le_top)
    let P := parallelTransportLinearEquivOnIcc (I := I) g γ hγ2 hL
    ∃ (δ : ℝ) (W : ∀ t, TangentSpace I (γ t)), 0 < δ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ (fun t =>
        (TotalSpace.mk' E (γ t) (W t) : TangentBundle I M)) (Ioo (-δ) (L + δ)) ∧
      W 0 = v ∧ W L = D v ∧
      ∀ t ∈ Icc (0 : ℝ) L, W t = parallelTransportSectionOnIcc (I := I) g γ hγ2 hL
        ((1 - t / L) • v + (t / L) • P.symm (D v)) t := by
  dsimp only
  let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by exact_mod_cast le_top)
  let P := parallelTransportLinearEquivOnIcc (I := I) g γ hγ2 hL
  let w := P.symm (D v)
  obtain ⟨δv, hδv, V, hV0, hVdiff, hVpar, hVs⟩ := parallelTransport_section_contMDiffOn_Ioo g γ hγ hL v
  obtain ⟨δw, hδw, Q, hQ0, hQdiff, hQpar, hQs⟩ := parallelTransport_section_contMDiffOn_Ioo g γ hγ hL w
  let δ := min δv δw
  have hδ : 0 < δ := lt_min hδv hδw
  have hVsub : Ioo (-δ) (L + δ) ⊆ Ioo (-δv) (L + δv) := by
    intro t ht
    have hh := min_le_left δv δw
    constructor <;> linarith [ht.1, ht.2]
  have hQsub : Ioo (-δ) (L + δ) ⊆ Ioo (-δw) (L + δw) := by
    intro t ht
    have hh := min_le_right δv δw
    constructor <;> linarith [ht.1, ht.2]
  have hcc : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hVe := parallel_field_eq_section g γ hγ2 hL V v hV0
    (fun t ht => hVdiff t (hVsub (hcc ht))) (fun t ht => hVpar t (hVsub (hcc ht)))
  have hQe := parallel_field_eq_section g γ hγ2 hL Q w hQ0
    (fun t ht => hQdiff t (hQsub (hcc ht))) (fun t ht => hQpar t (hQsub (hcc ht)))
  let W : ∀ t, TangentSpace I (γ t) := fun t => (1 - t / L) • V t + (t / L) • Q t
  refine ⟨δ, W, hδ, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hsV := (hVs t (hVsub ht)).contMDiffAt (isOpen_Ioo.mem_nhds (hVsub ht))
    have hsQ := (hQs t (hQsub ht)).contMDiffAt (isOpen_Ioo.mem_nhds (hQsub ht))
    have ha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t / L) t :=
      (contDiff_const.sub (contDiff_id.div_const L)).contMDiff.contMDiffAt
    have hb : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t / L) t :=
      (contDiff_id.div_const L).contMDiff.contMDiffAt
    exact (ContMDiffAt.add_tangentBundleAlong
      (ContMDiffAt.smul_tangentBundleAlong ha hsV)
      (ContMDiffAt.smul_tangentBundleAlong hb hsQ)).contMDiffWithinAt
  · simp [W, hV0]
  · have hQL := hQe L ⟨hL.le, le_rfl⟩
    change Q L = P w at hQL
    simp [W, ne_of_gt hL, hQL, w]
  · intro t ht
    dsimp only [W]
    rw [parallelTransportSectionOnIcc_add g γ hγ2 hL _ _ ht,
      parallelTransportSectionOnIcc_smul g γ hγ2 hL _ _ ht,
      parallelTransportSectionOnIcc_smul g γ hγ2 hL _ _ ht,
      hVe t ht, hQe t ht]

end DifferentialGeometry.Geometry.Riemannian.Variation
