import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.OverlapPieces
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold Metric
open scoped ContDiff NNReal
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn
  tendstoUniformlyOn_of_cPConvergence)
namespace GC.MetricGeometry

private theorem antilipschitzWith_source_of_ball
    {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]
    (e : OpenPartialHomeomorph E X) {ρ : ℝ} (hs : e.source = ball 0 ρ) {L : ℝ≥0}
    (hanti : AntilipschitzWith L (fun u : ball (0 : E) ρ => e u)) :
    AntilipschitzWith L (fun u : e.source => e u) := by
  intro u v
  have hu : (u : E) ∈ ball (0 : E) ρ := by
    rw [← hs]
    exact u.property
  have hv : (v : E) ∈ ball (0 : E) ρ := by
    rw [← hs]
    exact v.property
  exact hanti ⟨u, hu⟩ ⟨v, hv⟩

theorem exists_limit_atlas_of_pointed_chart_limits
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X] [Countable ι]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (K : ℕ) (hK : 1 ≤ K)
    (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0))
    (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (Φ : ι → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (z : ι → ∀ i, Y i) (r : ι → ℝ)
    (hΦs : ∀ a i, (Φ a i).source = ball 0 (r a))
    (hΦ0 : ∀ a i, Φ a i 0 = z a i)
    (hrad : ∀ a i, ∀ w ∈ ball (0 : E) (r a), dist (Φ a i w) (z a i) = ‖w‖)
    (himage : ∀ a i, ∀ t ≤ r a, (Φ a i : E → Y i) '' ball 0 t = ball (z a i) t)
    (ψ : ι → OpenPartialHomeomorph E X) (q : ι → X) (ρ : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρr : ∀ a, ρ a ≤ r a)
    (hψs : ∀ a, (ψ a).source = ball 0 (ρ a))
    (hψt : ∀ a, (ψ a).target = ball (q a) (ρ a))
    (hψ0 : ∀ a, ψ a 0 = q a)
    (hcover : ∀ x, ∃ a, x ∈ (ψ a).target)
    (L : ι → ℝ≥0)
    (hanti : ∀ a, AntilipschitzWith (L a) (fun u : ball (0 : E) (ρ a) => ψ a u))
    (hdom : ∀ a, ∀ᶠ i in atTop, ∀ u ∈ ball (0 : E) (ρ a), Φ a i u ∈ closedBall (o i) (R i))
    (hlim : ∀ a, TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (Φ a i u))
      (ψ a) atTop (ball 0 (ρ a)))
    (V : ι → Set E) (hV : ∀ a, IsOpen (V a)) (hρV : ∀ a, ball (0 : E) (ρ a) ⊆ V a)
    (hVr : ∀ a, V a ⊆ ball 0 (r a))
    (A : ι → ℝ)
    (hell : ∀ a, ∀ᶠ i in atTop, ∀ u ∈ V a, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ a i) u v v ∧
        pullbackMetricCoefficients (g i) (Φ a i) u v v ≤ 2 * ‖v‖ ^ 2)
    (hjets : ∀ a, ∀ᶠ i in atTop, ∀ k : ℕ, k ≤ K → ∀ u ∈ V a,
      ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (g i) (Φ a i)) u‖ ≤ A a) :
    ∃ (σ : ℕ → ℕ) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ), StrictMono σ ∧
      (∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (V a) ∧
        (∀ u ∈ V a, ∀ v w : E, b a u v w = b a u w v) ∧
        (∀ u ∈ V a, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b a u v v ∧ b a u v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ D : Set E, IsCompact D → D ⊆ V a →
          MapCPConvergenceOn D (K - 1)
            (fun i => pullbackMetricCoefficients (g (σ i)) (Φ a (σ i))) (b a)) ∧
      (∀ a d,
        ContDiffOn ℝ K ((ψ a).trans (ψ d).symm) ((ψ a).trans (ψ d).symm).source ∧
        ∀ Q : Set E, IsCompact Q → Q ⊆ ((ψ a).trans (ψ d).symm).source →
          MapCPConvergenceOn Q K (fun i u => (Φ d (σ i)).symm (Φ a (σ i) u))
            ((ψ a).trans (ψ d).symm) ∧
          ∃ s : ℝ, 0 < s ∧ s < ρ d ∧ ∀ᶠ i in atTop,
            Q ⊆ ((Φ a (σ i)).trans (Φ d (σ i)).symm).source ∧
            MapsTo (fun u => (Φ d (σ i)).symm (Φ a (σ i) u)) Q (closedBall 0 s)) ∧
      (∀ a d u, u ∈ ((ψ a).symm.symm.trans (ψ d).symm).source →
        b a u = (b d (((ψ a).symm.symm.trans (ψ d).symm) u)).bilinearComp
          (fderiv ℝ ((ψ a).symm.symm.trans (ψ d).symm) u)
          (fderiv ℝ ((ψ a).symm.symm.trans (ψ d).symm) u)) ∧
      (∀ a d, ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ a).symm.symm.trans (ψ d).symm)
        ((ψ a).symm.symm.trans (ψ d).symm).source) ∧
      (letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
        (fun a => (ψ a).symm) hcover
       IsManifold 𝓘(ℝ, E) K X) := by
  classical
  have hψV (a : ι) : (ψ a).source ⊆ V a := by
    rw [hψs a]
    exact hρV a
  have hin (a : ι) := openPartialHomeomorph_limit_laws_of_radial_chart p o F (Φ a) (z a) (hΦs a) (hΦ0 a)
    (hrad a) (himage a) (ψ a) (hρr a) (hψs a) (hdom a) (hlim a)
  have hantiS (d : ι) : AntilipschitzWith (L d) (fun v : (ψ d).source => ψ d v) :=
    antilipschitzWith_source_of_ball (ψ d) (hψs d) (hanti d)
  have hpair (a d : ι) := exists_countable_buffered_transition_cover p o F hε (Φ a) (Φ d)
    (ψ a) (ψ d) (q d) (hρ d) (hψs d) (hψt d) (hψ0 d) (hin a).1 (hin d).2.1 (hin d).2.2.1
    ((hin a).2.2.2.1.and (hin d).2.2.2.1) (hin a).2.2.2.2 (hin d).2.2.2.2 (hantiS d)
  choose S hS using hpair
  have hcount : ∀ a d : ι, Countable (S a d) := fun a d => (hS a d).1.to_subtype
  have hκ : Countable (Σ ad : ι × ι, S ad.1 ad.2) := inferInstance
  have hpf (a d : ι) (U : Set E) (hU : U ∈ S a d) :=
    eventually_transition_regular_of_buffered_limit K g (Φ a) (Φ d) (ψ a) (ψ d) (hψV d) ((hS a d).2.1 U hU).2.2
  have hWV (j : Σ ad : ι × ι, S ad.1 ad.2) : j.2.val ⊆ V j.1.1 :=
    fun x hx => hψV j.1.1 (((hS j.1.1 j.1.2).2.1 j.2.val j.2.property).2.1 hx).1
  have hBsmooth (a : ι) :=
    eventually_contDiffOn_pullbackMetricCoefficients K g (Φ a) (hΦs a) (hV a) (hVr a)
  obtain ⟨σ, b, hσ, hb, ht⟩ := exists_coefficient_and_transition_limits_of_countable_pieces K hK g Φ ψ
    (fun j : (Σ ad : ι × ι, S ad.1 ad.2) => j.1.1) (fun j => j.1.2) V (fun j => j.2.val) hV
    (fun j => ((hS j.1.1 j.1.2).2.1 j.2.val j.2.property).1) hWV A hBsmooth hell hjets
    (fun j => (hpf j.1.1 j.1.2 j.2.val j.2.property).1)
    (fun j => (hpf j.1.1 j.1.2 j.2.val j.2.property).2.1)
    (fun j => (hpf j.1.1 j.1.2 j.2.val j.2.property).2.2.1)
    (fun j => (hpf j.1.1 j.1.2 j.2.val j.2.property).2.2.2)
  have hpiece (a d : ι) (U : Set E) (hU : U ∈ S a d) :
      ContDiffOn ℝ K ((ψ a).trans (ψ d).symm) U ∧
        ∀ D : Set E, IsCompact D → D ⊆ U →
          MapCPConvergenceOn D K (fun i u => (Φ d (σ i)).symm (Φ a (σ i) u))
            ((ψ a).trans (ψ d).symm) :=
    ht ⟨(a, d), ⟨U, hU⟩⟩
  have hfullC (a d : ι) :
      ContDiffOn ℝ K ((ψ a).trans (ψ d).symm) ((ψ a).trans (ψ d).symm).source :=
    contDiffOn_of_isOpen_sUnion_eq (fun U hU => ((hS a d).2.1 U hU).1) (hS a d).2.2
      (fun U hU => (hpiece a d U hU).1)
  have hfullMap (a d : ι) (Q : Set E) (hQ : IsCompact Q)
      (hQO : Q ⊆ ((ψ a).trans (ψ d).symm).source) :
      MapCPConvergenceOn Q K (fun i u => (Φ d (σ i)).symm (Φ a (σ i) u))
        ((ψ a).trans (ψ d).symm) :=
    mapCPConvergenceOn_of_isOpen_sUnion_eq (fun U hU => ((hS a d).2.1 U hU).1) (hS a d).2.2
      (fun U hU => (hpiece a d U hU).2) hQ hQO
  have hfullBuf (a d : ι) (Q : Set E) (hQ : IsCompact Q)
      (hQO : Q ⊆ ((ψ a).trans (ψ d).symm).source) :
      ∃ s : ℝ, 0 < s ∧ s < ρ d ∧ ∀ᶠ i in atTop,
        Q ⊆ ((Φ a (σ i)).trans (Φ d (σ i)).symm).source ∧
        MapsTo (fun u => (Φ d (σ i)).symm (Φ a (σ i) u)) Q (closedBall 0 s) :=
    exists_transition_buffer_of_subseq p o F hε (Φ a) (Φ d) (ψ a) (ψ d) (q d) (hρ d)
      (hψs d) (hψt d) (hψ0 d) (hin a).1 (hin d).2.1 (hin d).2.2.1
      ((hin a).2.2.2.1.and (hin d).2.2.2.1) (hin a).2.2.2.2 (hin d).2.2.2.2 (hantiS d)
      hσ Q hQ hQO
  have hcompat (a d : ι) (u : E) (hu : u ∈ ((ψ a).trans (ψ d).symm).source) :
      b a u = (b d (((ψ a).trans (ψ d).symm) u)).bilinearComp
        (fderiv ℝ ((ψ a).trans (ψ d).symm) u) (fderiv ℝ ((ψ a).trans (ψ d).symm) u) := by
    have hzV : ((ψ a).trans (ψ d).symm) u ∈ V d := hψV d ((ψ d).map_target hu.2)
    have hOV : ((ψ a).trans (ψ d).symm).source ⊆ V a := fun x hx => hψV a hx.1
    exact bilinearComp_identity_of_isOpen_sUnion_eq (fun U hU => ((hS a d).2.1 U hU).1)
      (hS a d).2.2 (hV d)
      (B := fun i => pullbackMetricCoefficients (g (σ i)) (Φ a (σ i))) (b := b a)
      (C := fun i => pullbackMetricCoefficients (g (σ i)) (Φ d (σ i))) (c := b d)
      (Θ := fun i u => (Φ d (σ i)).symm (Φ a (σ i) u)) (T := (ψ a).trans (ψ d).symm)
      (fun D hD hDO => ((hb a).2.2.2 D hD (hDO.trans hOV)).mono_order (Nat.zero_le _))
      (fun D hD hDV => ((hb d).2.2.2 D hD hDV).mono_order (Nat.zero_le _))
      (fun U hU D hD hDU => ((hpiece a d U hU).2 D hD hDU).mono_order hK)
      (fun U hU => (hσ.tendsto_atTop.eventually (hpf a d U hU).1).mono fun _ hi =>
        hi.of_le (by exact_mod_cast Nat.le_add_left 1 K))
      (fun U hU => (hpiece a d U hU).1.of_le (by exact_mod_cast hK))
      (hb d).1.continuousOn
      (fun U hU => hσ.tendsto_atTop.eventually (hpf a d U hU).2.2.1)
      hu hzV
  have hfullC' (a d : ι) : ContDiffOn ℝ K ((ψ a).symm.symm.trans (ψ d).symm)
      ((ψ a).symm.symm.trans (ψ d).symm).source := by
    rw [OpenPartialHomeomorph.symm_symm]
    exact hfullC a d
  have htr (a d : ι) : ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ a).symm.symm.trans (ψ d).symm)
      ((ψ a).symm.symm.trans (ψ d).symm).source := by
    rw [Nat.sub_add_cancel hK]
    exact hfullC' a d
  refine ⟨σ, b, hσ, hb, fun a d => ⟨hfullC a d, fun Q hQ hQO =>
    ⟨hfullMap a d Q hQ hQO, hfullBuf a d Q hQ hQO⟩⟩, fun a d u hu => ?_, htr, ?_⟩
  · rw [OpenPartialHomeomorph.symm_symm] at hu ⊢
    exact hcompat a d u hu
  · exact DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
      (fun a => (ψ a).symm) hcover hfullC'

end GC.MetricGeometry
