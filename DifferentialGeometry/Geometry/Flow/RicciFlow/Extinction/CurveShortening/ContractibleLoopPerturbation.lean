import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import DifferentialGeometry.Geometry.Metric.ShortGeodesic

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ x y : M, ‖e x - e y‖ < δ → riemannianEDistOf g x y < ρ := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  have hdist : ∀ x y : M, riemannianEDistOf g x y = edist x y := fun _ _ => rfl
  have hcont : Continuous fun p : M × M => ‖e p.1 - e p.2‖ :=
    ((he.continuous.comp continuous_fst).sub (he.continuous.comp continuous_snd)).norm
  have hclosed : IsClosed {p : M × M | ρ ≤ edist p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.edist continuous_snd)
  obtain ⟨δ, hδpos, hδ⟩ := hclosed.isCompact.exists_forall_le' hcont.continuousOn
    (a := (0 : ℝ)) fun p hp => by
      rcases eq_or_lt_of_le (norm_nonneg (e p.1 - e p.2)) with h | h
      · exfalso
        have hz : e p.1 = e p.2 := sub_eq_zero.mp (norm_eq_zero.mp h.symm)
        have hxy : p.1 = p.2 := he.injective hz
        have hp' : ρ ≤ edist p.1 p.2 := hp
        rw [hxy, edist_self] at hp'
        exact absurd hp' (not_le.mpr hρ)
      · exact h
  refine ⟨δ, hδpos, fun x y hxy => ?_⟩
  have hlt : edist x y < ρ := by
    by_contra hle
    exact absurd (hδ (x, y) (not_lt.mp hle)) (not_le.mpr hxy)
  simpa only [hdist x y] using hlt

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_forall_isContractibleLoop_of_riemannianEDistOf_lt
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧
      ∀ {γ₀ γ₁ : ContinuousFreeLoop M}, IsContractibleLoop γ₀ →
      (∀ z, riemannianEDistOf g (γ₁ z) (γ₀ z) < ρ) → IsContractibleLoop γ₁ := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  have hg : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨ρ, W, hρ, hW, hregion, hG⟩ := exists_uniform_smooth_shortGeodesic (I := I) g hg
  refine ⟨(ρ : ℝ≥0∞), by exact_mod_cast hρ, ?_⟩
  intro γ₀ γ₁ h₀ hclose
  have hmem : ∀ q : unitInterval × Surgery.Topology.Circle,
      ((q.1 : ℝ), (γ₁ q.2, γ₀ q.2)) ∈ W := fun q =>
    hregion (q.1 : ℝ) q.1.property (γ₁ q.2) (γ₀ q.2) (hclose q.2).le
  have hΦ : Continuous fun q : unitInterval × Surgery.Topology.Circle =>
      ((q.1 : ℝ), (γ₁ q.2, γ₀ q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((γ₁.continuous.comp continuous_snd).prodMk (γ₀.continuous.comp continuous_snd))
  have hcont : Continuous fun q : unitInterval × Surgery.Topology.Circle =>
      shortGeodesic g hg (γ₁ q.2) (γ₀ q.2) (q.1 : ℝ) :=
    hG.continuousOn.comp_continuous hΦ hmem
  have hhom : ContinuousMap.Homotopic γ₁ γ₀ :=
    ⟨{ toContinuousMap :=
          ⟨fun q : unitInterval × Surgery.Topology.Circle =>
            shortGeodesic g hg (γ₁ q.2) (γ₀ q.2) (q.1 : ℝ), hcont⟩
       map_zero_left := fun z => shortGeodesic_zero g hg (γ₁ z) (γ₀ z)
       map_one_left := fun z =>
          shortGeodesic_one g hg (lt_top_iff_ne_top.mp ((hclose z).trans_le le_top)) }⟩
  obtain ⟨q, hq⟩ := h₀
  exact ⟨q, hhom.trans hq⟩

theorem exists_pos_forall_isContractibleLoop_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ {γ₀ γ₁ : ContinuousFreeLoop M}, IsContractibleLoop γ₀ →
      (∀ z, ‖e (γ₁ z) - e (γ₀ z)‖ < δ) → IsContractibleLoop γ₁ := by
  obtain ⟨ρ, hρ, hclose⟩ := exists_pos_forall_isContractibleLoop_of_riemannianEDistOf_lt g
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt g e he hρ
  exact ⟨δ, hδ, fun h₀ h => hclose h₀ fun z => hδ' _ _ (h z)⟩

theorem exists_pos_forall_loopFamily_isContractibleLoop_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ (γ Γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ),
      (∀ t ∈ J, IsContractibleLoop (γ t)) →
      (∀ t ∈ J, ∀ z, ‖e (Γ t z) - e (γ t z)‖ < δ) →
      ∀ t ∈ J, IsContractibleLoop (Γ t) := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_isContractibleLoop_of_norm_sub_lt g e he
  exact ⟨δ, hδ, fun γ Γ J hγ hclose t ht => h (hγ t ht) fun z => hclose t ht z⟩

omit [CompactSpace M] [T2Space M] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_ne_isContractibleLoop_of_norm_sub_lt (e : M → F) {δ : ℝ} {x y : M}
    (hne : x ≠ y) (h : ‖e y - e x‖ < δ) :
    ∃ γ₁ : ContinuousFreeLoop M, γ₁ ≠ constantLoops x ∧
      (∀ z, ‖e (γ₁ z) - e (constantLoops x z)‖ < δ) ∧ IsContractibleLoop γ₁ := by
  refine ⟨constantLoops y, ?_, ?_, isContractibleLoop_constant y⟩
  · intro hxy
    exact hne (congrArg
      (fun γ : ContinuousFreeLoop M => γ (0 : Surgery.Topology.Circle)) hxy).symm
  · intro z
    change ‖e y - e x‖ < δ
    exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
