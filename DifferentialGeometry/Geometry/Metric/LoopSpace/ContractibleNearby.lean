import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import DifferentialGeometry.Geometry.Metric.ShortGeodesic
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal


namespace DifferentialGeometry.Topology.FreeLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M]


variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_forall_nullhomotopic_of_riemannianEDistOf_lt
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧
      ∀ {γ₀ γ₁ : freeLoop M}, γ₀.Nullhomotopic →
      (∀ z, riemannianEDistOf g (γ₁ z) (γ₀ z) < ρ) → γ₁.Nullhomotopic := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  have hg : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨ρ, W, hρ, hW, hregion, hG⟩ := exists_uniform_smooth_shortGeodesic (I := I) g hg
  refine ⟨(ρ : ℝ≥0∞), by exact_mod_cast hρ, ?_⟩
  intro γ₀ γ₁ h₀ hclose
  have hmem : ∀ q : unitInterval × loopCircle,
      ((q.1 : ℝ), (γ₁ q.2, γ₀ q.2)) ∈ W := fun q =>
    hregion (q.1 : ℝ) q.1.property (γ₁ q.2) (γ₀ q.2) (hclose q.2).le
  have hΦ : Continuous fun q : unitInterval × loopCircle =>
      ((q.1 : ℝ), (γ₁ q.2, γ₀ q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((γ₁.continuous.comp continuous_snd).prodMk (γ₀.continuous.comp continuous_snd))
  have hcont : Continuous fun q : unitInterval × loopCircle =>
      shortGeodesic g hg (γ₁ q.2) (γ₀ q.2) (q.1 : ℝ) :=
    hG.continuousOn.comp_continuous hΦ hmem
  have hhom : ContinuousMap.Homotopic γ₁ γ₀ :=
    ⟨{ toContinuousMap :=
          ⟨fun q : unitInterval × loopCircle =>
            shortGeodesic g hg (γ₁ q.2) (γ₀ q.2) (q.1 : ℝ), hcont⟩
       map_zero_left := fun z => shortGeodesic_zero g hg (γ₁ z) (γ₀ z)
       map_one_left := fun z =>
          shortGeodesic_one g hg (lt_top_iff_ne_top.mp ((hclose z).trans_le le_top)) }⟩
  obtain ⟨q, hq⟩ := h₀
  exact ⟨q, hhom.trans hq⟩

theorem exists_pos_forall_nullhomotopic_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : _root_.Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ {γ₀ γ₁ : freeLoop M}, γ₀.Nullhomotopic →
      (∀ z, ‖e (γ₁ z) - e (γ₀ z)‖ < δ) → γ₁.Nullhomotopic := by
  obtain ⟨ρ, hρ, hclose⟩ := exists_pos_forall_nullhomotopic_of_riemannianEDistOf_lt g
  obtain ⟨δ, hδ, hδ'⟩ :=
    DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt
      g e he hρ
  exact ⟨δ, hδ, fun h₀ h => hclose h₀ fun z => hδ' _ _ (h z)⟩

theorem exists_pos_forall_loopFamily_nullhomotopic_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : _root_.Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ {K : Type*} (γ Γ : K → freeLoop M) (J : Set K),
      (∀ t ∈ J, (γ t).Nullhomotopic) →
      (∀ t ∈ J, ∀ z, ‖e (Γ t z) - e (γ t z)‖ < δ) →
      ∀ t ∈ J, (Γ t).Nullhomotopic := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_nullhomotopic_of_norm_sub_lt g e he
  exact ⟨δ, hδ, fun {K} γ Γ J hγ hclose t ht => h (hγ t ht) fun z => hclose t ht z⟩

end DifferentialGeometry.Topology.FreeLoop

end

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Topology.FreeLoop

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem loopFamily_norm_sub_lt_of_iteratedFDerivWithin_zero
    {M : Type*} [TopologicalSpace M] (e : M → F)
    (γ Γ : ℝ → freeLoop M) (J : Set ℝ) (δ : ℝ)
    (h : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ 0
          (fun q : ℝ × ℝ => e (Γ q.2 (q.1 : loopCircle))) (univ ×ˢ J) p -
        iteratedFDerivWithin ℝ 0
          (fun q : ℝ × ℝ => e (γ q.2 (q.1 : loopCircle))) (univ ×ˢ J) p‖ < δ) :
    ∀ t ∈ J, ∀ z, ‖e (Γ t z) - e (γ t z)‖ < δ := by
  intro t ht z
  obtain ⟨x, hx, hxeq⟩ := AddCircle.eq_coe_Ico z
  have hbound := h (x, t) ⟨⟨hx.1, hx.2.le⟩, ht⟩
  rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero] at hbound
  simpa only [hxeq, dist_eq_norm] using hbound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

theorem exists_pos_forall_loopFamily_nullhomotopic_of_iteratedFDerivWithin_zero
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : _root_.Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ (γ Γ : ℝ → freeLoop M) (J : Set ℝ),
      (∀ t ∈ J, (γ t).Nullhomotopic) →
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ 0
            (fun q : ℝ × ℝ => e (Γ q.2 (q.1 : loopCircle))) (univ ×ˢ J) p -
          iteratedFDerivWithin ℝ 0
            (fun q : ℝ × ℝ => e (γ q.2 (q.1 : loopCircle))) (univ ×ˢ J) p‖ < δ) →
      ∀ t ∈ J, (Γ t).Nullhomotopic := by
  obtain ⟨δ, hδ, hclose⟩ := exists_pos_forall_loopFamily_nullhomotopic_of_norm_sub_lt g e he
  exact ⟨δ, hδ, fun γ Γ J hγ h =>
    hclose γ Γ J hγ (loopFamily_norm_sub_lt_of_iteratedFDerivWithin_zero e γ Γ J δ h)⟩


end DifferentialGeometry.Topology.FreeLoop
