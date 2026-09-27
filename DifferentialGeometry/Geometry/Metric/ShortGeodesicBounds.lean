import DifferentialGeometry.Geometry.Metric.ShortGeodesic
import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction








noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle 𝓘(ℝ, E) M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold 𝓘(ℝ, E) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]



def ambientShortGeodesic (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g) (r : V → M)
    (p : ℝ × (V × V)) : M := shortGeodesic g hg (r p.2.1) (r p.2.2) p.1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem ambientShortGeodesic_embed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g) {r : V → M} {e : M → V}
    (hleft : ∀ x, r (e x) = x) (t : ℝ) (x y : M) :
    ambientShortGeodesic g hg r (t, (e x, e y)) = shortGeodesic g hg x y t := by
  simp only [ambientShortGeodesic, hleft]




theorem exists_ambientShortGeodesic_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g)
    {e : M → V} (he : Continuous e) {r : V → M} {U : Set V} (hU : IsOpen U)
    (heU : range e ⊆ U) (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ r U)
    (hleft : ∀ x, r (e x) = x) :
    ∃ (ρ C : ℝ≥0) (O : Set (ℝ × (V × V))), 0 < ρ ∧ IsOpen O ∧
      ContMDiffOn 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, E) ∞ (ambientShortGeodesic g hg r) O ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
        Manifold.riemannianEDist 𝓘(ℝ, E) x y ≤ (ρ : ℝ≥0∞) →
          (t, (e x, e y)) ∈ O ∧ ∀ v : ℝ × (V × V),
            Real.sqrt (g.inner (ambientShortGeodesic g hg r (t, (e x, e y)))
              (mfderiv 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, E) (ambientShortGeodesic g hg r)
                (t, (e x, e y)) v)
              (mfderiv 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, E) (ambientShortGeodesic g hg r)
                (t, (e x, e y)) v)) ≤ C * ‖v‖ := by
  obtain ⟨ρ, W, hρ, hW, hregion, hG⟩ := exists_uniform_smooth_shortGeodesic g hg
  let R : ℝ × (V × V) → ℝ × (M × M) := fun p => (p.1, (r p.2.1, r p.2.2))
  let A : Set (ℝ × (V × V)) := univ ×ˢ (U ×ˢ U)
  have hA : IsOpen A := isOpen_univ.prod (hU.prod hU)
  have hx : ContMDiff 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, V) ∞
      (fun p : ℝ × (V × V) => p.2.1) :=
    (contDiff_fst.comp contDiff_snd).contMDiff
  have hy : ContMDiff 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, V) ∞
      (fun p : ℝ × (V × V) => p.2.2) :=
    (contDiff_snd.comp contDiff_snd).contMDiff
  have ht : ContMDiff 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (V × V) => p.1) := contDiff_fst.contMDiff
  have hR : ContMDiffOn 𝓘(ℝ, ℝ × (V × V))
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) ∞ R A := by
    exact ht.contMDiffOn.prodMk
      ((hr.comp hx.contMDiffOn (fun _ (hp : _ ∈ A) => hp.2.1)).prodMk
        (hr.comp hy.contMDiffOn (fun _ (hp : _ ∈ A) => hp.2.2)))
  let O := A ∩ R ⁻¹' W
  have hO : IsOpen O := hR.continuousOn.isOpen_inter_preimage hA hW
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × (V × V)) 𝓘(ℝ, E) ∞
      (ambientShortGeodesic g hg r) O :=
    hG.comp (hR.mono inter_subset_left) (fun _ hp => hp.2)
  let K : Set (ℝ × (M × M)) := Icc 0 1 ×ˢ
    {p | Manifold.riemannianEDist 𝓘(ℝ, E) p.1 p.2 ≤ (ρ : ℝ≥0∞)}
  have hK : IsCompact K := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
    exact isCompact_Icc.prod (isClosed_le (continuous_fst.edist continuous_snd)
      continuous_const).isCompact
  let eK : ℝ × (M × M) → ℝ × (V × V) := fun p => (p.1, (e p.2.1, e p.2.2))
  have heK : Continuous eK := continuous_fst.prodMk
    ((he.comp (continuous_fst.comp continuous_snd)).prodMk
      (he.comp (continuous_snd.comp continuous_snd)))
  have hKO : eK '' K ⊆ O := by
    rintro _ ⟨⟨t, x, y⟩, hp, rfl⟩
    refine ⟨⟨mem_univ _, heU (mem_range_self x), heU (mem_range_self y)⟩, ?_⟩
    change (t, (r (e x), r (e y))) ∈ W
    rw [hleft, hleft]
    exact hregion t hp.1 x y hp.2
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hO
    (hF.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) (hK.image heK) hKO
  refine ⟨ρ, C, O, hρ, hO, hF, fun t ht x y hxy => ?_⟩
  have hp : (t, (e x, e y)) ∈ eK '' K :=
    mem_image_of_mem eK (show (t, (x, y)) ∈ K from ⟨ht, hxy⟩)
  exact ⟨hKO hp, hC _ hp⟩

end DifferentialGeometry.Geometry
