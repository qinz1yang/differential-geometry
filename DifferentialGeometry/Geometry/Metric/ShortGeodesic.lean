import DifferentialGeometry.Geometry.Metric.SmoothLog
import DifferentialGeometry.Geometry.Metric.ExponentialNeighborhood
import DifferentialGeometry.Geometry.Metric.SmoothTangentScaling



noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]


theorem minimizingLog_self (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (x : M) : minimizingLog g hg x x = 0 := by
  have h := (minimizingDiagLog_eventually_eq_branch g hg x).eq_of_nhds
  rw [standardDiagonalInverseBranch_inv, diagExpInv_center] at h
  exact congrArg (fun u : TangentBundle I M => (u.2 : E)) h



def shortGeodesic (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (x y : M) : ℝ → M :=
  intrinsicGeodesic (I := I) g hg x (minimizingLog g hg x y)


theorem shortGeodesic_eq_exp (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (x y : M) (t : ℝ) :
    shortGeodesic g hg x y t =
      expMapIntrinsic (I := I) g hg x (t • minimizingLog g hg x y) := by
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  rfl

theorem shortGeodesic_zero (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (x y : M) :
    shortGeodesic g hg x y 0 = x := intrinsicGeodesic_zero (I := I) g hg x _

theorem shortGeodesic_one (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) {x y : M}
    (h : Manifold.riemannianEDist I x y ≠ ⊤) : shortGeodesic g hg x y 1 = y := by
  rw [shortGeodesic_eq_exp, one_smul]
  exact minimizingLog_exp g hg h

theorem shortGeodesic_self (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (x : M) (t : ℝ) :
    shortGeodesic g hg x x t = x := by
  rw [shortGeodesic_eq_exp, minimizingLog_self, smul_zero, expMapIntrinsic_zero]



theorem shortGeodesic_speed (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) {x y : M}
    (h : Manifold.riemannianEDist I x y ≠ ⊤) (t : ℝ) :
    Real.sqrt (g.inner (shortGeodesic g hg x y t)
      (mfderiv 𝓘(ℝ, ℝ) I (shortGeodesic g hg x y) t 1)
      (mfderiv 𝓘(ℝ, ℝ) I (shortGeodesic g hg x y) t 1)) =
      (Manifold.riemannianEDist I x y).toReal := by
  rw [shortGeodesic, intrinsicGeodesic_speedSq_eq]
  exact minimizingLog_norm g hg h



theorem exists_smooth_shortGeodesic_neighborhood (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ W : Set (ℝ × (M × M)), IsOpen W ∧ (∀ t x, (t, (x, x)) ∈ W) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
        (fun p : ℝ × (M × M) => shortGeodesic g hg p.2.1 p.2.2 p.1) W := by
  obtain ⟨U, hU, hdiag, hlog⟩ := exists_smooth_minimizingDiagLog_neighborhood g hg
  obtain ⟨V, hV, hzero, hexp⟩ := exists_smooth_exp_zeroSection_neighborhood g hg
  let A : Set (ℝ × (M × M)) := Prod.snd ⁻¹' U
  have hA : IsOpen A := hU.preimage continuous_snd
  let S : ℝ × (M × M) → TangentBundle I M := fun p =>
    TotalSpace.mk' E p.2.1 (p.1 • minimizingLog g hg p.2.1 p.2.2)
  have hS : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod I)) I.tangent ∞ S A :=
    contMDiff_tangent_scaling.comp_contMDiffOn
      (contMDiff_fst.contMDiffOn.prodMk
        (hlog.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)))
  let W := A ∩ S ⁻¹' V
  have hW : IsOpen W := hS.continuousOn.isOpen_inter_preimage hA hV
  refine ⟨W, hW, ?_, ?_⟩
  · intro t x
    refine ⟨hdiag x, ?_⟩
    change TotalSpace.mk' E x (t • minimizingLog g hg x x) ∈ V
    rw [minimizingLog_self, smul_zero]
    exact hzero x
  · apply (hexp.comp (hS.mono inter_subset_left) (fun _ hp => hp.2)).congr
    intro p _
    exact shortGeodesic_eq_exp g hg p.2.1 p.2.2 p.1



theorem exists_uniform_smooth_shortGeodesic (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ (ρ : ℝ≥0) (W : Set (ℝ × (M × M))), 0 < ρ ∧ IsOpen W ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
        Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (t, (x, y)) ∈ W) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
        (fun p : ℝ × (M × M) => shortGeodesic g hg p.2.1 p.2.2 p.1) W := by
  obtain ⟨W, hW, hdiag, hs⟩ := exists_smooth_shortGeodesic_neighborhood g hg
  have hcompact : IsCompact (range (fun x : M => (x, x))) :=
    isCompact_range (continuous_id.prodMk continuous_id)
  obtain ⟨A, U, _, hU, htime, hdiagU, hAU⟩ :=
    generalized_tube_lemma (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) hcompact hW (by
      rintro ⟨t, z⟩ ⟨_, ⟨p, hp⟩⟩
      change (p, p) = z at hp
      subst z
      exact hdiag t p)
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ x y,
      Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    exact DifferentialGeometry.Analysis.exists_uniform_diagonal_radius hU
      (fun x => hdiagU (mem_range_self x))
  exact ⟨ρ, W, hρ, hW, fun t ht x y hxy => hAU ⟨htime ht, hρU x y hxy⟩, hs⟩

end DifferentialGeometry.Geometry
