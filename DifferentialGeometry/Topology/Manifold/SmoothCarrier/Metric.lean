import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Path.Composition
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Topology.Manifold

theorem enorm_tangent_eq_sqrt_inner {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : M → Type _)) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)) := by
  let _ : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

theorem enorm_mfderiv_eq_of_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N] {n m : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) m E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → N)
    (hG' : ∀ (x : M) (v w : E), G'.inner x v w =
      G.inner (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x w)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : N → Type _) := ⟨G.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G'.toRiemannianMetric⟩
    ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v‖ₑ = ‖v‖ₑ := by
  intro x v
  rw [enorm_tangent_eq_sqrt_inner G (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v),
    enorm_tangent_eq_sqrt_inner G' x v, hG' x v v]

theorem enorm_mfderiv_inverse_eq_of_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]
    {n m : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) m E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → N) (g : N → M)
    (hG' : ∀ (x : M) (v w : E), G'.inner x v w =
      G.inner (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x w))
    (hfg : ∀ y, f (g y) = y)
    (hcomp : ∀ (y : N) (w : TangentSpace 𝓘(ℝ, E) y),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (g y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y w) = w) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : N → Type _) := ⟨G.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G'.toRiemannianMetric⟩
    ∀ (y : N) (w : TangentSpace 𝓘(ℝ, E) y),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y w‖ₑ = ‖w‖ₑ := by
  intro y w
  rw [enorm_tangent_eq_sqrt_inner G' (g y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y w),
    enorm_tangent_eq_sqrt_inner G y w,
    hG' (g y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y w), hcomp y w,
    hfg y]

theorem pathELength_comp_eq_of_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace E N] [∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x)]
    [∀ y : N, ENorm (TangentSpace 𝓘(ℝ, E) y)] (f : M → N)
    (hf : ∀ x, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x)
    (hiso : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v‖ₑ = ‖v‖ₑ)
    (γ : ℝ → M) (a b : ℝ)
    (hγ : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    pathELength 𝓘(ℝ, E) (f ∘ γ) a b = pathELength 𝓘(ℝ, E) γ a b :=
  Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f hγ (ae_of_all _ fun t => hf (γ t))
    (ae_of_all _ fun t => hiso (γ t) _)

theorem riemannianEDist_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace E N] [∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x)]
    [∀ y : N, ENorm (TangentSpace 𝓘(ℝ, E) y)]
    [∀ y : N, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y)] (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f)
    (hiso : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v‖ₑ = ‖v‖ₑ) (x y : M) :
    riemannianEDist 𝓘(ℝ, E) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ, E) x y := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have heq : pathELength 𝓘(ℝ, E) (f ∘ γ) 0 1 = pathELength 𝓘(ℝ, E) γ 0 1 :=
    pathELength_comp_eq_of_isometry f (fun z => (hf z).mdifferentiableAt one_ne_zero) hiso γ 0 1
      hdiff
  have hle : riemannianEDist 𝓘(ℝ, E) (f x) (f y) ≤ pathELength 𝓘(ℝ, E) (f ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hf.comp_contMDiffOn hγ) (congrArg f hγ0) (congrArg f hγ1)
      zero_le_one
  rw [heq] at hle
  exact hle.trans_lt hlen

theorem SmoothCarrier.mfderiv_ofBase_comp_mfderiv_toBase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Type*} [MetricSpace X] {ι ι' : Type*}
    (A : SmoothCompatibleAtlas E X ι) (φ : ι' → OpenPartialHomeomorph X E)
    (hcover : ∀ x, ∃ i, x ∈ (φ i).source) {r : ℕ} (hr : 1 ≤ r) (hA : A.IsCompatible φ r) :
    letI := chartedSpaceOfOpenCover φ hcover
    ∀ x : SmoothCarrier A,
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) (SmoothCarrier.toBase A x)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  intro x
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x :=
    ((SmoothCarrier.contMDiff_toBase A φ hcover hA) x).mdifferentiableAt hr0
  have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A)
      (SmoothCarrier.toBase A x) :=
    ((SmoothCarrier.contMDiff_ofBase A φ hcover hA) (SmoothCarrier.toBase A x)).mdifferentiableAt
      hr0
  rw [← mfderiv_comp x h2 h1, SmoothCarrier.ofBase_comp_toBase]
  exact mfderiv_id

theorem SmoothCarrier.mfderiv_toBase_comp_mfderiv_ofBase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Type*} [MetricSpace X] {ι ι' : Type*}
    (A : SmoothCompatibleAtlas E X ι) (φ : ι' → OpenPartialHomeomorph X E)
    (hcover : ∀ x, ∃ i, x ∈ (φ i).source) {r : ℕ} (hr : 1 ≤ r) (hA : A.IsCompatible φ r) :
    letI := chartedSpaceOfOpenCover φ hcover
    ∀ y : X,
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A y)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) y) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  intro y
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y :=
    ((SmoothCarrier.contMDiff_ofBase A φ hcover hA) y).mdifferentiableAt hr0
  have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A)
      (SmoothCarrier.ofBase A y) :=
    ((SmoothCarrier.contMDiff_toBase A φ hcover hA) (SmoothCarrier.ofBase A y)).mdifferentiableAt
      hr0
  rw [← mfderiv_comp y h2 h1, SmoothCarrier.toBase_comp_ofBase]
  exact mfderiv_id

theorem SmoothCarrier.exists_pullback_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] {ι ι' : Type*} (A : SmoothCompatibleAtlas E X ι)
    (φ : ι' → OpenPartialHomeomorph X E) (hcover : ∀ x, ∃ i, x ∈ (φ i).source)
    {K : ℕ} (hK : 1 ≤ K) (hA : A.IsCompatible φ K)
    (hM : letI := chartedSpaceOfOpenCover φ hcover; IsManifold 𝓘(ℝ, E) K X) :
    letI := chartedSpaceOfOpenCover φ hcover
    letI := hM
    letI : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
    ∀ G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _),
      ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
          (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _),
        (∀ (x : SmoothCarrier A) (v w : E),
          G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
        (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
         letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
           ⟨G'.toRiemannianMetric⟩
         (∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
            ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ) ∧
         (∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
            ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ) ∧
         (∀ (γ : ℝ → SmoothCarrier A) (a b : ℝ),
            (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
            pathELength 𝓘(ℝ, E) (SmoothCarrier.toBase A ∘ γ) a b =
              pathELength 𝓘(ℝ, E) γ a b) ∧
         (∀ (γ : ℝ → X) (a b : ℝ),
            (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
            pathELength 𝓘(ℝ, E) (SmoothCarrier.ofBase A ∘ γ) a b =
              pathELength 𝓘(ℝ, E) γ a b) ∧
         (∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
            riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
         (∀ x y : SmoothCarrier A,
            dist x y = dist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
         (IsRiemannianManifold 𝓘(ℝ, E) X → IsRiemannianManifold 𝓘(ℝ, E) (SmoothCarrier A))) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  have : IsManifold 𝓘(ℝ, E) K X := hM
  have : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
  intro G
  obtain ⟨f, hf, -⟩ := SmoothCarrier.exists_diffeomorph_toBase A φ hcover hA
  obtain ⟨G', hG'⟩ :=
    DifferentialGeometry.Geometry.exists_finite_order_pullback_metric_of_diffeomorph
      (K - 1) K (K - 1) le_rfl (by omega) G f
  have hG'' : ∀ (x : SmoothCarrier A) (v w : E),
      G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w) := by
    intro x v w
    have h := hG' x v w
    rw [hf] at h
    exact h
  refine ⟨G', hG'', ?_⟩
  let _ : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
  let _ : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
    ⟨G'.toRiemannianMetric⟩
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hK1 : (1 : ℕ∞ω) ≤ (K : ℕ∞ω) := by exact_mod_cast hK
  have hC1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (SmoothCarrier.toBase A) :=
    (SmoothCarrier.contMDiff_toBase A φ hcover hA).of_le hK1
  have hC1' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (SmoothCarrier.ofBase A) :=
    (SmoothCarrier.contMDiff_ofBase A φ hcover hA).of_le hK1
  have hd1 : ∀ x : SmoothCarrier A,
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x :=
    fun x => ((SmoothCarrier.contMDiff_toBase A φ hcover hA) x).mdifferentiableAt hK0
  have hd2 : ∀ y : X, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y :=
    fun y => ((SmoothCarrier.contMDiff_ofBase A φ hcover hA) y).mdifferentiableAt hK0
  have hcomp : ∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w) = w :=
    fun y w => DFunLike.congr_fun
      (SmoothCarrier.mfderiv_toBase_comp_mfderiv_ofBase A φ hcover hK hA y) w
  have hiso : ∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ :=
    enorm_mfderiv_eq_of_pullback G G' (SmoothCarrier.toBase A) hG''
  have hiso' : ∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ :=
    enorm_mfderiv_inverse_eq_of_pullback G G' (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A)
      hG'' (SmoothCarrier.toBase_ofBase A) hcomp
  have hedist : ∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
      riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y) := by
    intro x y
    have hle := riemannianEDist_comp_le (SmoothCarrier.ofBase A) hC1' hiso'
      (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)
    rw [SmoothCarrier.ofBase_toBase, SmoothCarrier.ofBase_toBase] at hle
    exact le_antisymm hle (riemannianEDist_comp_le (SmoothCarrier.toBase A) hC1 hiso x y)
  refine ⟨hiso, hiso', fun γ a b hγ => pathELength_comp_eq_of_isometry _ hd1 hiso γ a b hγ,
    fun γ a b hγ => pathELength_comp_eq_of_isometry _ hd2 hiso' γ a b hγ, hedist,
    fun x y => (SmoothCarrier.dist_toBase A x y).symm, fun hX => ⟨fun x y => ?_⟩⟩
  exact (SmoothCarrier.edist_toBase A x y).symm.trans
    ((IsRiemannianManifold.out (I := 𝓘(ℝ, E)) (self := hX) (SmoothCarrier.toBase A x)
      (SmoothCarrier.toBase A y)).trans (hedist x y).symm)

end DifferentialGeometry.Topology.Manifold
