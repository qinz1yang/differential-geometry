import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import DifferentialGeometry.Bundle.PartialMfderiv.Regularity

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {A E F H G M N : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

theorem inner_covDerivAlong_parameter_derivative_map_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {η : A × ℝ → M} {z : A} {t : ℝ}
    (hη : ContMDiffAt (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ η (z, t))
    (ht : η (z, t) ∈ U) (v w : A) :
    h.inner (f (η (z, t)))
      (covDerivAlong h (fun r => f (η (z, r)))
        (fun r => mfderiv 𝓘(ℝ, A) J (fun q => f (η (q, r))) z v) t)
      (mfderiv 𝓘(ℝ, A) J (fun q => f (η (q, t))) z w) =
      g.inner (η (z, t))
        (covDerivAlong g (fun r => η (z, r))
          (fun r => mfderiv 𝓘(ℝ, A) I (fun q => η (q, r)) z v) t)
        (mfderiv 𝓘(ℝ, A) I (fun q => η (q, t)) z w) := by
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun r => η (z, r)) t :=
    hη.comp t (contMDiffAt_const.prodMk contMDiffAt_id)
  have hswap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A)) I ∞
      (Function.uncurry fun r q => η (q, r)) (t, z) :=
    hη.comp (t, z) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hY : DifferentiableAt ℝ (chartRepAt (I := I) (fun r => η (z, r))
      (fun r => mfderiv 𝓘(ℝ, A) I (fun q => η (q, r)) z v) t) t :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      (hswap.tangentMap_const_apply z v (by
        change (3 : WithTop ℕ∞) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))
  have hnat := covDerivAlong_map_of_local_isometry_on g h hU hf hmetric
    (fun r => η (z, r))
    (fun r => mfderiv 𝓘(ℝ, A) I (fun q => η (q, r)) z v) ht hγ hY
  have hmem : ∀ᶠ r in 𝓝 t, η (z, r) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  have hη₂ : ContMDiffAt (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I 2 η (z, t) :=
    hη.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiff : ∀ᶠ r in 𝓝 t,
      MDifferentiableAt 𝓘(ℝ, A) I (fun q => η (q, r)) z := by
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hη₂
    have hincl : ContinuousAt (fun r : ℝ => (z, r)) t :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hincl.tendsto hn] with r hr
    have hrη : ContMDiffAt (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I 2 η (z, r) := hr
    exact (hrη.comp z (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by decide)
  have hfield : ∀ᶠ r in 𝓝 t,
      (mfderiv I J f (η (z, r))
        (mfderiv 𝓘(ℝ, A) I (fun q => η (q, r)) z v) : F) =
        mfderiv 𝓘(ℝ, A) J (fun q => f (η (q, r))) z v := by
    filter_upwards [hmem, hdiff] with r hr hdr
    exact (mfderiv_comp_apply z ((hf ⟨η (z, r), hr⟩).mdifferentiableAt (by simp))
      hdr v).symm
  have hchain : mfderiv I J f (η (z, t))
      (mfderiv 𝓘(ℝ, A) I (fun q => η (q, t)) z w) =
      mfderiv 𝓘(ℝ, A) J (fun q => f (η (q, t))) z w :=
    (mfderiv_comp_apply z ((hf ⟨η (z, t), ht⟩).mdifferentiableAt (by simp))
      hdiff.self_of_nhds w).symm
  have hcov := covDerivAlong_congr_curve h
    (fun r => mfderiv I J f (η (z, r))
      (mfderiv 𝓘(ℝ, A) I (fun q => η (q, r)) z v))
    (fun r => mfderiv 𝓘(ℝ, A) J (fun q => f (η (q, r))) z v)
    (EventuallyEq.refl _ _) hfield
  rw [← hcov, ← hnat, ← hchain, ← hmetric (η (z, t)) ht]

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
