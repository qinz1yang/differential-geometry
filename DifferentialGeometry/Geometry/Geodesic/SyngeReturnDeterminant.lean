import DifferentialGeometry.Geometry.Geodesic.EndpointTangent
import DifferentialGeometry.Geometry.Geodesic.NormalReturnMap
import DifferentialGeometry.Geometry.Comparison.Variation.PositiveExponential

noncomputable section
open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem exists_minimal_twisted_geodesic_with_return_det_eq
    (g : SmoothRiemannianMetric I M) (hsec : HasPositiveSectionalCurvature g)
    (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (hfree : ∀ p, F p ≠ p) :
    ∃ (L : ℝ) (γ : ℝ → M) (hL : 0 < L) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ),
      IsGeodesic (I := I) g γ ∧ γ L = F (γ 0) ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      curveEnergy (I := I) g γ 0 L = L ∧
      (∀ c, SmoothNearInterval (I := I) c L → IsTwistedPath F L c →
        L ≤ curveEnergy (I := I) g c 0 L) ∧
      (((F.mfderivToContinuousLinearEquiv (by decide) (γ 0)).toLinearEquiv.trans
        (parallelTransportLinearEquivOnIcc (I := I) g γ (hγ.of_le (by decide)) hL).symm).toLinearMap.det =
          (-1 : ℝ) ^ (Module.finrank ℝ E - 1)) := by
  obtain ⟨L, γ, hL, hγ, hg, htw, hspeed, hE, hmin, _, hmatch⟩ :=
    exists_minimal_twisted_geodesic_with_endpoint_tangent g F hF hfree
  refine ⟨L, γ, hL, hγ, hg, htw, hspeed, hE, hmin, ?_⟩
  by_contra hdet
  let D : TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ L) :=
    (F.mfderivToContinuousLinearEquiv (by decide) (γ 0)).toLinearEquiv
  have hD (v w : TangentSpace I (γ 0)) :
      g.inner (γ L) (D v) (D w) = g.inner (γ 0) v w := by
    change g.inner (γ L) (mfderiv I I F (γ 0) v) (mfderiv I I F (γ 0) w) = _
    rw [htw, hF]
  obtain ⟨δ, W, hδ, hW, hpar, hunit, horth, hWL⟩ :=
    exists_parallel_normal_field_of_return_det g γ hγ hL (hg.isGeodesicOn _) D hD
      (hspeed 0) hmatch hdet
  obtain ⟨f, hf, hc, ht, hneg⟩ :=
    exists_negative_twisted_variation_of_parallel_normal_field g hsec F hF γ hL hδ
      (hg.isGeodesicOn _) htw W hW hpar hunit (fun t _ => hspeed t) horth hWL
  have hcc : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hstrip : (Ioo (-1 : ℝ) 1 ×ˢ Icc 0 L) ⊆ (univ ×ˢ Ioo (-δ) (L + δ)) :=
    fun _ hp => ⟨mem_univ _, hcc hp.2⟩
  have hlocal : IsLocalMin (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) 0 := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with s hs
    change curveEnergy (I := I) g (fun t => f (0, t)) 0 L ≤ _
    rw [hc, hE]
    exact hmin _ (smoothNearInterval_slice (isOpen_univ.prod isOpen_Ioo) hstrip hf hs) (ht s)
  have hsmooth := curveEnergy_contDiffOn_of_smooth_near_strip g f hL.le
    (isOpen_univ.prod isOpen_Ioo) hstrip hf
  have hcont := hsmooth.continuousOn.continuousAt
    (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  exact (not_lt_of_ge (DifferentialGeometry.Analysis.second_deriv_nonneg_of_isLocalMin hlocal hcont)) hneg

end DifferentialGeometry.Geometry.Riemannian
