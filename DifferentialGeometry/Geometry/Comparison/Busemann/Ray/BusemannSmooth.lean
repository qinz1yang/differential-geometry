import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannAffinity
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FixedBasePartialDiffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem busemann_expMapIntrinsic_affine
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) (v : TangentSpace I p) :
    let b := busemann (fun t : ℝ≥0 => γ t)
    b (expMapIntrinsic (I := I) g hEnorm p v) = b p + mvfderiv (I := I) b p v := by
  let b := busemann (fun t : ℝ≥0 => γ t)
  let eta := intrinsicGeodesic (I := I) g hEnorm p v
  let K := b (eta 1) - b (eta 0)
  have heta : ContMDiff 𝓘(ℝ, ℝ) I ∞ eta := intrinsicGeodesic_contMDiff (I := I) g hEnorm p v
  have hgeo : IsGeodesic (I := I) g eta := intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hline (t : ℝ) : b (eta t) = b (eta 0) + t * K :=
    busemann_comp_geodesic_affine (I := I) g hEnorm hRic hγ heta hgeo t
  have hfun : (fun t => b (eta t)) = (fun t => b (eta 0) + t * K) := funext hline
  have hk : deriv (fun t => b (eta t)) 0 = K := by
    rw [hfun]
    simpa only [one_mul] using!
      (((hasDerivAt_id (0 : ℝ)).mul_const K).const_add (b (eta 0))).deriv
  have hd := deriv_comp_mfderiv_along I b eta 0
    ((opposite_busemann_mdifferentiable (I := I) g hEnorm hRic hγ).1 (eta 0))
    (heta.contMDiffAt.mdifferentiableAt (by simp))
  change deriv (fun t => b (eta t)) 0 =
    mvfderiv (I := I) b (eta 0) (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) at hd
  have hv : (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  have hzero : eta 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  rw [hv, hk] at hd
  erw [hzero] at hd
  have h := hline 1
  rw [one_mul, hzero, hd] at h
  exact h

theorem busemann_contMDiff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (busemann (fun t : ℝ≥0 => γ t)) := by
  let b := busemann (fun t : ℝ≥0 => γ t)
  intro p
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
  let Φ := B.fixedBasePartialDiffeomorph
  have hp : p ∈ Φ.target := B.fixedBasePartialDiffeomorph_center_mem_target
  have hinv : ContMDiffAt I 𝓘(ℝ, E) ∞ (Φ.symm : M → E) p :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)
  let L : E →L[ℝ] ℝ := mvfderiv (I := I) b p
  have hlin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun v : E => b p + L v) :=
    contMDiff_const.add L.contMDiff
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => b p + L (Φ.symm y)) p :=
    hlin.contMDiffAt.comp p hinv
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Φ.open_target.mem_nhds hp] with y hy
  have h := busemann_expMapIntrinsic_affine (I := I) g hEnorm hRic hγ p (Φ.symm y)
  have hexp : expMapIntrinsic (I := I) g hEnorm p (Φ.symm y) = y := Φ.right_inv hy
  dsimp only at h
  rw [hexp] at h
  exact h

theorem busemann_hessian_eq_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) :
    hessFun (I := I) g (busemann (fun t : ℝ≥0 => γ t)) p = 0 := by
  let b := busemann (fun t : ℝ≥0 => γ t)
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b := busemann_contMDiff (I := I) g hEnorm hRic hγ
  have hdiag (v : TangentSpace I p) : hessFun (I := I) g b p v v = 0 := by
    let eta := intrinsicGeodesic (I := I) g hEnorm p v
    let K := b (eta 1) - b (eta 0)
    have heta : ContMDiff 𝓘(ℝ, ℝ) I ∞ eta := intrinsicGeodesic_contMDiff (I := I) g hEnorm p v
    have hgeo : IsGeodesic (I := I) g eta := intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
    have hfun : b ∘ eta = fun t => b (eta 0) + t * K := by
      funext t
      exact busemann_comp_geodesic_affine (I := I) g hEnorm hRic hγ heta hgeo t
    have hder : deriv (b ∘ eta) = fun _ => K := by
      funext t
      rw [hfun]
      simpa only [one_mul] using!
        (((hasDerivAt_id t).mul_const K).const_add (b (eta 0))).deriv
    have hd := deriv2_comp_geo_on (I := I) g isOpen_univ hb.contMDiffOn heta hgeo
      (t := 0) (mem_univ (eta 0))
    change deriv (deriv (b ∘ eta)) 0 = hessFun (I := I) g b (eta 0)
      (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E)
      (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) at hd
    have hv : (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) = (v : E) :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
    have hzero : eta 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
    rw [hder, deriv_const, hv] at hd
    erw [hzero] at hd
    exact hd.symm
  ext v w
  change hessFun (I := I) g b p v w = 0
  have h := hdiag (v + w)
  simp only [map_add, LinearMap.add_apply] at h
  rw [hdiag v, hdiag w, hessFun_symm_of_boundaryless (I := I) g hb p w v] at h
  linarith

theorem opposite_busemann_smooth_hessian_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (busemann (fun t : ℝ≥0 => γ t)) ∧
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) ∧
    ∀ p, hessFun (I := I) g (busemann (fun t : ℝ≥0 => γ t)) p = 0 ∧
      hessFun (I := I) g (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) p = 0 := by
  have hrev : Isometry (fun t : ℝ => γ (-t)) := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hγ.dist_eq, dist_neg_neg]
  exact ⟨busemann_contMDiff (I := I) g hEnorm hRic hγ,
    busemann_contMDiff (I := I) g hEnorm hRic hrev,
    fun p => ⟨busemann_hessian_eq_zero (I := I) g hEnorm hRic hγ p,
      busemann_hessian_eq_zero (I := I) g hEnorm hRic hrev p⟩⟩

end DifferentialGeometry.Geometry.Topology

end
