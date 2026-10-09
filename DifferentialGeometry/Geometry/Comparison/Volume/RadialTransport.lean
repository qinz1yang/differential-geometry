import DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Shape
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian

noncomputable section

open scoped Manifold ContDiff Topology Matrix

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Bundle Filter Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem contMDiffOn_branchEnergy
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (branchEnergy g B) B.dom := by
  let gp : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
  have hgp : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun _ : M => gp) B.dom := contMDiffOn_const
  have hinner := (hgp.clm_apply B.inv_contMDiffOn).clm_apply B.inv_contMDiffOn
  have hhalf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 2 : ℝ)) B.dom :=
    contMDiffOn_const
  exact (hhalf.mul hinner).congr (fun _ _ => rfl)

theorem branchEnergy_laplacian_eq_curveMean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (b : Module.Basis ι ℝ (TangentSpace I p)) :
    laplacian (LeviCivita g) g (branchEnergy g B) (expMapIntrinsic g hEnorm p u) =
      curveMean g (intrinsicGeodesic g hEnorm p u)
        (fun i => intrinsicJacobi g hEnorm p u (b i)) 1 := by
  classical
  let γ := intrinsicGeodesic g hEnorm p u
  let V := fun i => intrinsicJacobi g hEnorm p u (b i)
  let q := γ 1
  change laplacian (LeviCivita g) g (branchEnergy g B) q = _
  have hq : q ∈ B.dom := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) by
      exact (expMapIntrinsic_def g hEnorm p u).symm.trans
        (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using B.hom_eq hu)]
    exact B.hom.map_source hu
  have hLI : LinearIndependent ℝ (fun i => V i 1) :=
    intrinsicJacobi_li B hu b b.linearIndependent
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I q) := by
    exact (Module.finrank_eq_card_basis b).symm
  have : Nonempty ι := Fintype.card_pos_iff.mp (by
    rw [hcard]
    exact NeZero.pos (Module.finrank ℝ E))
  let e : Module.Basis ι ℝ (TangentSpace I q) :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have he (i : ι) : e i = V i 1 :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard) i
  let Q : Matrix ι ι ℝ := basisInvMetric g q e
  let G := curveGram g γ V 1
  have hQ := basisInvMetric_isInverse g q e
  have hQG : Q * G = 1 := by
    ext i j
    change (∑ k, Q i k * G k j) = if i = j then 1 else 0
    simpa only [Q, G, curveGram, Matrix.of_apply, he] using (hQ i j).1
  have hInv : G⁻¹ = Q := Matrix.inv_eq_left_inv hQG
  have hSym (i j : ι) : Q i j = Q j i := basisInvMetric_symm g q e i j
  rw [lap_eq_hess_on g B.hom.open_target (contMDiffOn_branchEnergy B) hq]
  rw [metricTracePair0SAt_eq_sum_basis g e Q hQ]
  simp only [he]
  have hH (i j : ι) : hessFun g (branchEnergy g B) q (V i 1) (V j 1) =
      curveMixedGram g γ V 1 i j := branchEnergy_hess B hu
  refine Eq.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => congrArg (fun r : ℝ => Q i j * r) (hH i j)) ?_
  change (∑ i, ∑ j, Q i j * curveMixedGram g γ V 1 i j) =
    Matrix.trace (G⁻¹ * curveMixedGram g γ V 1)
  rw [hInv, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hSym]

theorem hasDerivAt_curveDensity_intrinsicJacobi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (b : Module.Basis ι ℝ (TangentSpace I p)) :
    HasDerivAt
      (curveDensity g (intrinsicGeodesic g hEnorm p u)
        (fun i => intrinsicJacobi g hEnorm p u (b i)))
      (laplacian (LeviCivita g) g (branchEnergy g B) (expMapIntrinsic g hEnorm p u) *
        curveDensity g (intrinsicGeodesic g hEnorm p u)
          (fun i => intrinsicJacobi g hEnorm p u (b i)) 1) 1 := by
  let γ := intrinsicGeodesic g hEnorm p u
  let V := fun i => intrinsicJacobi g hEnorm p u (b i)
  let q := γ 1
  have hq : q ∈ B.dom := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) by
      exact (expMapIntrinsic_def g hEnorm p u).symm.trans
        (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using B.hom_eq hu)]
    exact B.hom.map_source hu
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ B.hom.open_target hq
    (contMDiffOn_branchEnergy B)
  have hSym (i j : ι) : hessFun g (branchEnergy g B) q (V i 1) (V j 1) =
      hessFun g (branchEnergy g B) q (V j 1) (V i 1) := by
    rw [← hessFun_congr g hFf]
    exact hessFun_symm_of_boundaryless g hF q (V i 1) (V j 1)
  have hW (i j : ι) : jacobiWronskian g γ (V i) (V j) 1 = 0 := by
    apply sub_eq_zero.mpr
    calc
      g.inner q (CovariantDerivativeAlong.covDerivAlong g γ (V i) 1) (V j 1) =
          hessFun g (branchEnergy g B) q (V i 1) (V j 1) :=
        (branchEnergy_hess B hu).symm
      _ = hessFun g (branchEnergy g B) q (V j 1) (V i 1) := hSym i j
      _ = g.inner q (CovariantDerivativeAlong.covDerivAlong g γ (V j) 1) (V i 1) :=
        branchEnergy_hess B hu
      _ = g.inner q (V i 1) (CovariantDerivativeAlong.covDerivAlong g γ (V j) 1) :=
        g.symm q _ _
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 1 :=
    (intrinsicGeodesic_contMDiff g hEnorm p u).contMDiffAt
  have hV (i : ι) : DifferentiableAt ℝ
      (CovariantDerivativeAlong.chartRepAt γ (V i) 1) 1 :=
    (intrinsicJacobi_diff g hEnorm p u (b i) 1).1
  have hpos := curveGram_det_pos g γ V 1
    (intrinsicJacobi_li B hu b b.linearIndependent)
  have hd := hasDerivAt_symmDen (by simp : (1 : WithTop ℕ∞) ≤ ∞) g γ V 1 hγ hV hpos hW
  rw [branchEnergy_laplacian_eq_curveMean B hu b]
  exact hd

end DifferentialGeometry.Geometry.Riemannian.Exponential
