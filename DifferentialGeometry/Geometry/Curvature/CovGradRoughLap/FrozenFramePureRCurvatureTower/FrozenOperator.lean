import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedDiffOpProportionalBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Slot0SliceFiberNormDomination
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

private def pureRFrozenDirLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 m I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x))
  map_add' v v' := by
    rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']
    rfl
  map_smul' c v := by
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]
    rfl

private noncomputable def pureRFrozenDirCLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRFrozenDirLMSummand (I := I) (M := M) g m B W x i)

noncomputable def pureRFrozenDirCLM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRFrozenDirCLMSummand (I := I) (M := M) g m B W x i

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma pureRFrozenDirCLM_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) (v : TangentSpace I x) :
    pureRFrozenDirCLM (I := I) (M := M) g m B W x v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x)) := by
  classical
  rw [pureRFrozenDirCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRFrozenDirCLMSummand, LinearMap.coe_toContinuousLinearMap', pureRFrozenDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]

noncomputable def pureRFrozenEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem pureRFrozenSlot0Sec_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x) (B i x))) := by
  classical
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))) := by
    have hWtot : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
          (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x (W.toSection x)) :=
      W.toSection.contMDiff_toFun
    exact (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 m).comp hWtot
  exact ContMDiff.clm_bundle_apply (b := fun x : M => x)
    (ϕ := fun x => (covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))
    (v := fun x => B i x) hHom (hB i)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureRFrozenDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)
    (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 m) (B i) (fun b : M => Y b)
            (fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
            x)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 m) (hB i) hY
      (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)
  refine hsum.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 0 m ℝ E)
    (E := fun z : M => TensorRSSpace 0 m I z) x) ?_
  rw [pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) (X := B i) (Y := fun b : M => Y b)
    (Z := fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
    (x := x) (hB i) hY (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)).symm ▸ rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem pureRFrozenEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRFrozenEndoFib (I := I) (M := M) g m B W x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
            (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph.contMDiff.comp
      (pureRFrozenDirCLM_homSection_contMDiff (I := I) (M := M) g m hB W)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

private noncomputable def pureRFrozenEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRFrozenEndoFib (I := I) (M := M) g m B W x
      contMDiff_toFun := pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m hB W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma pureRFrozenEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRFrozenEndoSucc (I := I) (M := M) g m B hB W).toSection x =
      pureRFrozenEndoFib (I := I) (M := M) g m B W x := rfl

noncomputable def pureRFrozenEndo0
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRFrozenEndoSucc (I := I) (M := M) g m B hB W

noncomputable def pureRFrozenDiffOp
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRFrozenEndo0 (I := I) (M := M) g B hB r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRFrozenDiffOp g B hB p r W) -
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRFrozenDiffOp g B hB p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard)
      i
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j
  have hstep : riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ ψ : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x S]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel S) (TensorRSSpace.toModel S) =
        covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)) from rfl]
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
      bse hbse_orth _ _]
    have hkey : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun j : Fin s => bse (ξ (Fin.natAdd 0 j))) := by
      intro ξ
      rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)
        (fun k => bse (ξ k))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x S (unitZeroSec (I := I) (M := M) x)]
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      rw [separableFormAt_zero (I := I) (M := M) g x
        (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd s i))]
    have hstep2 : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) *
            lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
      intro ξ
      rw [hkey ξ, ← pow_two]
      congr 2
      funext k
      rw [hbse_eq]
    refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep2 ξ)) ?_
    refine Fintype.sum_bijective
      (fun ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
        fun k : Fin s => ξ (Fin.natAdd 0 k))
      ?_ _ _ (fun ξ => rfl)
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add s) k), ?_⟩⟩
    · funext k
      have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add s) k) := by ext; simp
      rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add s) k)
    · funext k
      change φ (Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k)) = φ k
      have : Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k) = k := by ext; simp
      rw [this]
  rw [hstep]
  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]
    have hweight : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      have hcf : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0) := rfl
      rw [hcf]
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      have hL : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
          (fun k : Fin 0 => k.elim0)) mm = 1 := by
        have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
            (fun k : Fin 0 => k.elim0)) mm =
            coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
              (fun k : Fin 0 => k.elim0) := by
          apply congrArg; funext k; exact k.elim0
        rw [h1, coframeS_apply (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
          (fun k : Fin 0 => k.elim0)]
        simp
      have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) mm = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    rw [fiberNormSqComponent, hweight]
    rfl
  · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
  · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h

omit [SigmaCompactSpace M] in
private lemma exists_uniform_riemannOp_tensorCov_proportional
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 m I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
            (riemannOp (tensorCov (I := I) g 0 m) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
    mul_nonneg (mul_nonneg hvv_nonneg hww_nonneg)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x T)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (riemannOp (tensorCov (I := I) g 0 m) x v w T)
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
          hCcurv_bound x v w T
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pureRFrozenEndoFib_slot0Curry_rfns_eq
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀
          (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x (e a)) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
    riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK
  have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          slot0Curry (I := I) (M := M) g x m e K₀
            (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) ωK =
        tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a) := by
    rw [slot0Curry_apply (I := I) (M := M) g x m e K₀
      (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a ωK]
    have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
      rw [hωK,
        show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
        tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
        coframeS_apply (I := I) (M := M) g x 0 e K₀]
      simp
    rw [hscalar, one_smul]
  rw [hslot]
  rw [show (tensor0S_curry (I := I) (M := M) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a)
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a))
        (fun k => e (J k)) from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (v0 := e a) (vs := fun k => e (J k))]
  rw [pureRFrozenEndoFib]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x) ωK
    (Fin.cons (e a) (fun k => e (J k)))]
  rw [Fin.cons_zero]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundleEquiv_symm_reading_rfns_le
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M)
    (T : TensorRSSpace 0 (m + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (m + 1) S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x T := by
  classical
  have heq : riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀ T a) := by
    rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
      riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    congr 1
    unfold fiberNormSqComponent
    set ωK : Tensor0SSpace 0 I x :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) with hωK
    have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            slot0Curry (I := I) (M := M) g x m e K₀ T a) ωK =
          tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a) := by
      rw [slot0Curry_apply (I := I) (M := M) g x m e K₀ T a ωK]
      have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
        rw [hωK,
          show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
            coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
          tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
          coframeS_apply (I := I) (M := M) g x 0 e K₀]
        simp
      rw [hscalar, one_smul]
    rw [show ((((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            (covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) from rfl]
    rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x T (e a) ωK (fun k => e (J k))]
    rw [hslot]
    rw [show ((tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK)
      (v0 := e a) (vs := fun k => e (J k))]
  rw [heq]
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g m x e K₀
    hreprS hreprSucc T a

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundleEquiv_symm_reading_rfns_le_centreFrame
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x₀ : M)
    (T : TensorRSSpace 0 (m + 1) I x₀)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
        ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm T (B i x₀)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x₀ := fun j => B j x₀ with heC_def
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x₀) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x₀ (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  set K₀ : Fin 0 → Fin (Module.finrank ℝ E) := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin m → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S eC hnC horthC
  have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (m + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S eC hnC
      horthC
  have h := covGradBundleEquiv_symm_reading_rfns_le (I := I) (M := M) g m x₀ T eC K₀
    hreprS hreprSucc i
  rwa [heC_def] at h

theorem exists_proportional_pureRFrozenFrameDiffOp_orderZero
    (g : SmoothRiemannianMetric I M) :
    ∃ kappa0 : ℕ → ℝ, (∀ r, 0 ≤ kappa0 r) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x₀ : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x₀
            ((pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
              (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W).toSection x₀) ≤
          kappa0 r * riemannianFiberNormSq (I := I) (M := M) g 0 r x₀ (W.toSection x₀) := by
  classical
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def
  choose Csup hCsup_nonneg hCsup using fun m =>
    exists_uniform_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  refine ⟨fun r => match r with | 0 => 0 | (m + 1) => N ^ 3 * Csup m,
    fun r => ?_, fun r W x₀ => ?_⟩
  · cases r with
    | zero => exact le_refl 0
    | succ m => exact mul_nonneg (by positivity) (hCsup_nonneg m)
  rw [show (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W) =
      pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) r W from rfl]
  cases r with
  | zero =>
      rw [show ((pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 W).toSection x₀ :
            TensorRSSpace 0 (0 + 0) I x₀) = (0 : TensorRSSpace 0 (0 + 0) I x₀) from rfl]
      rw [riemannianFiberNormSq_zero]
      have hrhs0 : (fun r => match r with
          | 0 => (0 : ℝ) | (m + 1) => N ^ 3 * Csup m) 0 = 0 := rfl
      rw [hrhs0, zero_mul]
  | succ m =>
      set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x₀
        with hB_def
      have hBorth : ∀ i j : Fin (Module.finrank ℝ E),
          g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0 := by
        intro i j; rw [hB_def]; exact smoothOrthoFrame_orthonormal_at_center (I := I) g x₀ i j
      obtain ⟨n, e, _bse, hn, _hbse_eq, horth, _hpars, _hexp, _hreprm1⟩ :=
        tangent_orthonormalBasisS_witness (I := I) (M := M) g (m + 1) x₀
      set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
      have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S e
          (by rw [hn]) horth
      have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S e
          (by rw [hn]) horth
      rw [show (pureRFrozenEndo0 (I := I) (M := M) g B
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) (m + 1) W).toSection x₀ =
          pureRFrozenEndoFib (I := I) (M := M) g m B W x₀ from rfl]
      rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g m x₀ e K₀
        hreprS hreprSucc (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀)]
      have hslice : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (slot0Curry (I := I) (M := M) g x₀ m e K₀
                (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀) a) =
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) :=
        fun a => pureRFrozenEndoFib_slot0Curry_rfns_eq (I := I) (M := M) g m B W x₀ e K₀ hreprS a
      rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hslice a)]
      set Csm : ℝ := Csup m with hCsm_def
      have hper : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) ≤
            (n : ℝ) * ((n : ℝ) * (Csm *
              riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀))) := by
        intro a
        rw [pureRFrozenDirCLM_apply (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)]
        refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 m x₀
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _) ?_
        rw [Finset.card_univ, Fintype.card_fin]
        have hcard_le : (Module.finrank ℝ E : ℝ) = (n : ℝ) := by rw [hn]; rfl
        rw [hcard_le]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
        have hsummand : ∀ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
                (riemannOp (tensorCov (I := I) g 0 m) x₀ (B i x₀) (e a)
                  ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))) ≤
              Csm * riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀) := by
          intro i
          have hgB : g.inner x₀ (B i x₀) (B i x₀) = 1 := by
            have := hBorth i i; rwa [if_pos rfl] at this
          have hge : g.inner x₀ (e a) (e a) = 1 := by
            have := horth a a; rwa [if_pos rfl] at this
          have hbound := hCsup m x₀ (B i x₀) (e a)
            ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))
          rw [hgB, hge, mul_one, mul_one, ← hCsm_def] at hbound
          refine le_trans hbound ?_
          refine mul_le_mul_of_nonneg_left ?_ (by rw [hCsm_def]; exact hCsup_nonneg m)
          exact covGradBundleEquiv_symm_reading_rfns_le_centreFrame (I := I) (M := M) g m x₀
            (W.toSection x₀) B hBorth i
        refine le_trans (Finset.sum_le_sum (fun i _ => hsummand i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcard_le]
      refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn_eq : (n : ℝ) = N := by rw [hn, hN_def]; rfl
      have hrhs : (fun r => match r with
          | 0 => (0 : ℝ) | (m' + 1) => N ^ 3 * Csup m') (m + 1) = N ^ 3 * Csup m := rfl
      rw [hn_eq, hCsm_def, hrhs]
      exact le_of_eq (by ring)

end Curvature
end Geometry
end DifferentialGeometry

end
