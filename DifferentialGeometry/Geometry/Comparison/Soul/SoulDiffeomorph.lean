import DifferentialGeometry.Geometry.Comparison.Soul.SoulRadialField
import DifferentialGeometry.Geometry.Comparison.Soul.NormalFlowGluing
import DifferentialGeometry.Geometry.Comparison.Soul.SoulSubmanifold
import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceEmbedding

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_soul_normal_diffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧ PathConnectedSpace S ∧
      maxSliceDim I S < Module.finrank ℝ E ∧
      (∀ (x : M), x ∈ S → ∀ v : TangentSpace I x, v ∈ sliceTangent I S x →
        ∀ t : ℝ, intrinsicGeodesic g hEnorm x v t ∈ S) ∧
      let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
      let _ := embeddedSliceChartedSpace hS
      IsSmoothEmbedding 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I ∞ (Subtype.val : S → M) ∧
      let a := normalBundlePrebundle g hEnorm hconv hB
      let _ := a.totalSpaceTopology
      let _ := a.toFiberBundle
      let _ := a.toVectorBundle
      ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) ≃ₘ⟮
            (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
              𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
        ∀ q : S, e ⟨q, 0⟩ = q.1 := by
  classical
  obtain ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, hd, hradial, hfields⟩ :=
    exists_soul_set_with_radial_escape_flow g hEnorm hsec p
  have hconnected := IsTotallyConvex.pathConnectedSpace g hEnorm hconv hSne
  have hgeodesic : ∀ (x : M), x ∈ S → ∀ v : TangentSpace I x,
      v ∈ sliceTangent I S x → ∀ t : ℝ, intrinsicGeodesic g hEnorm x v t ∈ S :=
    fun _ hx _ hv t => intrinsicGeodesic_mem_of_relBoundary_eq_empty g hEnorm
      hconv hScomp.isClosed hB hx hv t
  refine ⟨S, hconv, hB, hSne, hScomp, hconnected, hdim, hgeodesic, ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  refine ⟨embeddedSlice_inclusion_isSmoothEmbedding g hEnorm hconv hB, ?_⟩
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let NB := TotalSpace FN (normalBundleFiber g S)
  obtain ⟨ε, hε, Φ, hsource, htarget, hΦ, _, hradius⟩ :=
    exists_normal_tube g hEnorm hsec hSne hScomp hconv hB
  let r := min r₀ ε
  have hr : 0 < r := lt_min hr₀ hε
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  obtain ⟨V, hVrad, hout, ϕ, hϕsmooth, hIntegral, _, _⟩ := hfields r hr hrr₀
  let ℓ := 3 * r / 8
  let δ := r / 16
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδℓ : δ < ℓ := by dsimp only [δ, ℓ]; linarith
  have hℓδε : ℓ + δ < ε := by dsimp only [δ, ℓ]; linarith
  have hℓmem : ℓ ∈ Ioo (r / 4) (r / 2) := by
    dsimp only [ℓ]
    constructor <;> linarith
  have hdAnn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
      {q | r / 4 < Metric.infDist q S ∧ Metric.infDist q S < r / 2} :=
    hd.mono (fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩)
  have hVAnn (q : M) (hqlo : r / 4 < Metric.infDist q S)
      (hqhi : Metric.infDist q S < r / 2) :
      V q = gradientFun g (fun x => Metric.infDist x S) q :=
    hVrad.self_of_nhdsSet q ⟨hqlo.le, hqhi.le⟩
  have houtℓ (q : M) (hq : ℓ ≤ Metric.infDist q S) (u : TangentSpace I q)
      (hu : g.inner q u u = 1)
      (hend : intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S) :
      g.inner q (V q) u < 0 :=
    hout q (by dsimp only [ℓ] at hq; linarith) u hu hend
  obtain ⟨e, _, hezero⟩ := exists_normalFlow_diffeomorph g hEnorm hSne hScomp hconv hB
    hℓ hδ hδℓ hℓδε V V.contMDiff.continuous ϕ hϕsmooth hIntegral houtℓ
    Φ hsource htarget hΦ hradius (by
      intro z hzlo hzhi
      let R := Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
      have hRmem : R ∈ Ioo (r / 4) (r / 2) := by
        change ℓ - δ < R at hzlo
        change R < ℓ + δ at hzhi
        dsimp only [ℓ, δ] at hzlo hzhi
        constructor <;> linarith
      have hR : 0 < R := by linarith [hRmem.1]
      let v : normalSpace g S z.proj.1 := R⁻¹ • z.snd
      have hR2 : R ^ 2 = g.inner z.proj.1 z.snd.1 z.snd.1 :=
        Real.sq_sqrt (gInner_self_nonneg g z.proj.1 z.snd.1)
      have hv : g.inner z.proj.1 v.1 v.1 = 1 := by
        change g.inner z.proj.1 (R⁻¹ • z.snd.1) (R⁻¹ • z.snd.1) = 1
        rw [gInner_smul_self, ← hR2]
        field_simp [hR.ne']
      have hcal : ∀ t ∈ Ioo (r / 4) (r / 2),
          Metric.infDist (intrinsicGeodesic g hEnorm z.proj.1 v.1 t) S = t := by
        intro t ht
        exact hradial z.proj v hv t (by linarith [ht.1]) (by linarith [ht.2])
      have hflow := flow_eq_intrinsicGeodesic_on_annulus g hEnorm hScomp hSne
        z.proj.1 v.1 hv (by positivity : 0 ≤ r / 4) hdAnn hcal V hVAnn ϕ hIntegral hℓmem hRmem
      have hparam (t : ℝ) : intrinsicGeodesic g hEnorm z.proj.1 v.1 t =
          normalExp g hEnorm S (⟨z.proj, (t / R) • z.snd⟩ : NB) := by
        rw [← expMapIntrinsic_smul_eq_intrinsicGeodesic]
        change expMapIntrinsic g hEnorm z.proj.1 (t • (R⁻¹ • z.snd.1)) =
          expMapIntrinsic g hEnorm z.proj.1 ((t / R) • z.snd.1)
        rw [smul_smul, div_eq_mul_inv]
      have hparamR : intrinsicGeodesic g hEnorm z.proj.1 v.1 R = normalExp g hEnorm S z := by
        simpa only [div_self hR.ne', one_smul] using hparam R
      change ϕ (R - ℓ) (normalExp g hEnorm S ⟨z.proj, (ℓ / R) • z.snd⟩) =
        normalExp g hEnorm S z
      rw [← hparam ℓ, ← hparamR]
      exact hflow)
  exact ⟨e, hezero⟩

end DifferentialGeometry.Geometry.Topology
