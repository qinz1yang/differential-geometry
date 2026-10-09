import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.LocalLaplacianPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientPullback
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Differentiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleLaplacianSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff _root_.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ (p : F.M) (y : P.M), y ∈ K → ∀ s : ℝ, 0 < s →
      ∀ B : ℝ,
      (∀ t ∈ Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ z : F.M,
        normSq0S (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ B) →
      ∀ alpha : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
        alpha 0 = p → alpha (Real.sqrt s) = Phi.map k y →
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z => redLength ((U).term (phi k)).S 0 p (Phi.map k z) s) y →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ V : Set P.M, IsOpen V ∧ y ∈ V ∧
        ∃ f : P.M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V ∧
          f y = redLength ((U).term (phi k)).S 0 p (Phi.map k y) s ∧
          (∀ z ∈ V, redLength ((U).term (phi k)).S 0 p (Phi.map k z) s ≤ f z) ∧
          laplacian (LeviCivita (gSeqExt Phi R bf hsrc htgt k (1 - s)))
            (gSeqExt Phi R bf hsrc htgt k (1 - s)) f y <
              (1 / 2 : ℝ) * normGradSqFun (gSeqExt Phi R bf hsrc htgt k (1 - s))
                (fun z => redLength ((U).term (phi k)).S 0 p (Phi.map k z) s) y -
              (1 / 2 : ℝ) * ((U).term (phi k)).S.scalar (-s) (Phi.map k y) +
              ((Module.finrank ℝ E : ℝ) -
                redLength ((U).term (phi k)).S 0 p (Phi.map k y) s) / (2 * s) +
              epsilon := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  filter_upwards [eventually_gSeqExt_eq_pullback Phi R bf hsrc htgt K hK,
    eventually_laplacian_gSeqExt_comp_map Phi R bf hsrc htgt hK,
    eventually_normGradSqFun_gSeqExt_eq_on_compact Phi R bf hsrc htgt hK]
    with k hk hlap hgrad
  intro p y hy s hs B hB alpha halpha hstart hend hdiff epsilon hepsilon
  obtain ⟨W, hW, hKW, hWs, _⟩ := hk
  have hys : y ∈ Phi.source k := hWs (hKW hy)
  have hlocal := (Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ hys
  have htarget : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z => redLength ((U).term (phi k)).S 0 p z s) (Phi.map k y) :=
    hlocal.mdifferentiableAt_of_comp (by simp) hdiff
  obtain ⟨V, hV, hyV, f, hf, hcontact, hupper, _, hbound⟩ :=
    exists_curvatureNormalizedSolution_redLength_upper_support_laplacian_lt
      F.S F.isSolution hreg b (tau (phi k) + b)⁻¹ B hb
      (inv_pos.mpr (hsigma (phi k))) hbmem hg p (Phi.map k y) s hs hB
      alpha halpha hstart hend htarget hepsilon
  have hmetric : ((Y).term (phi k)).S.base.metric (1 - s) =
      ((U).term (phi k)).S.base.metric (-s) := by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    congr 1
    ring
  have hPhi : ContMDiffOn I I ∞ (Phi.map k) (Phi.source k) :=
    (Phi.partialDiffeomorph k).contMDiffOn
  let V' : Set P.M := Phi.source k ∩ Phi.map k ⁻¹' V
  have hV' : IsOpen V' :=
    hPhi.continuousOn.isOpen_inter_preimage (Phi.source_open k) hV
  have hf' : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f ∘ Phi.map k) V' :=
    hf.comp (hPhi.mono inter_subset_left) inter_subset_right
  refine ⟨V', hV', ⟨hys, hyV⟩, f ∘ Phi.map k, hf', hcontact,
    (fun z hz => hupper (Phi.map k z) hz.2), ?_⟩
  have hlap' := hlap (1 - s) f V hV hf y hy hyV
  have hgrad' := hgrad (1 - s) y hy
    (fun z => redLength ((U).term (phi k)).S 0 p z s) htarget
  rw [hmetric] at hlap' hgrad'
  erw [hlap', hgrad']
  exact hbound

end DifferentialGeometry.CheegerGromovCompactness
