import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointPulledUpperSupport
import DifferentialGeometry.Geometry.Operator.Laplacian.ChartLineSupport


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff _root_.Manifold _root_.Topology

universe u uE uH uκ

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

theorem eventually_exists_poleEndpoint_redLength_chart_upper_contacts
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ {κ : Type uκ} [Fintype κ], ∀ (p : F.M) (a : P.M) (z : E),
      z ∈ (extChartAt I a).target → (extChartAt I a).symm z ∈ K →
      ∀ s : ℝ, 0 < s → ∀ B : ℝ,
      (∀ t ∈ Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ y : F.M,
        normSq0S (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ B) →
      ∀ alpha : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
        alpha 0 = p → alpha (Real.sqrt s) = Phi.map k ((extChartAt I a).symm z) →
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => redLength ((U).term (phi k)).S 0 p (Phi.map k y) s)
        ((extChartAt I a).symm z) →
      ∀ (v : κ → E) (w : κ → ℝ),
      (∀ i j : Fin (Module.finrank ℝ E),
        chartDensityOnE (gSeqExt Phi R bf hsrc htgt k (1 - s)) a z *
          chartInvGramOnE (gSeqExt Phi R bf hsrc htgt k (1 - s)) a i j z =
          ∑ l, w l * (chartModelBasis E).repr (v l) i * (chartModelBasis E).repr (v l) j) →
      ∀ epsilon : ℝ, 0 < epsilon →
      let g := gSeqExt Phi R bf hsrc htgt k (1 - s)
      let f := fun y => redLength ((U).term (phi k)).S 0 p (Phi.map k y) s
      let y := (extChartAt I a).symm z
      ∃ ψ : κ → ℝ → ℝ,
        (∀ l, ContDiffAt ℝ 2 (ψ l) 0) ∧
        (∀ l, ∀ᶠ t in 𝓝 0, scalarOnE (I := I) a f (z + t • v l) ≤ ψ l t) ∧
        (∀ l, scalarOnE (I := I) a f z = ψ l 0) ∧
        (∑ l, w l * deriv (deriv (ψ l)) 0) ≤
          chartDensityOnE g a z *
            ((1 / 2 : ℝ) * normGradSqFun g f y -
              (1 / 2 : ℝ) * ((U).term (phi k)).S.scalar (-s) (Phi.map k y) +
              ((Module.finrank ℝ E : ℝ) - f y) / (2 * s)) -
            (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              iteratedFDeriv ℝ 1
                (fun u => chartDensityOnE g a u * chartInvGramOnE g a ij.1 ij.2 u) z
                (fun _ => chartModelBasis E ij.1) *
                  iteratedFDeriv ℝ 1 (scalarOnE (I := I) a f) z
                    (fun _ => chartModelBasis E ij.2)) + epsilon := by
  filter_upwards [eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt hb hg hK] with k hk
  intro κ _ p a z hz hyK s hs B hB alpha halpha hstart hend hdiff v w hC epsilon hepsilon
  dsimp only
  let g := gSeqExt Phi R bf hsrc htgt k (1 - s)
  let f := fun y => redLength ((U).term (phi k)).S 0 p (Phi.map k y) s
  let y := (extChartAt I a).symm z
  let rho := chartDensityOnE g a z
  have hrho : 0 < rho :=
    chartDensity_pos g a (extChartAt_symm_mem_trivializationAt_baseSet a hz)
  obtain ⟨V, hV, hyV, fup, hfup, hcontact, hupper, hlap⟩ :=
    hk p y hyK s hs B hB alpha halpha hstart hend hdiff (epsilon / rho)
      (div_pos hepsilon hrho)
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I a).symm z :=
    ((contMDiffOn_extChartAt_symm (n := (1 : ℕ∞ω)) a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hz)).mdifferentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (scalarOnE (I := I) a f) z :=
    (hdiff.comp z hsymm).differentiableAt
  obtain ⟨ψ, hψ, hu, hc, hsum⟩ :=
    exists_affine_line_upper_supports_of_contMDiffOn
      g a hz hV hyV hfup hdf hcontact hupper v w hC
  refine ⟨ψ, hψ, hu, hc, ?_⟩
  rw [hsum]
  have hbound := mul_lt_mul_of_pos_left hlap hrho
  have hcancel : rho * (epsilon / rho) = epsilon :=
    mul_div_cancel₀ epsilon (ne_of_gt hrho)
  dsimp only [g, f, y, rho] at hbound hcancel ⊢
  nlinarith

end DifferentialGeometry.CheegerGromovCompactness
