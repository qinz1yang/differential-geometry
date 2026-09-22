import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalHamilton
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalSoliton


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.Manifold Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_exists_terminal_normalized_soliton
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S b p) (Ioi 0))
    (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (hescape : Tendsto (fun k => tau (phi (co.φ (psi k))) + b) atTop atTop)
    (ell : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term
          (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell atTop)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold (I := I)))
    (hsmooth : ∀ t : ℝ, ∀ ht : 1 < t,
      ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, ⟨t, ht.le⟩)))
    (hsol : ∀ t : ℝ, ∀ ht : 1 < t, gradientRicciSoliton (co.gInf (1 - t))
      (⟨fun x => ell (x, ⟨t, ht.le⟩), hsmooth t ht⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / t))
    (hnormal : ∀ t : ℝ, ∀ ht : 1 < t, ∀ x : P.M,
      metricScalarAt (co.gInf (1 - t)) x +
        normGradSqFun (co.gInf (1 - t)) (fun x => ell (x, ⟨t, ht.le⟩)) x =
          (1 / t) * ell (x, ⟨t, ht.le⟩)) :
    ∃ hf₁ : ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)),
    let f₁ : C^∞⟮I, P.M; ℝ⟯ := ⟨fun x => ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩), hf₁⟩
    gradientRicciSoliton (co.gInf 0) f₁ 1 ∧
      hamiltonNormalized (co.gInf 0) f₁ 1 ∧
      IsHamiltonNormalizedPotential (co.gInf 0) f₁ ∧
      normalizedShrinkerMass (co.gInf 0) f₁ = asymptoticReducedVolume F.S b p := by
  let ellExt : P.M × ℝ → ℝ :=
    fun z => ell (z.1, ⟨max 1 z.2, (le_max_left (1 : ℝ) z.2)⟩)
  have hext (x : P.M) (t : ℝ) (ht : 1 ≤ t) :
      ellExt (x, t) = ell (x, ⟨t, ht⟩) := by
    simp only [ellExt, max_eq_right ht]
  have hθ (n : ℕ) : 1 < θ n := by
    change 1 < 1 + 1 / ((n : ℝ) + 1)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hslice (n : ℕ) : (fun x => ellExt (x, θ n)) =
      (fun x => ell (x, ⟨θ n, (hθ n).le⟩)) := by
    funext x
    exact hext x (θ n) (hθ n).le
  have hsmoothExt (n : ℕ) : ContMDiff I 𝓘(ℝ) ∞ (fun x => ellExt (x, θ n)) := by
    rw [hslice n]
    exact hsmooth (θ n) (hθ n)
  have hsolExt (n : ℕ) : gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ellExt (x, θ n), hsmoothExt n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n) := by
    have heq : (⟨fun x => ellExt (x, θ n), hsmoothExt n⟩ : C^∞⟮I, P.M; ℝ⟯) =
        ⟨fun x => ell (x, ⟨θ n, (hθ n).le⟩), hsmooth (θ n) (hθ n)⟩ := by
      ext x
      exact hext x (θ n) (hθ n).le
    rw [heq]
    exact hsol (θ n) (hθ n)
  have hconvExt : ∀ x : P.M, ∀ t ∈ Icc (1 : ℝ) 2,
      Tendsto (fun k => redLength
        ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term
          (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) x) t) atTop (𝓝 (ellExt (x, t))) := by
    intro x t ht
    rw [hext x t ht.1]
    have hpoint := (tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at
      (a := (x, (⟨t, ht.1⟩ : Ici (1 : ℝ)))) (mem_univ _)
    exact hpoint
  obtain ⟨hfExt, hsolTerminal⟩ := poleEndpoint_redLength_limit_exists_terminal_gradientRicciSoliton
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p
      (Eventually.of_forall fun k => hbase (phi (co.φ k)))
      psi hpsi.tendsto_atTop ellExt hconvExt hsmoothExt hsolExt
  have hf₁ : ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)) := by
    simpa only [ellExt, max_self] using hfExt
  have hbundle : (⟨fun x => ellExt (x, 1), hfExt⟩ : C^∞⟮I, P.M; ℝ⟯) =
      ⟨fun x => ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩), hf₁⟩ := by
    ext x
    exact hext x 1 le_rfl
  rw [hbundle] at hsolTerminal
  have hterminal := poleEndpoint_redLength_limit_terminal_hamilton
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p
      (Eventually.of_forall fun k => hbase (phi (co.φ k)))
      psi hpsi.tendsto_atTop ellExt hconvExt hsmoothExt hsolExt
      (by
        intro n x
        rw [hslice n, hext x (θ n) (hθ n).le]
        exact hnormal (θ n) (hθ n) x)
  have hterminal₁ : ∀ x : P.M, metricScalarAt (co.gInf 0) x +
      normGradSqFun (co.gInf 0) (fun x => ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)) x =
        ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩) := by
    intro x
    simpa only [ellExt, max_self] using hterminal x
  refine ⟨hf₁, ?_⟩
  dsimp only
  refine ⟨hsolTerminal, ?_, ?_, ?_⟩
  · intro x
    change metricScalarAt (co.gInf 0) x +
      normGradSqFun (co.gInf 0) (fun y => ell (y, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)) x =
        1 * ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)
    simpa only [one_mul] using hterminal₁ x
  · intro x
    change metricScalarAt (co.gInf 0) x +
      (co.gInf 0).inner x
        (gradientFun (co.gInf 0) (fun y => ell (y, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)) x)
        (gradientFun (co.gInf 0) (fun y => ell (y, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)) x) =
      ell (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)
    simpa only [Connection.gradient_eq_gradFun, normGradSqFun_def] using hterminal₁ x
  · exact normalizedShrinkerMass_poleEndpoint_redLength_limit_eq_asymptoticReducedVolume
      F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p hbase hmono
      psi hpsi hescape ell hconv hcomplete

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
