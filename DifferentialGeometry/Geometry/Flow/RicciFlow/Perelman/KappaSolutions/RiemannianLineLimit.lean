import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RescaledPointedSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedOppositeRayLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CanonicalPointedMetricControl

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

section ArbitraryConvergence

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance riemannianLineLimitTopology : TopologicalSpace L.M := L.topology
local instance riemannianLineLimitCharted : ChartedSpace H L.M := L.charted
local instance riemannianLineLimitSmooth : IsManifold I ∞ L.M := L.smooth

theorem exists_riemannian_line_of_rescaled_pointed_convergence
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      (spatialRescaledPointedSeq g x lam hlam) L psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M) :
    let P := properMetricOn (I := I) L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun y v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  have hescapeNative : Tendsto (fun i => (riemannianEDist I p (x i)).toReal)
      atTop atTop := by
    simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] using hescape
  have hscaledNative : Tendsto (fun i => lam i * (riemannianEDist I p (x i)).toReal)
      atTop atTop := by
    simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] using hscaled
  have hselectedEscape : Tendsto
      (fun k => (riemannianEDist I p ((x ∘ psi) k)).toReal) atTop atTop :=
    hescapeNative.comp hpsi.tendsto_atTop
  have hselectedScaled : Tendsto
      (fun k => (lam ∘ psi) k * (riemannianEDist I p ((x ∘ psi) k)).toReal)
      atTop atTop := hscaledNative.comp hpsi.tendsto_atTop
  obtain ⟨phi, hphi, alpha, beta, hcenter, _, hsame, hopposite⟩ :=
    exists_spatialRescaledPointedSeq_approximate_opposite_rays (I := I)
      g hEnorm hsec p (x ∘ psi) (lam ∘ psi) (fun k => hlam (psi k))
      hselectedEscape hselectedScaled
  let X := spatialRescaledPointedSeq g x lam hlam
  have hfinite (n : ℕ) (y z : M) :
      riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric y z ≠ ⊤ := by
    rw [spatialRescaledPointedSeq_edist,
      riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Exponential.riemannianEDist_ne_top (I := I) y z)
  have halpha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun n => riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
        (alpha n s) (alpha n t)) atTop (𝓝 (ENNReal.ofReal |s - t|)) := by
    intro s t hs ht
    have heq : ∀ᶠ n in atTop,
        ENNReal.ofReal |s - t| = riemannianEDistOf (I := I)
          (X.obj ((psi ∘ phi) n)).metric (alpha n s) (alpha n t) := by
      filter_upwards [hsame s t hs ht] with n hn
      have hr : (riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
          (alpha n s) (alpha n t)).toReal = |s - t| := hn.1
      rw [← hr, ENNReal.ofReal_toReal (hfinite n (alpha n s) (alpha n t))]
    exact tendsto_const_nhds.congr' heq
  have hbeta : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun n => riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
        (beta n s) (beta n t)) atTop (𝓝 (ENNReal.ofReal |s - t|)) := by
    intro s t hs ht
    have heq : ∀ᶠ n in atTop,
        ENNReal.ofReal |s - t| = riemannianEDistOf (I := I)
          (X.obj ((psi ∘ phi) n)).metric (beta n s) (beta n t) := by
      filter_upwards [hsame s t hs ht] with n hn
      have hr : (riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
          (beta n s) (beta n t)).toReal = |s - t| := hn.2
      rw [← hr, ENNReal.ofReal_toReal (hfinite n (beta n s) (beta n t))]
    exact tendsto_const_nhds.congr' heq
  have hoppositeExtended : ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun n => riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
        (alpha n r) (beta n r)) atTop (𝓝 (ENNReal.ofReal (2 * r))) := by
    intro r hr
    have hreal : Tendsto (fun n =>
        (riemannianEDistOf (I := I) (X.obj ((psi ∘ phi) n)).metric
          (alpha n r) (beta n r)).toReal) atTop (𝓝 (2 * r)) := hopposite r hr
    exact (ENNReal.tendsto_ofReal hreal).congr' (Filter.Eventually.of_forall fun n =>
      ENNReal.ofReal_toReal (hfinite n (alpha n r) (beta n r)))
  exact exists_pointed_line_of_approximate_opposite_rays
    (C.compSubseq phi hphi) (reference_eq_limit_compSubseq C hreference phi hphi)
    hcomplete hconnected alpha beta (fun n => (hcenter n).1) (fun n => (hcenter n).2)
    halpha hbeta hoppositeExtended

end ArbitraryConvergence

theorem exists_riemannian_line_of_canonical_rescaled_compactness
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    (C : CanonicalMetricCompactness (I := I) (spatialRescaledPointedSeq g x lam hlam))
    (hconnected : @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology) :
    let L := C.compactness.limit
    let _ : TopologicalSpace L.M := L.topology
    let _ : ChartedSpace H L.M := L.charted
    let _ : IsManifold I ∞ L.M := L.smooth
    let P := properMetricOn (I := I) L C.compactness.limit_complete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  exact exists_riemannian_line_of_rescaled_pointed_convergence
    g hg hsec p x lam hlam hescape hscaled C.compactness.strictMono
    C.compactness.maps C.compactness.convergence.metrics C.reference_eq_limit
    C.compactness.limit_complete hconnected

theorem exists_riemannian_line_in_rescaled_metricCompactness
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    (inp : MetricCompactnessAssumptions (I := I) (spatialRescaledPointedSeq g x lam hlam)) :
    let C := inp.metricCompactness (spatialRescaledPointedSeq_complete g hg x lam hlam)
      (spatialRescaledPointedSeq_connected g x lam hlam)
    let L := C.limit
    let _ : TopologicalSpace L.M := L.topology
    let _ : ChartedSpace H L.M := L.charted
    let _ : IsManifold I ∞ L.M := L.smooth
    let P := properMetricOn (I := I) L C.limit_complete
      (metricCompactness_limit_connected inp
        (spatialRescaledPointedSeq_complete g hg x lam hlam)
        (spatialRescaledPointedSeq_connected g x lam hlam))
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  exact exists_riemannian_line_of_canonical_rescaled_compactness
    g hg hsec p x lam hlam hescape hscaled
    (inp.canonicalMetricCompactness (spatialRescaledPointedSeq_complete g hg x lam hlam)
      (spatialRescaledPointedSeq_connected g x lam hlam))
    (metricCompactness_limit_connected inp
      (spatialRescaledPointedSeq_complete g hg x lam hlam)
      (spatialRescaledPointedSeq_connected g x lam hlam))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
