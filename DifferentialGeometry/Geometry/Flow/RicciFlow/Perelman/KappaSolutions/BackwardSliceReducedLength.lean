import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Lipschitz
import Mathlib.Topology.MetricSpace.Algebra

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

theorem exists_reducedLength_limit_of_backward_slice_convergence
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) [PreconnectedSpace P.M]
    {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) :
    ∃ (psi : ℕ → ℕ) (ell : C(P.M, ℝ)), StrictMono psi ∧
      (∀ x, 0 ≤ ell x) ∧ ell P.basepoint ≤ A ∧
      (∀ x y, |Real.sqrt (ell x) - Real.sqrt (ell y)| ≤
        Real.sqrt 3 / 2 * (riemannianEDistOf P.metric x y).toReal) ∧
      ∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
        (fun i x => redLength F.S 0 p (Phi.map (psi i) x) (tau (phi (psi i)))) ell atTop K := by
  have hnonneg (i : ℕ) (x : F.M) : 0 ≤ redLength F.S 0 p x (tau i) := by
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 (htau i).le
    intro t ht y
    simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1
  let f : ∀ i : ℕ, ((backwardSliceSequence F tau htau q).obj i).M → ℝ :=
    fun i x => Real.sqrt (redLength F.S 0 p x (tau i))
  let c : ℝ≥0 := ⟨Real.sqrt 3 / 2, by positivity⟩
  have hLip (i : ℕ) (x y : F.M) : |f i x - f i y| ≤
      (c : ℝ) * (riemannianEDistOf ((backwardSliceSequence F tau htau q).obj i).metric x y).toReal :=
    abs_sqrt_redLength_sub_le_rescaled_distance F hF p x y (htau i)
  have hbdd : ∃ B : ℝ, ∀ᶠ i in atTop,
      |f (phi i) ((backwardSliceSequence F tau htau q).obj (phi i)).basepoint| ≤ B := by
    refine ⟨Real.sqrt A, Eventually.of_forall fun i => ?_⟩
    change |Real.sqrt (redLength F.S 0 p (q (phi i)) (tau (phi i)))| ≤ _
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hbase (phi i))
  obtain ⟨psi, g, hpsi, hgLip, hgconv⟩ :=
    Phi.exists_lipschitz_subseq_limit C href hcomplete f c hLip hbdd
  have hgpoint (x : P.M) : Tendsto (fun i => f (phi (psi i)) (Phi.map (psi i) x))
      atTop (𝓝 (g x)) := (hgconv {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hgnonneg (x : P.M) : 0 ≤ g x :=
    ge_of_tendsto (hgpoint x) (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
  let ell : C(P.M, ℝ) := g ^ 2
  have hsqrt (x : P.M) : Real.sqrt (ell x) = g x := by
    change Real.sqrt (g x ^ 2) = g x
    exact Real.sqrt_sq (hgnonneg x)
  have hconv (K : Set P.M) (hK : IsCompact K) : TendstoUniformlyOn
      (fun i x => redLength F.S 0 p (Phi.map (psi i) x) (tau (phi (psi i)))) ell atTop K := by
    have h := (hgconv K hK).tendstoLocallyUniformlyOn
    have hsq := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (h.mul₀ h g.continuous.continuousOn g.continuous.continuousOn)
    convert hsq using 1
    · funext i x
      change redLength F.S 0 p (Phi.map (psi i) x) (tau (phi (psi i))) =
        Real.sqrt (redLength F.S 0 p (Phi.map (psi i) x) (tau (phi (psi i)))) *
        Real.sqrt (redLength F.S 0 p (Phi.map (psi i) x) (tau (phi (psi i))))
      exact (Real.mul_self_sqrt (hnonneg _ _)).symm
    · funext x
      change g x ^ 2 = g x * g x
      exact pow_two _
  refine ⟨psi, ell, hpsi, fun x => sq_nonneg (g x), ?_, ?_, hconv⟩
  · apply le_of_tendsto ((hconv {P.basepoint} isCompact_singleton).tendsto_at
      (mem_singleton P.basepoint))
    exact Eventually.of_forall fun i => by
      simpa only [PointedRiemannianConvergenceMaps.map, Phi.basepoint_map]
        using hbase (phi (psi i))
  · intro x y
    rw [hsqrt, hsqrt]
    exact hgLip x y

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

theorem exists_backward_slice_reducedLength_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
        (C : MetricConvergenceData Phi),
        (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) ∧
        (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∃ ell : C(P.M, ℝ), (∀ x, 0 ≤ ell x) ∧ ell P.basepoint ≤ A ∧
          (∀ x y, |Real.sqrt (ell x) - Real.sqrt (ell y)| ≤
            Real.sqrt 3 / 2 * (riemannianEDistOf P.metric x y).toReal) ∧
          ∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
            (fun i x => redLength F.S 0 p (Phi.map i x) (tau (phi i))) ell atTop K := by
  obtain ⟨P, phi, hphi, Phi, C, hcanonical, href, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q
      (backwardSliceApproximateMetricCompactness_of_redLength_le F hF p tau htau q hbase)
  let _ : ConnectedSpace P.M := hconnected
  obtain ⟨psi, ell, hpsi, hnonneg, hbaseLimit, hLip, hconv⟩ :=
    exists_reducedLength_limit_of_backward_slice_convergence F hF p tau htau q hbase
      P Phi C href hcomplete
  refine ⟨P, phi ∘ psi, hphi.comp hpsi, Phi.compSubseq psi hpsi, C.compSubseq psi hpsi,
    ?_, ?_, hcomplete, hconnected, ell, hnonneg, hbaseLimit, hLip, hconv⟩
  · intro i
    change MetricSourceData.compSubseq psi hpsi i (C.domain (psi i)) = _
    rw [hcanonical]
    rfl
  · intro i
    exact href (psi i)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
