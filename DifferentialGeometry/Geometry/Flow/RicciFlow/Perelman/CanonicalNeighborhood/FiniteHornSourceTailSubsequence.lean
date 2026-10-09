import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornSourceTail
import Mathlib.Topology.MetricSpace.Sequences

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature
open CheegerGromovCompactness
open Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_positive_tail_length_subsequence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ hX : FiniteControlledRadius X,
          ∃ (phi : ℕ → ℕ) (ell : ℝ)
            (gamma : ∀ i, ℝ → (X.term (phi i)).M) (a : ℕ → ℝ),
            StrictMono phi ∧ 1 / Real.sqrt 2 ≤ ell ∧ ell ≤ hX.radius ∧ 0 < ell ∧
            let L := fun i => metricDistance ((X.term (phi i)).S.base.metric 0)
              (X.term (phi i)).basepoint (hX.points (phi i))
            Tendsto L atTop (𝓝 hX.radius) ∧
            Tendsto (fun i => L i - a i) atTop (𝓝 ell) ∧
            Tendsto (fun i => (X.term (phi i)).S.scalar 0 (gamma i (L i))) atTop atTop ∧
            ∀ i, a i ∈ Icc 0 (L i) ∧
              gamma i 0 = (X.term (phi i)).basepoint ∧ gamma i (L i) = hX.points (phi i) ∧
              ContinuousOn (gamma i) (Icc 0 (L i)) ∧
              (∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
                metricDistance ((X.term (phi i)).S.base.metric 0) (gamma i s) (gamma i t) =
                  |s - t|) ∧
              (X.term (phi i)).S.scalar 0 (gamma i (a i)) = 2 ∧
              (∀ s ∈ Icc (a i) (L i), 2 ≤ (X.term (phi i)).S.scalar 0 (gamma i s)) ∧
              1 / Real.sqrt 2 < L i - a i := by
  obtain ⟨epsStar, D, hepsStar, hD, hcmp⟩ :=
    exists_source_tail_endpoint_distance_lower hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hsmall sigma hsigma Phi hPhi X hX
  let L : ℕ → ℝ := fun i => metricDistance ((X.term i).S.base.metric 0)
    (X.term i).basepoint (hX.points i)
  have hcurv : ∀ᶠ i in atTop, max 2 (2 * D) < (X.term i).S.scalar 0 (hX.points i) :=
    hX.curvature_limit.eventually_gt_atTop (max 2 (2 * D))
  have hupper : ∀ᶠ i in atTop, L i < hX.radius + 1 :=
    hX.distance_limit.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcurv.and hupper)
  have htail : ∀ i : ℕ, ∃ (gamma : ℝ → (X.term (i + N)).M) (a : ℝ),
      a ∈ Icc 0 (L (i + N)) ∧
      gamma 0 = (X.term (i + N)).basepoint ∧ gamma (L (i + N)) = hX.points (i + N) ∧
      ContinuousOn gamma (Icc 0 (L (i + N))) ∧
      (∀ s ∈ Icc 0 (L (i + N)), ∀ t ∈ Icc 0 (L (i + N)),
        metricDistance ((X.term (i + N)).S.base.metric 0) (gamma s) (gamma t) = |s - t|) ∧
      (X.term (i + N)).S.scalar 0 (gamma a) = 2 ∧
      (∀ s ∈ Icc a (L (i + N)), 2 ≤ (X.term (i + N)).S.scalar 0 (gamma s)) ∧
      1 / Real.sqrt 2 < L (i + N) - a := by
    intro i
    have hi := hN (i + N) (Nat.le_add_left N i)
    obtain ⟨gamma, a, hzero, hend, hcont, hdist, ha, heq, hhigh⟩ :=
      exists_source_high_scalar_segment X (i + N) (hX.points (i + N))
        (lt_of_le_of_lt (le_max_left _ _) hi.1)
    have hsep := hcmp eps heps hsmall sigma hsigma Phi hPhi X (i + N)
      (gamma a) (hX.points (i + N)) heq (lt_of_le_of_lt (le_max_right _ _) hi.1)
    have hL : 0 ≤ L (i + N) := ha.1.trans ha.2
    have hdist' := hdist a ha (L (i + N)) ⟨hL, le_rfl⟩
    rw [hend, abs_of_nonpos (sub_nonpos.mpr ha.2)] at hdist'
    refine ⟨gamma, a, ha, hzero, hend, hcont, hdist, heq, hhigh, ?_⟩
    linarith
  choose gamma a ha hzero hend hcont hdist heq hhigh hsep using htail
  have hmem : ∀ i, L (i + N) - a i ∈ Icc (1 / Real.sqrt 2) (hX.radius + 1) := by
    intro i
    refine ⟨(hsep i).le, ?_⟩
    have hi := (hN (i + N) (Nat.le_add_left N i)).2
    linarith [(ha i).1]
  obtain ⟨ell, hell, psi, hpsi, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  let phi : ℕ → ℕ := fun i => psi i + N
  have hphi : StrictMono phi := (strictMono_id.add_const N).comp hpsi
  have hLlim : Tendsto (fun i => L (phi i)) atTop (𝓝 hX.radius) :=
    hX.distance_limit.comp hphi.tendsto_atTop
  have htaillim : Tendsto (fun i => L (phi i) - a (psi i)) atTop (𝓝 ell) := hlim
  have hellUpper : ell ≤ hX.radius := by
    exact le_of_tendsto_of_tendsto htaillim hLlim
      (Eventually.of_forall fun i => sub_le_self _ (ha (psi i)).1)
  have hellPos : 0 < ell := lt_of_lt_of_le (by positivity) hell.1
  refine ⟨phi, ell, (fun i => gamma (psi i)), (fun i => a (psi i)),
    hphi, hell.1, hellUpper, hellPos, hLlim, htaillim, ?_, ?_⟩
  · have hscalar := hX.curvature_limit.comp hphi.tendsto_atTop
    have hEq : (fun i => (X.term (phi i)).S.scalar 0
        (gamma (psi i) (L (psi i + N)))) =
        (fun i => (X.term (phi i)).S.scalar 0 (hX.points (phi i))) := by
      funext i
      dsimp [phi]
      rw [hend (psi i)]
    have hscalarTail : Tendsto (fun i => (X.term (phi i)).S.scalar 0
        (gamma (psi i) (L (psi i + N)))) atTop atTop := by
      rw [hEq]
      simpa only [Function.comp_def] using hscalar
    simpa only [Function.comp_apply] using hscalarTail
  · intro i
    exact ⟨ha (psi i), hzero (psi i), hend (psi i), hcont (psi i), hdist (psi i),
      heq (psi i), hhigh (psi i), hsep (psi i)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
