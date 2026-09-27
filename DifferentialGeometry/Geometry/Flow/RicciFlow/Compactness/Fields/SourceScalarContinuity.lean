import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.sigmaCompact PointedFlowData.t2
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2

theorem PointedCGHMaps.eventually_continuousOn_scalar
    (Φ : PointedCGHMaps X P subseq) (η : ℕ → ℕ) (hη : Tendsto η atTop atTop)
    {J : Set ℝ} (htime : J ⊆ X.D.carrier) {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in atTop,
      ContinuousOn
        (fun z : ℝ × P.M =>
          (X.term (subseq (η k))).S.scalar z.1 (Φ.map (η k) z.2))
        (J ×ˢ K) := by
  obtain ⟨N, hN⟩ := Φ.source_subset hK
  filter_upwards [hη.eventually (eventually_ge_atTop N)] with k hk
  have hmap : ContinuousOn (fun x : P.M => Φ.map (η k) x) K := by
    simpa only [PointedCGHMaps.map] using
      (Φ.partialDiffeomorph (η k)).contMDiffOn_toFun.continuousOn.mono (hN (η k) hk)
  have hpair : ContinuousOn
      (fun z : ℝ × P.M => (z.1, Φ.map (η k) z.2)) (J ×ˢ K) :=
    continuousOn_fst.prodMk (hmap.comp continuousOn_snd (fun _ hz => hz.2))
  have hmaps : MapsTo
      (fun z : ℝ × P.M => (z.1, Φ.map (η k) z.2)) (J ×ˢ K)
      (X.D.carrier ×ˢ (univ : Set (X.term (subseq (η k))).M)) :=
    fun _ hz => ⟨htime hz.1, mem_univ _⟩
  simpa only [Function.comp_def] using
    (X.term (subseq (η k))).isSolution.scalarCont.comp hpair hmaps

end DifferentialGeometry.CheegerGromovCompactness
