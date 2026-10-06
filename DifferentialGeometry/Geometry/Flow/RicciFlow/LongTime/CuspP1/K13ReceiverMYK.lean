import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularDisk

/-!
# S-MY-K13 G2 consumer: IMS03 K13 `isEmbedding_of_no_transverse` on the `_HC2` disks

K13 (`IsMorreyDisk.isEmbedding_of_no_transverse`, ported verbatim in G1) has three conditions
besides the Morrey disk itself: `hrank` (closed-disk rank), `hseparate` (interior points are
not mapped to the loop) and `hNoTransverse` (the MY-G obligation).

* an `example := @…isEmbedding_of_no_transverse`: the verbatim type check of the K13 receiver.
* `isEmbedding_of_HC_clauses_of_no_transverse_MYK`: K13 instantiated on the confined Morrey
  disk of `exists_eventual_confined_morrey_disk_HC2` (target `U = {ρ < a}`, metric `G` the
  canonical positive-domain metric). `hrank` is fed by `closed_rank_of_HC_clauses_KP` (K16a),
  so only `hseparate` and `hNoTransverse` remain as hypotheses; no other premise is added.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- Verbatim type check of the K13 receiver (IMS03 tip `66cbb8d61`). -/
example := @DifferentialGeometry.Geometry.IsMorreyDisk.isEmbedding_of_no_transverse

/-- K13 on the clauses of `exists_eventual_confined_morrey_disk_HC2`: the Morrey disk `q` is an
embedding as soon as `hseparate` and `hNoTransverse` (MY-G) hold. The closed-disk rank `hrank`
comes from `closed_rank_of_HC_clauses_KP` applied to a smooth extension `Q` of `q`. -/
theorem isEmbedding_of_HC_clauses_of_no_transverse_MYK
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γU θ) →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
        x ≠ y → diskExtension q x = diskExtension q y →
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
        ¬ Function.Surjective
          ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
              mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
            (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
              mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y)))) →
      Topology.IsEmbedding q := by
  intro U δ hδ hU G ι γU q hsm hMor hbd hsep hnt
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨⟨Q, hQ⟩, hall⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  exact hMor.isEmbedding_of_no_transverse hsm hd3 hQ (fun z hz => ((hall Q hQ).2 z hz).1)
    hsep hnt

end GC.LongTime.CuspP1
