import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileClosedRank

/-!
# S-K16B-PORT B5 consumer: closed-disk rank of the confined Morrey disks of `_HC2`

IMS03 `closed_disk_immersion_of_completed_profile` (K16a, ported in B5) applied to the clauses of
`exists_eventual_confined_morrey_disk_HC2`: any smooth extension `Q` of the Morrey disk `q` is an
immersion on the whole closed disk (interior and boundary), also after composing with the
inclusion `U ⊆ M`. This is the rank half of the frozen `hMY` (`Function.Injective q` is not
claimed).
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

/-- K16a on the clauses of `exists_eventual_confined_morrey_disk_HC2`: the rank half of `hMY`. -/
theorem closed_rank_of_HC_clauses_KP
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
      (∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q) ∧
        ∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
          SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) (ι.comp q) (Subtype.val ∘ Q) ∧
          ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
            Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) ∧
            Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (Subtype.val ∘ Q) z) := by
  intro U δ hδ hU G ι γU q hsm hMor hbd
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨hbase, hcontact⟩ := hessian_clauses_of_hcvx_KP t a ha ρ hcvx
  have hγzero : ∀ θ : loopCircle, ρ (γU θ : (postStage F.observation t).Carrier) = 0 :=
    fun θ => boundary_zero_of_weak_trace_KP
      (fun x : U => ρ (x : (postStage F.observation t).Carrier)) hMor.trace hbd θ
  have key := closed_disk_immersion_of_completed_profile hd3 (postMetric F.observation t) a ha ρ hρ
    hbase hcontact
  refine ⟨?_, fun Q hQ => key γU q hsm hMor hγzero Q hQ⟩
  obtain ⟨Q, hQ⟩ := IsMorreyDisk.exists_smooth_extension G hd3 hsm hMor
  exact ⟨Q, hQ⟩

end GC.LongTime.CuspP1
