import DifferentialGeometry.Geometry.Coordinates.StereographicComplex
import Mathlib.Topology.CompactOpen

noncomputable section

open scoped Topology

namespace DifferentialGeometry

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "P" => {ξ : S2 // ξ ≠ sphereNorthPole}

private theorem nonpole_iff (Q : S2 ≃ₜ S2) (hQ : Q sphereNorthPole = sphereNorthPole)
    (ξ : S2) : ξ ≠ sphereNorthPole ↔ Q ξ ≠ sphereNorthPole := by
  constructor
  · intro hξ h
    exact hξ (Q.injective (h.trans hQ.symm))
  · intro hξ h
    exact hξ (h ▸ hQ)

theorem tendsto_stereographicComplex_conjugate_of_fixed_northPole
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (Qn : ι → S2 ≃ₜ S2) (Q : S2 ≃ₜ S2)
    (hn : ∀ n, Qn n sphereNorthPole = sphereNorthPole)
    (hlim : Filter.Tendsto (fun n => (Qn n : C(S2, S2))) l (𝓝 (Q : C(S2, S2)))) :
    ∃ hQ : Q sphereNorthPole = sphereNorthPole,
      Filter.Tendsto (fun n =>
        (stereographicComplex.symm.trans
          (((Qn n).subtype (nonpole_iff (Qn n) (hn n))).trans stereographicComplex) : C(ℂ, ℂ)))
        l (𝓝
          (stereographicComplex.symm.trans
            ((Q.subtype (nonpole_iff Q hQ)).trans stereographicComplex) : C(ℂ, ℂ))) := by
  have heval := ((continuous_eval_const sphereNorthPole).tendsto (Q : C(S2, S2))).comp hlim
  have hQ : Q sphereNorthPole = sphereNorthPole :=
    tendsto_nhds_unique heval (by simpa only [Function.comp_def, ContinuousMap.coe_apply, hn] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => sphereNorthPole) l (𝓝 sphereNorthPole)))
  refine ⟨hQ, ?_⟩
  let incl : C(P, S2) := ContinuousMap.subtypeVal {ξ : S2 | ξ ≠ sphereNorthPole}
  let Rn (n : ι) : C(P, P) :=
    (((Qn n).subtype (p := fun ξ : S2 => ξ ≠ sphereNorthPole)
      (q := fun ξ : S2 => ξ ≠ sphereNorthPole) (nonpole_iff (Qn n) (hn n))) : C(P, P))
  let R : C(P, P) := ((Q.subtype (p := fun ξ : S2 => ξ ≠ sphereNorthPole)
    (q := fun ξ : S2 => ξ ≠ sphereNorthPole) (nonpole_iff Q hQ)) : C(P, P))
  have hpre := ((ContinuousMap.continuous_precomp incl).tendsto (Q : C(S2, S2))).comp hlim
  have hR : Filter.Tendsto Rn l (𝓝 R) :=
    (ContinuousMap.isEmbedding_postcomp incl Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr hpre
  have hchartIn := ((ContinuousMap.continuous_precomp
    (stereographicComplex.symm : C(ℂ, P))).tendsto R).comp hR
  have hchartOut := ((ContinuousMap.continuous_postcomp
    (stereographicComplex : C(P, ℂ))).tendsto
      (R.comp (stereographicComplex.symm : C(ℂ, P)))).comp hchartIn
  exact hchartOut

end DifferentialGeometry
