import DifferentialGeometry.Topology.ThreeManifold.UncappingInteriorCover

noncomputable section

open Set Metric Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private local instance smoothCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
private local instance smoothCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_uncapping_homeomorph_localDiffeomorph :
    ∃ H : C.UncappingQuotient ≃ₜ M.Carrier,
      (∀ x : T.core, H (Quot.mk C.innerCapRelation
        (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x))) = x.val) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H) ∧
      ∀ (a : T.Index) (z : S2),
        IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞
          (H ∘ C.uncappingSeam a)
          (z,(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  obtain ⟨B,hsmall,hboundary,hhalf,hcollar,Ψ,ρ,hρ,hzero,hone,hpos,hgerm,_,hlo,hhi,H,hcore,hann⟩ :=
    C.exists_normalized_uncapping_homeomorph v
  obtain ⟨ε₀,ε₁,hε₀,hε₁,hloρ,hhiρ⟩ := hgerm
  have hmono : StrictMono (ρ : ℝ → ℝ) := strictMono_of_deriv_pos hpos
  have hρgerm : (ρ : ℝ → ℝ) =ᶠ[𝓝 (1 / 4 : ℝ)] (fun r => r - 1 / 4) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 4 : ℝ) hε₀] with r hr
    exact hloρ r (by
      have h : |r - 1 / 4| < ε₀ := by simpa only [mem_ball,Real.dist_eq] using hr
      exact h.le)
  refine ⟨H,hcore,?_,?_⟩
  · intro y
    let _ := C.coreCharts
    let _ := C.coreSmooth
    rcases C.uncappingInterior_cover B hsmall hboundary v y with ⟨x,hx,hy⟩ | ⟨b,z,hy⟩ | ⟨b,q,hq,hy⟩
    · have heq : y = ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ := Subtype.ext hy
      rw [heq]
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_core H hcore x hx
    · obtain ⟨e,⟨he,heq⟩,V,hV,hSV,hcap,_,_⟩ := hcollar b
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_outer H hcore
        (fun b => (B b).toHomeomorph) hsmall hboundary Ψ hlo hhi ρ hρ hann ε₁ hε₁ hhiρ b v e he heq V hV hSV
        (fun x hx => (hcap x hx).2) z y hy
    · have heq : y = ⟨C.capAnnulusInteriorChart b (B b) v q,
          C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b (B b) (hsmall b) v q hq⟩ :=
        Subtype.ext hy
      rw [heq]
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_annulus H B hsmall hboundary Ψ ρ hρ
        hmono hzero hone hann b v q hq
  · intro a z
    exact C.isLocalDiffeomorphAt_homeomorph_uncappingSeam H (fun b => (B b).toHomeomorph)
      hsmall hboundary hhalf Ψ ρ hρ hmono hzero hone hann hρgerm a z

end DifferentialGeometry.Topology.SphericalCapping
